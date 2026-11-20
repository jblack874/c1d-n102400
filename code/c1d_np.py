"""NP-beta1 (Nudge-Polish, beta 1) worker for C_1d.

Loop until the deadline:
  1. read the shared global best (elitist: every worker nudges whatever is best right now, so wins compound);
  2. nudge: multiply one random contiguous block (BLOCK cells, or all cells with --global) by (1 + sigma*N(0,1)),
     sigma log-uniform in [SMIN, SMAX];
  3. polish: s5_search.py (p-norm annealed L-BFGS) from p0 drawn from P0S, for a time drawn from SECS;
  4. accept if the true (max-norm) float score drops; write the shared best atomically.
Every sample is logged with its parameters so the coordinator can see which settings produce wins.

Usage: python3 c1d_np.py <tag> <shared_dir> <seconds> <seed> [--global] [--smin 1e-8] [--smax 1e-6]
                          [--p0 4096] [--secs 25] [--bmin 16] [--bmax 4096]      (--p0/--secs accept comma lists)
The shared_dir must hold best.npz (key x) to start from.
"""
import sys, os, time, subprocess, re, argparse, fcntl, numpy as np
ap = argparse.ArgumentParser()
ap.add_argument("tag"); ap.add_argument("shared"); ap.add_argument("seconds", type=float); ap.add_argument("seed", type=int)
ap.add_argument("--global", dest="glob", action="store_true")
ap.add_argument("--smin", type=float, default=1e-8); ap.add_argument("--smax", type=float, default=1e-6)
ap.add_argument("--p0", default="4096"); ap.add_argument("--secs", default="25")
ap.add_argument("--n", type=int, default=0, help="stop after exactly this many samples (0 = time only)")
ap.add_argument("--bmin", type=int, default=16); ap.add_argument("--bmax", type=int, default=4096)
a = ap.parse_args()
P0S = [float(t) for t in a.p0.split(",")]; SECS = [float(t) for t in a.secs.split(",")]
rng = np.random.default_rng(a.seed); t0 = time.time()
S5 = os.path.join(os.path.dirname(os.path.abspath(__file__)), "aaron", "s5_search.py")
BAR = 1.4513064006879361
best_f = os.path.join(a.shared, "best.npz"); lock_f = os.path.join(a.shared, "best.lock")
work = os.path.join(a.shared, a.tag); os.makedirs(work, exist_ok=True)
log = open(os.path.join(a.shared, f"{a.tag}.log"), "a")

def score(v):
    n = len(v); m = 1 << int(np.ceil(np.log2(2 * n))); F = np.fft.rfft(v, m); c = np.fft.irfft(F * F, m)[:2 * n - 1]
    return 2 * n * np.abs(c).max() / v.sum() ** 2

def read_best():
    with open(lock_f, "a") as L:
        fcntl.flock(L, fcntl.LOCK_SH); x = np.load(best_f)["x"].astype(float); fcntl.flock(L, fcntl.LOCK_UN)
    return x, score(x)

def offer(x, s):
    with open(lock_f, "a") as L:
        fcntl.flock(L, fcntl.LOCK_EX)
        cur = score(np.load(best_f)["x"].astype(float))
        won = s < cur
        if won:
            tmp = os.path.join(work, "best_tmp.npz"); np.savez(tmp, x=x); os.replace(tmp, best_f)
            np.savez(os.path.join(a.shared, f"win_{a.tag}_{time.time()-t0:.0f}s_{s:.16f}.npz"), x=x)
        fcntl.flock(L, fcntl.LOCK_UN)
    return won

x0, s0 = read_best()
print(f"{a.tag} start best {s0:.16f} n {len(x0)} args {vars(a)}", file=log, flush=True)
k = wins = 0
while True:
    left = a.seconds - (time.time() - t0); secs = min(float(rng.choice(SECS)), left - 8)
    if secs < 8 or (a.n and k >= a.n): break
    k += 1; x, s_in = read_best(); n = len(x)
    sigma = 10 ** rng.uniform(np.log10(a.smin), np.log10(a.smax)); p0 = float(rng.choice(P0S))
    v = x.copy()
    if a.glob:
        L, b = n, 0; v *= 1 + sigma * rng.standard_normal(n)
    else:
        L = int(rng.integers(a.bmin, a.bmax + 1)); b = int(rng.integers(0, n - L)); v[b:b + L] *= 1 + sigma * rng.standard_normal(L)
    start, out = os.path.join(work, "start.npz"), os.path.join(work, "out.npz"); np.savez(start, x=v)
    try:
        subprocess.run([sys.executable, S5, start, "1", str(p0), "1500", str(secs), "20", out, "3.4e7"],
                       capture_output=True, text=True, timeout=secs + 60, env=dict(os.environ, OMP_NUM_THREADS="1"))
        c = np.load(out)["x"].astype(float); cs = score(c)
    except Exception as e:
        print(f"{a.tag} k {k} error {e}", file=log, flush=True); continue
    won = cs < s_in and offer(c, cs); wins += won
    np.savez(os.path.join(a.shared, f"samp_{a.tag}_{k:02d}.npz"), x=c, sigma=sigma, L=L, b=b, p0=p0, secs=secs, s_in=s_in, s_out=cs)
    print(f"{a.tag} k {k} t {time.time()-t0:.0f} sigma {sigma:.2e} block {L}@{b} p0 {p0:.0f} secs {secs:.0f} "
          f"in {s_in:.16f} out {cs:.16f} d {cs-s_in:+.3e} vs_bar {cs-BAR:+.3e}{' WIN' if won else ''}", file=log, flush=True)
x, s = read_best()
print(f"{a.tag} final samples {k} wins {wins} shared best {s:.16f} vs_bar {s-BAR:+.3e}", file=log, flush=True)
print(f"{a.tag} final samples {k} wins {wins} shared best {s:.16f} vs_bar {s-BAR:+.3e}")
