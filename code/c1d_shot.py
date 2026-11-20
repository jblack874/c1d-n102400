"""C_1d shotgun sampler around #374's certificate.
Each sample: perturb the current best (random block noise at a random scale, or a factor-2 split with a random
symmetry-breaking kick = high resolution 204,800 cells), then a short high-p polish with s5_search.py; keep if the
TRUE score drops. Usage: python3 c1d_shot.py <cert.json> <seconds> <seed> <outdir>
"""
import sys, os, json, time, subprocess, re, numpy as np
cert, T, seed, outdir = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
os.makedirs(outdir, exist_ok=True); rng = np.random.default_rng(seed); t0 = time.time()
here = os.path.dirname(os.path.abspath(__file__)); S5 = os.path.join(here, "aaron", "s5_search.py")
BAR = 1.4513064006879361
d = json.load(open(cert)); x = np.array([float(int(t)) for t in d.get("v_int", d.get("values"))])
def score(v):
    n = len(v); m = 1 << int(np.ceil(np.log2(2 * n))); F = np.fft.rfft(v, m); c = np.fft.irfft(F * F, m)[:2 * n - 1]
    return 2 * n * np.abs(c).max() / v.sum() ** 2
best = x; bscore = score(x); bestf = os.path.join(outdir, "c1d_best.npz"); np.savez(bestf, x=best)
log = open(os.path.join(outdir, "c1d_shot.log"), "a")
print(f"start score {bscore:.16f} n {len(x)}", file=log, flush=True)
k = 0
while time.time() - t0 < T - 20:
    k += 1; left = T - (time.time() - t0); secs = min(rng.choice([25, 40, 60]), left - 10)
    if secs < 10: break
    mode = rng.choice(["block", "global", "split"], p=[0.45, 0.25, 0.3]) if len(best) == 102400 else rng.choice(["block", "global"])
    sigma = 10 ** rng.uniform(-7, -3); start = os.path.join(outdir, "start.npz"); out = os.path.join(outdir, "out.npz")
    env = dict(os.environ, OMP_NUM_THREADS="1")
    if mode == "split":
        src, factor = bestf, 2; env["KICK"] = f"{sigma:.3e}"; env["SEED"] = str(int(rng.integers(1 << 30)))
    else:
        v = best.copy(); n = len(v)
        if mode == "block":
            L = int(rng.integers(16, 4096)); a = int(rng.integers(0, n - L)); v[a:a + L] *= 1 + sigma * rng.standard_normal(L)
        else:
            v *= 1 + sigma * rng.standard_normal(n)
        np.savez(start, x=v); src, factor = start, 1
    p0 = float(rng.choice([4096, 65536, 1e6]))
    try:
        r = subprocess.run([sys.executable, S5, src, str(factor), str(p0), "1500", str(secs), "20", out, "3.4e7"],
                           capture_output=True, text=True, timeout=secs + 60, env=env)
        mm = re.findall(r"final best ([0-9.]+)", r.stdout + r.stderr)
        cand = np.load(out)["x"].astype(float); cs = score(cand)
    except Exception as e:
        print(f"k {k} {mode} error {e}", file=log, flush=True); continue
    tag = ""
    if cs < bscore:
        best, bscore = cand, cs; np.savez(bestf, x=best); tag = " NEW BEST"
    print(f"k {k} t {time.time()-t0:.0f} {mode} sigma {sigma:.1e} p0 {p0:.0f} n {len(cand)} score {cs:.16f} best {bscore:.16f} vs_bar {bscore-BAR:+.3e}{tag}", file=log, flush=True)
print(f"final samples {k} n {len(best)} best {bscore:.16f} vs_bar {bscore-BAR:+.3e} file {bestf}", file=log, flush=True)
print(f"final samples {k} n {len(best)} best {bscore:.16f} vs_bar {bscore-BAR:+.3e} file {bestf}")
