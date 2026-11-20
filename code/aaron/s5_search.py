"""Sprint 5 search step for C_1d step functions: smooth, then sharpen (lean optimizer).

score(v) = 2 n max_m |(v*v)_m| / (sum v)^2 for a step function with n equal cells on [-1/4, 1/4].

Every lag of the autoconvolution feeds the optimizer: the objective is log ||v*v||_p - 2 log S over ALL
2n-1 lags, so every near-active point carries weight. p starts low and doubles stage by stage.
Start: a record certificate with each cell split into `factor` equal cells (same function, same score).
Optimizer: own L-BFGS (two-loop recursion, strong-Wolfe line search); two FFT pairs per evaluation.
The best TRUE score seen at any evaluation is kept and checkpointed.

One call is one cycle of the loop: start at a LOW p (strong smoothing), double p stage by stage (sharpen).
The loop driver (s5_loop.py) feeds the best result back in as the next start.

Usage: python s5_search.py <cert.json|ckpt.npz> <factor> <p0> <iters_per_stage> <seconds> <memory> <out.npz> [pmax]
Needs numpy and scipy.
"""
import os, sys, json, time
for _k in ("OMP_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "OPENBLAS_NUM_THREADS"):
    os.environ.setdefault(_k, "1")          # one thread per worker: many workers share the machine
import numpy as np
import scipy.fft as sf
from scipy.linalg.blas import ddot, daxpy

t0 = time.time()
src, factor, p0, iters, tlimit, mem, out = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
pmax = float(sys.argv[8]) if len(sys.argv) > 8 else 1e12
if src.endswith(".npz"):
    import os
    v = np.load(src)["xcur" if os.environ.get("RESUME_CUR") else "x"].astype(float)   # RESUME_CUR=1 continues an interrupted schedule
else:
    d = json.load(open(src))
    v = np.array([float(int(t)) for t in d.get("v_int", d.get("values"))])
x = np.repeat(v, factor)
import os
kick = float(os.environ.get("KICK", "0"))
if kick and factor == 2:
    # symmetry-breaking kick: move mass between the two halves of each old cell (sum unchanged).
    # The two halves start equal, which is a stationary point for the new degrees of freedom.
    e = kick * v * np.random.default_rng(int(os.environ.get("SEED", "1"))).standard_normal(len(v))
    x[0::2] += e; x[1::2] -= e
noise = float(os.environ.get("NOISE", "0"))
if noise:                                    # optional diversity for the loop search: multiplicative jitter
    x = x * (1 + noise * np.random.default_rng(int(os.environ.get("SEED", "1"))).standard_normal(len(x)))
x *= len(x) / x.sum()                       # normalise: mean cell value 1
n = len(x); M = 2 * n - 1; L = sf.next_fast_len(M, real=True)
st = {"best": np.inf, "bx": None, "nev": 0, "tp": 0.0, "m90": False, "R0": None}


class OutOfTime(Exception):
    pass


def fg(x, p):
    el = time.time() - t0
    if el > tlimit:
        raise OutOfTime()
    X = sf.rfft(x, L); c = sf.irfft(X * X, L)[:M]
    q = np.abs(c); mx = q.max(); S = x.sum()
    R = 2 * n * mx / S ** 2
    st["nev"] += 1
    if R < st["best"]:
        st["best"] = R; st["bx"] = x.copy()
    if st["R0"] is not None:
        if not st["m90"] and el >= 90.0:
            st["m90"] = True
            print("MARK90 best %.15f gain %.3e p %.4g nev %d" % (st["best"], st["R0"] - st["best"], p, st["nev"]), flush=True)
        if el - st["tp"] >= 30.0:
            st["tp"] = el
            print("  .. t %.0f p %.4g R %.15f best %.15f gain %.3e nev %d" % (el, p, R, st["best"], st["R0"] - st["best"], st["nev"]), flush=True)
    r = q / mx
    idx = np.flatnonzero(r > 1.0 - 700.0 / p) if p > 2000 else np.flatnonzero(r > 0)
    ri = r[idx]
    e = np.exp(p * np.log(ri)); se = e.sum()
    f = np.log(mx) + np.log(se) / p - 2 * np.log(S)
    w = np.zeros(L)
    w[idx] = (e / ri) * np.sign(c[idx]) / (mx * se)
    g = 2 * sf.irfft(sf.rfft(w) * np.conj(X), L)[:n] - 2.0 / S
    return f, g


def wolfe(x, f0, g0, dvec, dg0, a, p, c1=1e-4, c2=0.9, maxev=30):
    """Strong-Wolfe line search (bracket then zoom). Returns (alpha, f, g, xnew) or None."""
    lo = (0.0, f0, dg0, g0, x); hi = None; prev = lo; best = None
    for k in range(maxev):
        xn = x + a * dvec
        f, g = fg(xn, p); dg = ddot(g, dvec)
        cur = (a, f, dg, g, xn)
        armijo = f <= f0 + c1 * a * dg0
        if armijo and (best is None or f < best[1]):
            best = cur
        if hi is None:                                   # bracketing phase
            if (not armijo) or (k > 0 and f >= prev[1]):
                lo, hi = prev, cur
            elif abs(dg) <= -c2 * dg0:
                return cur
            elif dg >= 0:
                lo, hi = cur, prev
            else:
                prev = cur; a *= 2.0
                continue
        else:                                            # zoom phase
            if (not armijo) or f >= lo[1]:
                hi = cur
            else:
                if abs(dg) <= -c2 * dg0:
                    return cur
                if dg * (hi[0] - lo[0]) >= 0:
                    hi = lo
                lo = cur
        # next trial: cubic through lo and hi, safeguarded; else bisect
        a_l, f_l, d_l = lo[0], lo[1], lo[2]; a_h, f_h, d_h = hi[0], hi[1], hi[2]
        a = None
        try:
            d1 = d_l + d_h - 3 * (f_l - f_h) / (a_l - a_h)
            rad = d1 * d1 - d_l * d_h
            if rad >= 0:
                d2 = np.sign(a_h - a_l) * np.sqrt(rad)
                a = a_h - (a_h - a_l) * (d_h + d2 - d1) / (d_h - d_l + 2 * d2)
        except Exception:
            a = None
        w0, w1 = min(a_l, a_h), max(a_l, a_h); margin = 0.1 * (w1 - w0)
        if a is None or not np.isfinite(a) or a < w0 + margin or a > w1 - margin:
            a = 0.5 * (a_l + a_h)
        if w1 - w0 < 1e-14 * max(1.0, w1):
            break
    return best


def stage(x, p, iters, mem):
    f, g = fg(x, p)
    S = []; Y = []; RHO = []
    first = True; nit = 0
    for it in range(iters):
        q = g.copy(); al = []
        for s, y, r in zip(reversed(S), reversed(Y), reversed(RHO)):
            a = r * ddot(s, q); al.append(a); q = daxpy(y, q, a=-a)
        if S:
            q *= ddot(S[-1], Y[-1]) / ddot(Y[-1], Y[-1])
        for s, y, r, a in zip(S, Y, RHO, reversed(al)):
            b = r * ddot(y, q); q = daxpy(s, q, a=a - b)
        dvec = -q; dg0 = ddot(g, dvec)
        if dg0 >= 0:                                      # not a descent direction: restart memory
            S = []; Y = []; RHO = []; dvec = -g; dg0 = -ddot(g, g); first = True
        a0 = 1e-3 * np.sqrt(ddot(x, x) / ddot(dvec, dvec)) if first else 1.0
        res = wolfe(x, f, g, dvec, dg0, a0, p)
        if res is None:
            if S:
                S = []; Y = []; RHO = []; first = True
                continue
            break
        a, fn, dgn, gn, xn = res
        s = xn - x; y = gn - g; sy = ddot(s, y)
        if sy > 1e-10 * np.sqrt(ddot(s, s) * ddot(y, y)):
            S.append(s); Y.append(y); RHO.append(1.0 / sy)
            if len(S) > mem:
                S.pop(0); Y.pop(0); RHO.pop(0)
        x, f, g = xn, fn, gn; first = False; nit += 1
    return x, nit


def true_ratio(x):
    X = sf.rfft(x, L); c = sf.irfft(X * X, L)[:M]
    return 2 * n * np.abs(c).max() / x.sum() ** 2


R0 = true_ratio(x)
st["best"] = R0; st["bx"] = x.copy(); st["R0"] = R0
print("n %d L %d init %.15f p0 %g iters %d mem %d" % (n, L, R0, p0, iters, mem), flush=True)
p = p0
try:
    while p <= pmax:
        x, nit = stage(x, p, iters, mem)
        x *= n / x.sum()
        R = true_ratio(x)
        print("p %.4g R %.15f best %.15f gain %.3e nit %d nev %d t %.1f" % (p, R, st["best"], R0 - st["best"], nit, st["nev"], time.time() - t0), flush=True)
        np.savez(out, x=st["bx"], best=st["best"], R0=R0, p=p, t=time.time() - t0, xcur=x)
        p *= float(os.environ.get("PMULT", "2"))        # stage-to-stage growth of p (default: doubling)
except OutOfTime:
    pass
print("final best %.15f gain %.3e nev %d t %.1f" % (st["best"], R0 - st["best"], st["nev"], time.time() - t0), flush=True)
np.savez(out, x=st["bx"], best=st["best"], R0=R0, p=p, t=time.time() - t0, xcur=x)
