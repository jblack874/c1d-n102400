"""Grade NP run samples: score, gain vs its input, vs bar, tied lags at the max, distance to the shared best."""
import sys, glob, os, json, numpy as np
d = sys.argv[1]; BAR = 1.4513064006879361
def corr(v):
    n=len(v); m=1<<int(np.ceil(np.log2(2*n))); F=np.fft.rfft(v,m); return np.fft.irfft(F*F,m)[:2*n-1]
best = np.load(f"{d}/best.npz")["x"].astype(float); bn = best/best.sum()
rows=[]
for f in sorted(glob.glob(f"{d}/samp_*.npz")):
    z=np.load(f); x=z["x"].astype(float); c=np.abs(corr(x)); s=2*len(x)*c.max()/x.sum()**2
    ties=int((c >= c.max()*(1-1e-12)).sum()); dist=float(np.linalg.norm(x/x.sum()-bn)/np.linalg.norm(bn))
    tag,k=os.path.basename(f)[5:-4].rsplit("_",1)
    rows.append(dict(id=f"{tag}-{k}", score=s, vs_bar=s-BAR, d_in=float(z["s_out"]-z["s_in"]), win=bool(z["s_out"]<z["s_in"]),
        sigma=float(z["sigma"]), block=int(z["L"]), p0=int(z["p0"]), secs=int(z["secs"]), ties=ties, dist=dist))
rows.sort(key=lambda r:r["score"])
json.dump(rows, open(f"{d}/graded.json","w"), indent=1)
print(f"{'rank':>4} {'id':8} {'score':>20} {'vs_bar':>10} {'d_vs_input':>11} {'win':>4} {'sigma':>8} {'block':>5} {'p0':>6} {'secs':>4} {'ties':>4} {'dist_to_best':>12}")
for i,r in enumerate(rows,1):
    print(f"{i:>4} {r['id']:8} {r['score']:.16f} {r['vs_bar']:+.3e} {r['d_in']:+.3e} {'Y' if r['win'] else '-':>4} {r['sigma']:.1e} {r['block']:>5} {r['p0']:>6} {r['secs']:>4} {r['ties']:>4} {r['dist']:.2e}")
w=[r for r in rows if r['win']]; print(f"wins {len(w)}/{len(rows)}; by worker:", {t:sum(r['win'] for r in rows if r['id'].startswith(t)) for t in ('b1a','b1b')})
