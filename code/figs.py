"""Figures for the 2026-11-19 sprint results (static PNGs for posting). Palette: dataviz reference, light mode."""
import json, numpy as np, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from scipy.signal import fftconvolve as cv
B = "/home/claude/h/c1d-handoff/"; OUT = B + "figs/"
import os; os.makedirs(OUT, exist_ok=True)
SURF, T1, T2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e6e5e1"
S = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4"]
plt.rcParams.update({"figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
                     "axes.labelcolor": T2, "xtick.color": T2, "ytick.color": T2, "text.color": T1, "font.size": 10,
                     "axes.titlesize": 12, "axes.titleweight": "bold", "axes.titlelocation": "left", "axes.grid": True,
                     "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False})
def ld(p):
    d = json.load(open(p)); return np.array([float(t) for t in d.get("v_int", d.get("values"))])

# 1. C_1d certificate: f and f*f
v = ld(B + "np5/v1/cert.json"); n = len(v); x = -0.25 + (np.arange(n) + 0.5) / (2 * n)
c = cv(v, v); r = 2 * n * c / v.sum() ** 2; t = -0.5 + (np.arange(2 * n - 1) + 1) / (2 * n); M = np.abs(r).max()
fig, ax = plt.subplots(2, 1, figsize=(9, 6.4), height_ratios=[1, 1.1])
ax[0].plot(x, v / v.sum() * 2 * n, color=S[0], lw=0.6)
ax[0].axhline(0, color=T2, lw=0.8)
ax[0].set_title("C_1d certificate: step function f (102,400 cells), normalized to mean 1")
ax[0].set_xlabel("x"); ax[0].set_ylabel("f(x) / mean f")
ax[1].plot(t, r, color=S[0], lw=0.6)
ax[1].axhline(M, color=S[1], lw=1.2, ls="--"); ax[1].axhline(-M, color=S[1], lw=1.2, ls="--")
ax[1].set_title("Autoconvolution f∗f / (∫f)²: the bound is its largest absolute value")
ax[1].set_xlabel(f"t        (dashed lines: ±{M:.10f} = max |f∗f| / (∫f)², the bound)"); ax[1].set_ylabel("(f∗f)(t) / (∫f)²")
fig.tight_layout(); fig.savefig(OUT + "1_c1d_certificate.png", dpi=150); plt.close(fig)

# 2. Tightness gate profiles
def prof(vals, sense="max"):
    vals = np.asarray(vals, float)
    if sense == "max": m = vals.max(); g = (m - vals) / abs(m)
    else: m = vals.min(); g = (vals - m) / abs(m)
    return np.sort(g[g >= 0])
P = {}
P["C_1d (v1) — loose, NP won"] = prof(np.abs(c))
a = np.load(B + "g/c1a/best.npy"); P["1a first autocorrelation — tight"] = prof(cv(a, a))
h = np.load(B + "g/c1b/best.npy"); m_ = len(h); P["1b Erdős overlap — tight"] = prof(cv(h, np.ones(m_)[::-1]) - cv(h, h[::-1]))
w = np.load(B + "g/c1c/best.npy"); K = int(open(B + "g/c1c/K.txt").read()); P["1c Barnard–Steinerberger — tight"] = prof(cv(w, w[::-1])[len(w) - 1:][:K + 1], "min")
at = np.load(B + "dl/a64/v.npy"); P["Arena 6.4 (Atris) — tight"] = prof(cv(at, at))
ds = np.logspace(-12, -5, 300)
fig, ax = plt.subplots(figsize=(9, 5.2))
styles = ["-", "--", "-.", ":", (0, (5, 1))]
for i, (k, g) in enumerate(P.items()):
    y = np.searchsorted(g, ds, side="right")
    ax.plot(ds, np.maximum(y, 0.8), color=S[i], lw=2, ls=styles[i], label=k)
ax.set_xscale("log"); ax.set_yscale("log")
ax.axvline(1e-8, color=T2, lw=0.8); ax.axvline(1e-7, color=T2, lw=0.8)
ax.text(1e-8, ax.get_ylim()[1], " 1e-8", color=T2, va="top", fontsize=9); ax.text(1e-7, ax.get_ylim()[1], " 1e-7", color=T2, va="top", fontsize=9)
ax.set_xlabel("relative distance from the binding value δ"); ax.set_ylabel("constraints within δ (count)")
ax.set_title("NP-β2 tightness gate: loose records climb late, tight records are already flat")
ax.legend(frameon=False, fontsize=9, loc="lower right")
fig.text(0.01, 0.005, "Gate passes when count(≤1e-8) ≤ 1% of count(≤1e-7). C_1d: 19 vs 12,818 (0.15%). Others: 92–100%.", color=T2, fontsize=8.5)
fig.tight_layout(rect=(0, 0.03, 1, 1)); fig.savefig(OUT + "2_tightness_gate.png", dpi=150); plt.close(fig)

# 3. Record chain vs #374
chain = [("#374 (bar)", 1.4513064006879361), ("Shotgun 12:15", 1.4513063999152274), ("Run 1 14:02", 1.4513063934337895),
         ("Run 2 14:22", 1.4513063921690856), ("Run 3 14:55", 1.4513063899323682), ("Run 4 15:11", 1.4513063896445777),
         ("Run 5 17:14", 1.4513063886307913)]
gap = [(1.4513064006879361 - val) * 1e9 for _, val in chain]
fig, ax = plt.subplots(figsize=(9, 4.6))
ax.bar(range(len(chain)), gap, color=S[0], width=0.62)
for i, gv in enumerate(gap):
    if i: ax.text(i, gv, f"{gv:.2f}", ha="center", va="bottom", fontsize=9, color=T1)
ax.set_xticks(range(len(chain))); ax.set_xticklabels([k for k, _ in chain], fontsize=8.5)
ax.set_ylabel("below #374 (×1e-9)"); ax.grid(axis="x", visible=False)
ax.set_title("C_1d record chain, 2026-11-19: exact margin below registry PR #374")
fig.text(0.01, 0.005, "Every point exact-checked by two independent checkers. Runs 1–4 NP-β1, run 5 NP-β2.", color=T2, fontsize=8.5)
fig.tight_layout(rect=(0, 0.03, 1, 1)); fig.savefig(OUT + "3_record_chain.png", dpi=150); plt.close(fig)

# 4. Heilbronn n = 11 configuration
p = np.array(json.load(open(B + "heil_fix/heil11_exact_valid.json"))["points"])
fig, ax = plt.subplots(figsize=(6.6, 6.2))
tri = np.array([[0, 0], [1, 0], [0.5, np.sqrt(3) / 2]])
ax.add_patch(Polygon(tri, closed=True, fill=False, ec=T2, lw=1.2))
ax.add_patch(Polygon(p[[1, 3, 7]], closed=True, fc=S[2], ec=S[2], alpha=0.35, lw=1.5))
ax.scatter(p[:, 0], p[:, 1], s=46, color=S[0], zorder=3, ec=SURF, lw=1.5)
ax.scatter([p[8, 0]], [p[8, 1]], s=110, color=S[1], zorder=4, ec=SURF, lw=2)
for i, (px, py) in enumerate(p):
    ax.text(px + 0.012, py + 0.012, str(i), fontsize=9, color=T1)
ax.annotate("point 8: 1.85e-17 outside the edge in the\nrecord; fixed by 1 ulp, same exact score", xy=p[8], xytext=(0.02, 0.78),
            fontsize=9, color=T1, arrowprops=dict(arrowstyle="-", color=T2, lw=0.8))
ax.text(0.70, 0.80, "shaded: smallest triangle\n(points 1, 3, 7)", color=T1, fontsize=9)
ax.set_aspect("equal"); ax.set_xlim(-0.03, 1.03); ax.set_ylim(-0.04, 0.92); ax.grid(False)
ax.set_xticks([]); ax.set_yticks([]); [s.set_visible(False) for s in ax.spines.values()]
ax.set_title("Heilbronn triangles, n = 11 (arena record, exactly valid version)\nmin area / (√3/4) = 0.0365298898800301288…")
fig.tight_layout(); fig.savefig(OUT + "4_heilbronn11.png", dpi=150); plt.close(fig)
print("ok")
