"""Turn a search result (float cell values) into an integer certificate with its exact score.

Usage: python c1d_mkcert.py <in.npz|in.json> <out.json> <bits> <method note> [--record X]...
  in.npz : float cell values under key x; they are scaled so the largest |value| is 2^bits and rounded to integers.
  in.json: an existing certificate; its integers (key v_int) are kept as they are.
The exact score is computed by c1d_check_kron.score from the ROUNDED integers, so the certified number is that
of the integer function, not of the floats. The decimal "claim" is the exact score rounded UP to 10 places.
"""
import os, sys, json
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # own folder only (needed under python -I)
from c1d_check_kron import score, floor_dec

if len(sys.argv) < 5:
    raise SystemExit("usage: c1d_mkcert.py <in.npz|in.json> <out.json> <bits> <method note> [--record X]...")
src, dst, bits, note = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
if src.endswith(".npz"):
    x = np.asarray(np.load(src)["x"], dtype=np.float64)          # float64 always, whatever the stored dtype
    if not np.all(np.isfinite(x)):
        raise SystemExit("FAIL: non-finite cell values")
    scale = float(1 << bits) / float(np.abs(x).max())
    v = [int(round(float(t) * scale)) for t in x]
else:
    d0 = json.load(open(src))
    v = d0["v_int"]
    if not all(type(t) is int for t in v):
        raise SystemExit("FAIL: v_int must hold JSON integers")
r, mx, knots, S, _ = score(v)
q, rem = divmod(r.numerator * 10 ** 10, r.denominator)
q += 1 if rem else 0                                             # round UP: the claim is an upper bound
s = str(q).rjust(11, "0")
claim = s[:-10] + "." + s[-10:]
assert Fraction(claim) >= r
cert = {"constant": "C_1d", "bound": "upper", "n": len(v), "claim": claim,
        "score_num": str(r.numerator), "score_den": str(r.denominator),
        "deciding_knot": knots[0], "v_int": v, "note": note}
json.dump(cert, open(dst, "w"), separators=(",", ":"))
print("wrote", dst, "n", len(v), "max|v| bits", max(abs(t) for t in v).bit_length())
print("EXACT %d/%d" % (r.numerator, r.denominator))
print("decimal %s... (floor to 30 places)" % floor_dec(r))
print("claim C_1d <=", claim, "| deciding lag", knots, "| lags at max", len(knots))
i = 5
while i < len(sys.argv):
    if sys.argv[i] != "--record" or i + 1 >= len(sys.argv):
        raise SystemExit("usage error near %s" % sys.argv[i])
    rec = Fraction(sys.argv[i + 1])
    print("vs record %s: beats=%s margin %.6e" % (sys.argv[i + 1][:24], r < rec, float(rec - r)))
    i += 2
