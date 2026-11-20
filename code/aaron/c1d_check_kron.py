"""Exact checker 1 for C_1d step-function certificates: Kronecker substitution.

score(v) = 2 n max_m |c_m| / S^2,   c_m = sum_{i+j=m} v_i v_j (m = 0..2n-2),   S = sum_i v_i.
Exact integers throughout; the absolute value is inside the maximum (the registry's rule for C_1d).

Method: v = P - Q (positive and negative parts, both >= 0), so c = P*P - 2 P*Q + Q*Q. Each product is one
big-integer multiplication of the values packed into fixed-width slots. A coefficient is at most
n * max|v|^2 < 2^(bitlen(n) + 2 bitlen(max|v|)), and the slot is at least that many bits plus 2, so no slot
can overflow or carry into its neighbour.

Usage: python c1d_check_kron.py <certificate.json> [--record X]... [--fraction NUM/DEN] [--save-conv out.npz]
  --record X      the certificate must score strictly below X (X is NUM/DEN or a decimal); may be repeated
  --fraction F    the exact score must equal F
The integers are read from key v_int (or values) and must be JSON integers. If the file also holds n,
score_num/score_den, claim or deciding_knot, they are checked. Exit status 0 only if every check passes.
"""
import sys, json, time
from fractions import Fraction

try:
    from gmpy2 import mpz
except Exception:  # pure Python fallback (slower, same result)
    mpz = int


def load_cert(path):
    with open(path) as fh:
        d = json.load(fh)
    if not isinstance(d, dict):
        raise SystemExit("FAIL: the certificate must be a JSON object")
    key = "v_int" if "v_int" in d else ("values" if "values" in d else None)
    if key is None:
        raise SystemExit("FAIL: no v_int (or values) key")
    v = d[key]
    if not isinstance(v, list) or not v:
        raise SystemExit("FAIL: %s must be a non-empty list" % key)
    for i, x in enumerate(v):
        if type(x) is not int:
            raise SystemExit("FAIL: %s[%d] is not a JSON integer (%r); refusing to truncate" % (key, i, x))
    return v, d


def pack(vals, B):
    return int.from_bytes(b"".join(x.to_bytes(B, "little") for x in vals), "little")


def unpack(z, B, count):
    raw = int(z).to_bytes(B * count, "little")
    return [int.from_bytes(raw[i * B:(i + 1) * B], "little") for i in range(count)]


def exact_conv(v):
    n = len(v)
    P = [x if x > 0 else 0 for x in v]
    Q = [-x if x < 0 else 0 for x in v]
    mxv = max(max(P), max(Q))
    bits = 2 * mxv.bit_length() + n.bit_length() + 2
    B = (bits + 7) // 8
    M = 2 * n - 1
    p = mpz(pack(P, B)); q = mpz(pack(Q, B))
    pp = unpack(p * p, B, M); qq = unpack(q * q, B, M); pq = unpack(p * q, B, M)
    return [pp[m] - 2 * pq[m] + qq[m] for m in range(M)]


def score(v):
    n = len(v)
    S = sum(v)
    if S == 0:
        raise SystemExit("FAIL: the values sum to zero, so the ratio is undefined and gives no bound")
    c = exact_conv(v)
    mx = max(abs(x) for x in c)
    knots = [m for m, x in enumerate(c) if abs(x) == mx]
    return Fraction(2 * n * mx, S * S), mx, knots, S, c


def floor_dec(fr, digits=30):
    """The positive fraction fr as a decimal string, cut off (not rounded) after `digits` places."""
    whole, rest = divmod(fr.numerator, fr.denominator)
    return "%d.%0*d" % (whole, digits, rest * 10 ** digits // fr.denominator)


def verdict(r, knots, n, d, records, fraction):
    """Print every comparison; return True only if all of them pass."""
    ok = True
    if "n" in d:
        good = d["n"] == n; ok &= good
        print("file n = %r: %s" % (d["n"], "matches" if good else "DIFFERS from the number of values (%d)" % n))
    if "score_num" in d and "score_den" in d:
        good = Fraction(int(d["score_num"]), int(d["score_den"])) == r; ok &= good
        print("fraction stated in the file:", "EQUAL" if good else "DIFFERS")
    if "claim" in d:
        good = Fraction(str(d["claim"])) >= r; ok &= good
        print("claim C_1d <= %s:" % d["claim"], "implied" if good else "NOT implied (the claim is below the exact score)")
    if "deciding_knot" in d:
        good = d["deciding_knot"] in knots; ok &= good
        print("file deciding_knot = %r:" % d["deciding_knot"], "attains the maximum" if good else "does NOT attain the maximum")
    if fraction is not None:
        good = Fraction(fraction) == r; ok &= good
        print("fraction given on the command line:", "EQUAL" if good else "DIFFERS")
    for rec in records:
        R = Fraction(rec); good = r < R; ok &= good
        print("record %s: %s (record minus score = %.6e)" % (rec if len(rec) < 40 else rec[:18] + "..." + rec[-12:], "beaten strictly" if good else "NOT beaten", float(R - r)))
    return ok


def parse_args(argv, allowed=("--record", "--fraction", "--save-conv")):
    path, records, fraction, save = None, [], None, None
    i = 1
    while i < len(argv):
        a = argv[i]
        if a in allowed:
            if i + 1 >= len(argv):
                raise SystemExit("usage error: %s needs a value" % a)
            val = argv[i + 1]; i += 2
            if a == "--record":
                records.append(val)
            elif a == "--fraction":
                fraction = val
            else:
                save = val
        elif a.startswith("--"):
            raise SystemExit("usage error: unknown option %s" % a)
        elif path is None:
            path = a; i += 1
        else:
            raise SystemExit("usage error: unexpected argument %s" % a)
    if path is None:
        raise SystemExit("usage error: give the certificate path")
    return path, records, fraction, save


if __name__ == "__main__":
    t0 = time.time()
    path, records, fraction, save = parse_args(sys.argv)
    v, d = load_cert(path)
    r, mx, knots, S, c = score(v)
    print("n", len(v), "max|v|", max(abs(x) for x in v))
    print("S", S)
    print("max|c|", mx, "at lags", knots[:10], "(count %d)" % len(knots))
    print("EXACT %d/%d" % (r.numerator, r.denominator))
    print("decimal %s... (floor to 30 places)" % floor_dec(r))
    ok = verdict(r, knots, len(v), d, records, fraction)
    if save:
        import numpy as np
        sg = np.array([1 if x >= 0 else -1 for x in c], dtype=np.int8)
        slack = np.array([float(mx - abs(x)) for x in c])
        np.savez(save, sign=sg, slack=slack, mx=float(mx), S=float(S))
        print("saved", save)
    print("RESULT: %s (%.1f s)" % ("PASS" if ok else "FAIL", time.time() - t0))
    sys.exit(0 if ok else 1)
