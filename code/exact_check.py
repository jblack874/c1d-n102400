import json, sys
from fractions import Fraction
d = json.load(open(sys.argv[1]))
if isinstance(d, dict):
    print('keys:', [k for k in d][:12])
    v = next(val for val in d.values() if isinstance(val, list) and len(val) > 100)
else:
    v = d
v = [int(x) for x in v]
n = len(v); mxv = max(abs(x) for x in v)
K = 8 * ((2 * mxv.bit_length() + n.bit_length() + 9) // 8 + 1)
P = 0
for x in reversed(v):
    P = (P << K) + x
P2 = P * P
nb = K // 8
b = P2.to_bytes((P2.bit_length() + 7) // 8 + nb + 1, 'little')
half, full = 1 << (K - 1), 1 << K
carry = 0; mx = 0; arg = -1
for m in range(2 * n - 1):
    s = int.from_bytes(b[nb * m:nb * m + nb], 'little') + carry
    if s >= half:
        s -= full; carry = 1
    else:
        carry = 0
    if abs(s) > mx:
        mx = abs(s); arg = m
r = Fraction(2 * n * mx, sum(v) ** 2)
print('cells', n, 'max|v| = 2^%.2f' % (mxv.bit_length() - 1 + 0.0), 'argmax k', arg)
print('exact', r.numerator, '/', r.denominator)
print('= %.16f' % float(r))
claimed = Fraction(21267647941510998263770007610303168512, 14626277862557668614837367632277156521)
import os; rec = os.environ.get('RECORD'); print('below RECORD %s: %s' % (rec, r < Fraction(rec))) if rec else None
