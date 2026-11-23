"""Generate Lean Data/Challenge/Solution modules for an autoconvolution certificate.

Usage: python3 -I gen_cert.py VALUES_JSON NAMESPACE OUTDIR BOUND_DECIMAL ABS
  VALUES_JSON  {"values": [...]} or {"v_int": [...]} (integer cell heights)
  ABS          1: signed heights, statement about max |c_k| (C_1d); 0: nonnegative heights, max c_k (C_1a)
"""
import json, sys, hashlib, os
from fractions import Fraction


def pack(vals, width):
    """sum(vals[i] << (width*i)), by halving (vals nonnegative)."""
    if len(vals) <= 64:
        r = 0
        for x in reversed(vals):
            r = (r << width) | x
        return r
    h = len(vals) // 2
    return pack(vals[:h], width) | (pack(vals[h:], width) << (width * h))

path, ns, out, bound, absflag = sys.argv[1:6]
absmode = absflag == '1'
raw = open(path, 'rb').read()
sha = hashlib.sha256(raw).hexdigest()
d = json.loads(raw)
v = [int(x) for x in (d.get('values') or d.get('v_int'))]
n = len(v)
S = sum(v)
if not absmode:
    assert min(v) >= 0
CZ = 256
assert n % CZ == 0
w = 1
while not all(-(1 << (w - 1)) <= x < (1 << (w - 1)) for x in v):
    w += 1
o = 1 << (w - 1)
M0 = n * o * o
# exact convolution (Python Kronecker, independent of the Lean proof)
Kc = (2 * M0).bit_length() + 1
Kc += (-Kc) % 8
L = 2 * n - 1
pos = pack([x if x > 0 else 0 for x in v], Kc)
neg = pack([-x if x < 0 else 0 for x in v], Kc)
Bc = 1 << Kc
Nc = (pos - neg) ** 2 + M0 * ((Bc ** L - 1) // (Bc - 1))
nb = Kc // 8
by = Nc.to_bytes(nb * L + 1, 'little')
c = [int.from_bytes(by[k * nb:(k + 1) * nb], 'little') - M0 for k in range(L)]
assert all(-M0 <= x <= M0 for x in c)
if absmode:
    M = max(abs(x) for x in c)
    k0 = max(range(L), key=lambda k: abs(c[k]))
else:
    M = max(c)
    k0 = c.index(M)
    assert min(c) >= 0
t = (M0 + M).bit_length()
assert M0 + M < 2 ** t
K = max(t, (n << w).bit_length(), (2 * M0).bit_length()) + 2
assert 2 * M0 + (2 ** t - 1 - (M0 + M)) < 2 ** K and t <= K and w <= K and n * 2 ** w < 2 ** K - 1
score = Fraction(2 * n * M, S * S)
bnum = int(bound.replace('.', ''))
bden = 10 ** len(bound.split('.')[1])
assert score <= Fraction(bnum, bden), (float(score), bound)
cfuel = (n // CZ).bit_length() + 2
chunks = [pack([x + o for x in v[j:j + CZ]], K) for j in range(0, n, CZ)]
Pall = pack(chunks, K * CZ)
assert [((Pall >> (K * i)) & ((1 << K) - 1)) - o for i in range(0, n, 997)] == v[::997]

os.makedirs(f"{out}/{ns}", exist_ok=True)
chunk_txt = ",\n  ".join(hex(p) for p in chunks)
open(f"{out}/{ns}/Data.lean", "w").write(f"""import Autoconv.Pack
/-!
Certificate data for `{ns}`: the {n} integer cell heights of `{os.path.basename(path)}`
(SHA-256 `{sha}`). Height `i` is the `i`-th base-`2^K` digit of `P` minus `2^(w-1)`, with `K = {K}`, `w = {w}`;
`P` is assembled from {n // CZ} chunks of {CZ} digits (chunked so the literals parse quickly).
`tools/gen_cert.py` regenerates this file from the JSON.
-/
namespace {ns}
open Autoconv

def n : Nat := {n}
def K : Nat := {K}
def w : Nat := {w}
def parts : List Nat := [
  {chunk_txt}]
def P : Nat := combine K {CZ} {cfuel} parts
/-- The cell heights `v_0, …, v_{{n-1}}`. -/
def v : List Int := unpackK K (2 ^ (w - 1)) n P

end {ns}
""")

quant = "(conv v v k).natAbs ≤ M" if absmode else "conv v v k ≤ M"
att = f"(conv v v {k0}).natAbs = M" if absmode else f"conv v v {k0} = M"
stmt = f"""v.length = n ∧ v.sum = S ∧
    (∀ k, {quant}) ∧ {att} ∧
    (2 * n * M * den : Int) = num * S ^ 2 ∧ num * {bden} ≤ {bnum} * den"""
what = "max_k |c_k| = M" if absmode else "max_k c_k = M"
cont = "max_t |(f*f)(t)| / (∫f)²" if absmode else "max_t (f*f)(t) / (∫f)²"


def hdr(title, imp):
    return f"""import {ns}.Data
import {imp}
/-!
# {title}

With `c_k = conv v v k = Σ_{{i+j=k}} v_i v_j` and `S = Σ v_i`: `{what}` (attained at `k = {k0}`),
and `2·n·M / S² = num/den ≤ {bound}`.
By the knot formula for step functions with `n` equal cells on `[-1/4, 1/4]`, `2·n·M/S²` equals
`{cont}` for the step function with these heights; that formula is not formalized here.
-/
namespace {ns}
open Autoconv

def M : Nat := {M}
def S : Int := {S}
def num : Nat := {score.numerator}
def den : Nat := {score.denominator}
"""


open(f"{out}/{ns}/Challenge.lean", "w").write(hdr("Challenge statement", "Autoconv.Basic") + f"""
theorem certificate :
    {stmt} := by sorry

end {ns}
""")

bnd = ("exact final_bound K w n P t M (by decide +kernel) (by decide) (by decide) (by decide) (by decide) hP hA hU hC h1 h2 k" if absmode else
       "exact Int.le_trans Int.le_natAbs (by exact_mod_cast final_bound K w n P t M (by decide +kernel) (by decide) (by decide) (by decide) (by decide) hP hA hU hC h1 h2 k)")
attp = (f"rw [final_digit K w n P (by decide +kernel) (by decide) (by decide) (by decide) hP hA hM0 {k0} (by decide), hdig]; decide")
open(f"{out}/{ns}/Solution.lean", "w").write(hdr("Solution: proved by kernel computation", "Autoconv.Final") + f"""
private def t : Nat := {t}

private theorem hP : P < (2 ^ K) ^ n := by decide +kernel
private theorem hA : P &&& (hiMask K w * rep (2 ^ K) n) = 0 := by decide +kernel
private theorem hU : M0f n w + M < 2 ^ t := by decide +kernel
private theorem hC : 2 * M0f n w + (2 ^ t - 1 - (M0f n w + M)) < 2 ^ K := by decide +kernel
private theorem hM0 : 2 * M0f n w < 2 ^ K := by decide +kernel
private theorem hS : n * 2 ^ w < 2 ^ K - 1 := by decide +kernel
private theorem h1 : (Nf K w n P + (2 ^ t - 1 - (M0f n w + M)) * rep (2 ^ K) (2 * n - 1)) &&&
      (hiMask K t * rep (2 ^ K) (2 * n - 1)) = 0 := by decide +kernel
private theorem h2 : (2 * M0f n w * rep (2 ^ K) (2 * n - 1) - Nf K w n P +
      (2 ^ t - 1 - (M0f n w + M)) * rep (2 ^ K) (2 * n - 1)) &&& (hiMask K t * rep (2 ^ K) (2 * n - 1)) = 0 := by
  decide +kernel
private theorem hdig : ((Nf K w n P >>> (K * {k0}) % 2 ^ K : Nat) : Int) - M0f n w = {c[k0]} := by decide +kernel
private theorem hsum : ((P % (2 ^ K - 1) : Nat) : Int) - ((2 ^ (w - 1) : Nat) : Int) * n = S := by decide +kernel

theorem certificate :
    {stmt} := by
  refine ⟨length_unpackK _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · show (unpackK K (2 ^ (w - 1)) n P).sum = S
    rw [final_sum K w n P (by decide +kernel) (by decide) hP hA hS]; exact hsum
  · intro k
    show {quant.replace("conv v v k", "conv (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P) k")}
    {bnd}
  · show {att.replace(f"conv v v {k0}", f"conv (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P) {k0}")}
    {attp}
  · decide +kernel
  · decide +kernel

end {ns}
""")
print(json.dumps(dict(n=n, w=w, K=K, t=t, M=M, k0=k0, ck0=c[k0], S=S, score=str(float(score)),
                      num=score.numerator, den=score.denominator, sha=sha)))
