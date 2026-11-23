import C1d.Data
import Autoconv.Basic
/-!
# Challenge statement

With `c_k = conv v v k = Σ_{i+j=k} v_i v_j` and `S = Σ v_i`: `max_k |c_k| = M` (attained at `k = 165136`),
and `2·n·M / S² = num/den ≤ 1.4513063746953753`.
By the knot formula for step functions with `n` equal cells on `[-1/4, 1/4]`, `2·n·M/S²` equals
`max_t |(f*f)(t)| / (∫f)²` for the step function with these heights; that formula is not formalized here.
-/
namespace C1d
open Autoconv

def M : Nat := 10032334394911663717273796490132430
def S : Int := 37625859069456179333
def num : Nat := 2054622084077908729297673521179121664000
def den : Nat := 1415705270714577825348504941537856324889

theorem certificate :
    v.length = n ∧ v.sum = S ∧
    (∀ k, (conv v v k).natAbs ≤ M) ∧ (conv v v 165136).natAbs = M ∧
    (2 * n * M * den : Int) = num * S ^ 2 ∧ num * 10000000000000000 ≤ 14513063746953753 * den := by sorry

end C1d
