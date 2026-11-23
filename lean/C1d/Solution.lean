import C1d.Data
import Autoconv.Final
/-!
# Solution: proved by kernel computation

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

private def t : Nat := 129

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
private theorem hdig : ((Nf K w n P >>> (K * 165136) % 2 ^ K : Nat) : Int) - M0f n w = 10032334394911663717273796490132430 := by decide +kernel
private theorem hsum : ((P % (2 ^ K - 1) : Nat) : Int) - ((2 ^ (w - 1) : Nat) : Int) * n = S := by decide +kernel

theorem certificate :
    v.length = n ∧ v.sum = S ∧
    (∀ k, (conv v v k).natAbs ≤ M) ∧ (conv v v 165136).natAbs = M ∧
    (2 * n * M * den : Int) = num * S ^ 2 ∧ num * 10000000000000000 ≤ 14513063746953753 * den := by
  refine ⟨length_unpackK _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · show (unpackK K (2 ^ (w - 1)) n P).sum = S
    rw [final_sum K w n P (by decide +kernel) (by decide) hP hA hS]; exact hsum
  · intro k
    show (conv (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P) k).natAbs ≤ M
    exact final_bound K w n P t M (by decide +kernel) (by decide) (by decide) (by decide) (by decide) hP hA hU hC h1 h2 k
  · show (conv (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P) 165136).natAbs = M
    rw [final_digit K w n P (by decide +kernel) (by decide) (by decide) (by decide) hP hA hM0 165136 (by decide), hdig]; decide
  · decide +kernel
  · decide +kernel

end C1d
