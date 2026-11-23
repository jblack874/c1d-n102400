/-!
# Autoconvolution of integer sequences: definitions

`gd l i` is the `i`-th entry of `l` (0-indexed), and `0` past the end.
`conv a b k = Σ_{i+j=k} a_i b_j`, written as the sum over `i ≤ k` of `a_i · b_{k-i}`.
-/
namespace Autoconv

/-- `i`-th entry of `l`, or `0` past the end. -/
def gd : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => gd xs k

/-- The `k`-th coefficient of the convolution of `a` and `b`: `Σ_{i ≤ k} a_i · b_{k-i}`. -/
def conv (a b : List Int) (k : Nat) : Int :=
  ((List.range (k + 1)).map fun i => gd a i * gd b (k - i)).sum

end Autoconv
