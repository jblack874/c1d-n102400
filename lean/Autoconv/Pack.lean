import Autoconv.Basic
/-!
# Packed integer lists

Certificate heights are stored as the base-`2^K` digits of one natural number `P`, minus an offset;
`P` is assembled from chunk literals by `combine` (chunked only so that the literals parse quickly).
-/
namespace Autoconv

/-- Join packed chunks `ps` (each `cz` entries of `W` bits) into one packed number, first chunk lowest. -/
def combine (W cz : Nat) : Nat → List Nat → Nat
  | 0, ps => ps.foldr (fun p acc => p + 2 ^ (W * cz) * acc) 0
  | f + 1, ps =>
    if ps.length ≤ 1 then ps.foldr (fun p acc => p + 2 ^ (W * cz) * acc) 0
    else combine W cz f (ps.take (ps.length / 2)) + 2 ^ (W * cz * (ps.length / 2)) * combine W cz f (ps.drop (ps.length / 2))

end Autoconv

namespace Autoconv

/-- `n` entries read from `P`: entry `i` is the `i`-th base-`2^K` digit of `P` minus the offset `o`. -/
def unpackK (K o : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, P => (((P % 2 ^ K : Nat) : Int) - (o : Int)) :: unpackK K o n (P / 2 ^ K)

end Autoconv
