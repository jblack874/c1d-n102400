import Autoconv.Basic
/-!
# Kronecker substitution, with proofs

The bridge from the definition `conv` to one big-integer multiplication, and a divide-and-conquer digit check.
-/
namespace Autoconv

/-- Coefficientwise sum of two coefficient lists. -/
def addL : List Int → List Int → List Int
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

/-- Schoolbook product of coefficient lists. -/
def mulL : List Int → List Int → List Int
  | [], _ => []
  | a :: as, b => addL (b.map (a * ·)) (0 :: mulL as b)

@[simp] theorem gd_nil (k : Nat) : gd [] k = 0 := by cases k <;> rfl
@[simp] theorem gd_cons_zero (x : Int) (xs : List Int) : gd (x :: xs) 0 = x := rfl
@[simp] theorem gd_cons_succ (x : Int) (xs : List Int) (k : Nat) : gd (x :: xs) (k + 1) = gd xs k := rfl

theorem gd_addL (xs ys : List Int) (k : Nat) : gd (addL xs ys) k = gd xs k + gd ys k := by
  induction xs generalizing ys k with
  | nil => simp [addL]
  | cons x xs ih =>
    cases ys with
    | nil => cases k <;> simp [addL]
    | cons y ys => cases k <;> simp [addL, ih]

theorem gd_map_mul (a : Int) (b : List Int) (k : Nat) : gd (b.map (a * ·)) k = a * gd b k := by
  induction b generalizing k with
  | nil => simp
  | cons y ys ih => cases k <;> simp [ih]

theorem sum_map_zero (l : List Nat) : (l.map fun _ => (0 : Int)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons i is ih => simp [ih]

theorem conv_nil (b : List Int) (k : Nat) : conv [] b k = 0 := by
  simp [conv, sum_map_zero]

theorem conv_cons_zero (a : Int) (as b : List Int) : conv (a :: as) b 0 = a * gd b 0 := by
  simp [conv]

theorem conv_cons_succ (a : Int) (as b : List Int) (k : Nat) :
    conv (a :: as) b (k + 1) = a * gd b (k + 1) + conv as b k := by
  unfold conv
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.sum_cons]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_sub_add_right]

theorem gd_mulL (a b : List Int) (k : Nat) : gd (mulL a b) k = conv a b k := by
  induction a generalizing k with
  | nil => simp [mulL, conv_nil]
  | cons x xs ih =>
    cases k with
    | zero => simp [mulL, gd_addL, gd_map_mul, conv_cons_zero]
    | succ k => simp [mulL, gd_addL, gd_map_mul, conv_cons_succ, ih]

/-- Evaluation of a coefficient list at `B` (Horner). -/
def evalI (l : List Int) (B : Int) : Int := l.foldr (fun x acc => x + B * acc) 0

@[simp] theorem evalI_nil (B : Int) : evalI [] B = 0 := rfl
@[simp] theorem evalI_cons (x : Int) (l : List Int) (B : Int) : evalI (x :: l) B = x + B * evalI l B := rfl

theorem evalI_addL (xs ys : List Int) (B : Int) : evalI (addL xs ys) B = evalI xs B + evalI ys B := by
  induction xs generalizing ys with
  | nil => simp [addL]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addL]
    | cons y ys => simp [addL, ih, Int.mul_add]; omega

theorem evalI_map_mul (a : Int) (b : List Int) (B : Int) : evalI (b.map (a * ·)) B = a * evalI b B := by
  induction b with
  | nil => simp
  | cons y ys ih => simp [ih, Int.mul_add, Int.mul_left_comm]

theorem evalI_mulL (a b : List Int) (B : Int) : evalI (mulL a b) B = evalI a B * evalI b B := by
  induction a with
  | nil => simp [mulL]
  | cons x xs ih => simp [mulL, evalI_addL, evalI_map_mul, ih, Int.add_mul, Int.mul_assoc]

theorem evalI_append (l₁ l₂ : List Int) (B : Int) :
    evalI (l₁ ++ l₂) B = evalI l₁ B + B ^ l₁.length * evalI l₂ B := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih, Int.pow_succ, Int.mul_add, Int.add_assoc, Int.mul_comm, Int.mul_left_comm]

end Autoconv
