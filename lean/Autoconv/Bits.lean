import Autoconv.Check
/-!
# Whole-number digit checks with one bitwise AND

For `B = 2^K`: if `X = Σ x_i B^i` with every `x_i < B`, then `X &&& (h · Σ_{i<n} B^i) = 0`, where `h` has bits
`w … K-1` set, says every `x_i < 2^w`. The kernel does this with one big-integer AND.
-/
namespace Autoconv

/-- `Σ_{i<n} B^i`, computed in closed form. -/
def rep (B n : Nat) : Nat := (B ^ n - 1) / (B - 1)

theorem evalN_nil (B : Nat) : evalN [] B = 0 := rfl
theorem evalN_cons (x : Nat) (l : List Nat) (B : Nat) : evalN (x :: l) B = x + B * evalN l B := rfl

theorem evalN_replicate_one (B n : Nat) (hB : 1 < B) : evalN (List.replicate n 1) B = rep B n := by
  have key : (B - 1) * evalN (List.replicate n 1) B = B ^ n - 1 := by
    induction n with
    | zero => simp [evalN_nil]
    | succ n ih =>
      rw [List.replicate_succ, evalN_cons, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, ih, Nat.pow_succ]
      have h1 : 1 ≤ B ^ n := Nat.one_le_pow _ _ (by omega)
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm B (B ^ n)]
      have : B ≤ B ^ n * B := Nat.le_mul_of_pos_left B h1
      omega
  unfold rep; rw [← key, Nat.mul_div_cancel_left _ (by omega)]

theorem evalN_replicate (B n c : Nat) : evalN (List.replicate n c) B = c * evalN (List.replicate n 1) B := by
  induction n with
  | zero => simp [evalN_nil]
  | succ n ih => rw [List.replicate_succ, List.replicate_succ, evalN_cons, evalN_cons, ih]; simp [Nat.mul_add, Nat.mul_left_comm]

theorem evalN_map_add (l : List Nat) (c B : Nat) :
    evalN (l.map (· + c)) B = evalN l B + c * evalN (List.replicate l.length 1) B := by
  induction l with
  | nil => simp [evalN_nil]
  | cons x xs ih =>
    simp only [List.map_cons, evalN_cons, ih, List.length_cons, List.replicate_succ, Nat.mul_add, Nat.mul_one]
    simp only [Nat.mul_left_comm c B]; omega

theorem evalN_map_sub (l : List Nat) (C B : Nat) (h : ∀ x ∈ l, x ≤ C) :
    evalN (l.map (C - ·)) B + evalN l B = C * evalN (List.replicate l.length 1) B := by
  induction l with
  | nil => simp [evalN_nil]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, evalN_cons, List.length_cons, List.replicate_succ, Nat.mul_add, Nat.mul_one]
    have e : B * evalN (xs.map (C - ·)) B + B * evalN xs B = C * (B * evalN (List.replicate xs.length 1) B) := by
      rw [← Nat.mul_add, ih', Nat.mul_left_comm]
    omega

/-- Low bits of `a + 2^K b` are those of `a`; high bits are those of `b`. -/
theorem testBit_split (a b K j : Nat) (ha : a < 2 ^ K) :
    (a + 2 ^ K * b).testBit j = if j < K then a.testBit j else b.testBit (j - K) := by
  rw [Nat.add_comm]; exact Nat.testBit_two_pow_mul_add b ha j

theorem land_split (a b c d K : Nat) (ha : a < 2 ^ K) (hc : c < 2 ^ K)
    (h : (a + 2 ^ K * b) &&& (c + 2 ^ K * d) = 0) : a &&& c = 0 ∧ b &&& d = 0 := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro j
    have := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_and, testBit_split _ _ _ _ ha, testBit_split _ _ _ _ hc, Nat.zero_testBit] at this ⊢
    by_cases hj : j < K
    · simpa [hj] using this
    · have h1 : a.testBit j = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h1]
  · apply Nat.eq_of_testBit_eq; intro j
    have := congrArg (fun x => x.testBit (j + K)) h
    have hjk : ¬ (j + K < K) := by omega
    simp only [Nat.testBit_and, testBit_split _ _ _ _ ha, testBit_split _ _ _ _ hc, Nat.zero_testBit, hjk,
      if_false, Nat.add_sub_cancel] at this ⊢
    exact this

/-- Bits `w … K-1`. -/
def hiMask (K w : Nat) : Nat := (2 ^ (K - w) - 1) * 2 ^ w

theorem hiMask_lt (K w : Nat) (hw : w ≤ K) : hiMask K w < 2 ^ K := by
  unfold hiMask
  have h1 : 2 ^ K = 2 ^ (K - w) * 2 ^ w := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  have h3 : 0 < 2 ^ (K - w) := Nat.two_pow_pos _
  have h4 : 2 ^ w ≤ 2 ^ (K - w) * 2 ^ w := Nat.le_mul_of_pos_left _ h3
  rw [h1, Nat.sub_mul, Nat.one_mul]; omega

theorem lt_of_land_hiMask (x K w : Nat) (hw : w ≤ K) (hx : x < 2 ^ K) (h : x &&& hiMask K w = 0) : x < 2 ^ w := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  by_cases hjK : j < K
  · have := congrArg (fun y => y.testBit j) h
    simp only [Nat.testBit_and, Nat.zero_testBit, hiMask, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one] at this
    have hj' : w ≤ j := hj
    simp only [hj', decide_true, Bool.true_and] at this
    have : j - w < K - w := by omega
    simp_all
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))

/-- The AND check on a digit list. -/
theorem digits_lt_of_land (l : List Nat) (K w : Nat) (hw : w ≤ K) (hl : ∀ x ∈ l, x < 2 ^ K)
    (h : evalN l (2 ^ K) &&& evalN (List.replicate l.length (hiMask K w)) (2 ^ K) = 0) :
    ∀ x ∈ l, x < 2 ^ w := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    have hx := hl x (by simp)
    rw [List.length_cons, List.replicate_succ, evalN_cons, evalN_cons] at h
    have ⟨h1, h2⟩ := land_split _ _ _ _ K hx (hiMask_lt K w hw) h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lt_of_land_hiMask _ K w hw hx h1
    · exact ih (fun z hz => hl z (by simp [hz])) h2 y hy

/-! ## Reading the digits of a natural number -/

/-- The first `n` base-`2^K` digits of `P`. -/
def digs (K : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, P => (P % 2 ^ K) :: digs K n (P / 2 ^ K)

theorem length_digs (K n P : Nat) : (digs K n P).length = n := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => simp [digs, ih]

theorem digs_lt (K n P : Nat) : ∀ x ∈ digs K n P, x < 2 ^ K := by
  induction n generalizing P with
  | zero => simp [digs]
  | succ n ih =>
    intro x hx; simp only [digs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (Nat.two_pow_pos K)
    · exact ih _ x hx

theorem evalN_digs (K n P : Nat) : evalN (digs K n P) (2 ^ K) = P % 2 ^ (K * n) := by
  induction n generalizing P with
  | zero => simp [digs, evalN_nil, Nat.mod_one]
  | succ n ih =>
    rw [digs, evalN_cons, ih, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (K * n)) (2 ^ K), Nat.mod_mul]

theorem evalN_mod_sum (l : List Nat) (B : Nat) (hB : 1 ≤ B) : evalN l B % (B - 1) = l.sum % (B - 1) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [evalN_cons, List.sum_cons]
    have e : x + B * evalN xs B = (x + evalN xs B) + (B - 1) * evalN xs B := by
      rw [Nat.sub_mul, Nat.one_mul]
      have : evalN xs B ≤ B * evalN xs B := Nat.le_mul_of_pos_left _ hB
      omega
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mod, ih, ← Nat.add_mod]

end Autoconv
