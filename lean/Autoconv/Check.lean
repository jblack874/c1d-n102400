import Autoconv.Kronecker
/-!
# From one big-integer computation to a bound on every convolution coefficient
-/
namespace Autoconv

/-! ## Lengths -/

theorem length_addL (xs ys : List Int) : (addL xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [addL]
  | cons x xs ih => cases ys with
    | nil => simp [addL]
    | cons y ys => simp [addL, ih, Nat.succ_max_succ]

theorem length_mulL (a b : List Int) (ha : a ≠ []) (hb : b ≠ []) :
    (mulL a b).length = a.length + b.length - 1 := by
  induction a with
  | nil => exact absurd rfl ha
  | cons x xs ih =>
    have hbl : 0 < b.length := List.length_pos_iff.mpr hb
    cases xs with
    | nil => simp [mulL, length_addL]; omega
    | cons y ys =>
      have := ih (by simp)
      simp only [mulL, length_addL, List.length_map, List.length_cons] at this ⊢
      omega

theorem gd_of_length_le (l : List Int) (k : Nat) (h : l.length ≤ k) : gd l k = 0 := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih => cases k with
    | zero => simp at h
    | succ k => simp only [gd_cons_succ]; exact ih k (by simp at h; omega)

/-! ## A crude a-priori bound on the coefficients -/

theorem natAbs_gd_le (l : List Int) (m : Nat) (h : ∀ x ∈ l, x.natAbs ≤ m) (k : Nat) :
    (gd l k).natAbs ≤ m := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih => cases k with
    | zero => simpa using h x (by simp)
    | succ k => simpa using ih (fun y hy => h y (by simp [hy])) k

theorem natAbs_gd_mulL_le (a b : List Int) (A Bd : Nat) (ha : ∀ x ∈ a, x.natAbs ≤ A)
    (hb : ∀ y ∈ b, y.natAbs ≤ Bd) (k : Nat) : (gd (mulL a b) k).natAbs ≤ a.length * (A * Bd) := by
  induction a generalizing k with
  | nil => simp [mulL]
  | cons x xs ih =>
    have hx : x.natAbs ≤ A := ha x (by simp)
    have ih' := ih (fun y hy => ha y (by simp [hy]))
    have h1 : (x * gd b k).natAbs ≤ A * Bd := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul hx (natAbs_gd_le b Bd hb k)
    have h2 : (gd (0 :: mulL xs b) k).natAbs ≤ xs.length * (A * Bd) := by
      cases k with
      | zero => simp
      | succ k => simpa using ih' k
    simp only [mulL, gd_addL, gd_map_mul, List.length_cons]
    have := Int.natAbs_add_le (x * gd b k) (gd (0 :: mulL xs b) k)
    rw [Nat.succ_mul]; omega

theorem mem_gd (l : List Int) (x : Int) (h : x ∈ l) : ∃ k, gd l k = x := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨k, hk⟩ := ih h; exact ⟨k + 1, by simpa using hk⟩

/-! ## Offsetting the coefficients -/

theorem evalI_map_add (l : List Int) (t B : Int) :
    evalI (l.map (· + t)) B = evalI l B + t * evalI (List.replicate l.length 1) B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, evalI_cons, ih, List.length_cons, List.replicate_succ]
    simp only [Int.mul_add, Int.mul_one, Int.add_assoc, Int.mul_left_comm t B]
    omega

/-! ## Base-`B` digits of natural numbers -/

/-- Evaluation of a list of natural-number digits at `B`. -/
def evalN (l : List Nat) (B : Nat) : Nat := l.foldr (fun x acc => x + B * acc) 0

/-- `i`-th entry, `0` past the end. -/
def gdN : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => gdN xs k

theorem evalN_digit (d : List Nat) (B : Nat) (hB : 0 < B) (hd : ∀ x ∈ d, x < B) (k : Nat) :
    evalN d B / B ^ k % B = gdN d k := by
  induction d generalizing k with
  | nil => simp [evalN, gdN]
  | cons x xs ih =>
    have hx : x < B := hd x (by simp)
    have ih' := ih (fun y hy => hd y (by simp [hy]))
    have hdiv : (x + B * evalN xs B) / B = evalN xs B := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx, Nat.zero_add]
    cases k with
    | zero =>
      simp only [evalN, List.foldr_cons, Nat.pow_zero, Nat.div_one, gdN] at *
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ k =>
      simp only [gdN]
      rw [← ih' k, Nat.pow_succ, Nat.mul_comm (B ^ k) B, ← Nat.div_div_eq_div_mul]
      simp only [evalN, List.foldr_cons] at hdiv ⊢
      rw [hdiv]

theorem evalN_cast (l : List Int) (B : Nat) (h : ∀ x ∈ l, 0 ≤ x) :
    ((evalN (l.map Int.toNat) B : Nat) : Int) = evalI l (B : Int) := by
  induction l with
  | nil => simp [evalN]
  | cons x xs ih =>
    have hx : 0 ≤ x := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [evalN, List.map_cons, List.foldr_cons] at ih' ⊢
    rw [Int.natCast_add, Int.natCast_mul, ih', Int.toNat_of_nonneg hx, evalI_cons]

theorem gdN_map_toNat (l : List Int) (k : Nat) : gdN (l.map Int.toNat) k = (gd l k).toNat := by
  induction l generalizing k with
  | nil => cases k <;> simp [gdN]
  | cons x xs ih => cases k <;> simp [gdN, ih]

theorem gd_map_add (l : List Int) (t : Int) (k : Nat) (hk : k < l.length) :
    gd (l.map (· + t)) k = gd l k + t := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih => cases k with
    | zero => simp
    | succ k => simp only [List.map_cons, gd_cons_succ]; exact ih k (by simp at hk; omega)

/-! ## Divide-and-conquer digit check -/

/-- `chk B lo hi f N len`: every base-`B` digit `k < len` of `N` lies in `[lo, hi]`. -/
def chk (B lo hi : Nat) : Nat → Nat → Nat → Bool
  | 0, N, len => (List.range len).all fun k => lo ≤ N / B ^ k % B && N / B ^ k % B ≤ hi
  | f + 1, N, len =>
    if len ≤ 1 then (len == 0 || (lo ≤ N % B && N % B ≤ hi))
    else chk B lo hi f (N % B ^ (len / 2)) (len / 2) && chk B lo hi f (N / B ^ (len / 2)) (len - len / 2)

theorem chk_sound (B lo hi : Nat) (hB : 0 < B) (f N len : Nat) (h : chk B lo hi f N len = true)
    (k : Nat) (hk : k < len) : lo ≤ N / B ^ k % B ∧ N / B ^ k % B ≤ hi := by
  induction f generalizing N len k with
  | zero =>
    simp only [chk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h k hk
  | succ f ih =>
    unfold chk at h
    split at h
    · have hk0 : k = 0 := by omega
      subst hk0
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · omega
      · simpa using h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      by_cases hkh : k < len / 2
      · have := ih _ _ h1 k hkh
        have hpow : B ^ (len / 2) = B ^ k * B ^ (len / 2 - k) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hdvd : B ∣ B ^ (len / 2 - k) := by
          have he : len / 2 - k = (len / 2 - k - 1) + 1 := by omega
          rw [he, Nat.pow_succ]; exact Nat.dvd_mul_left B _
        rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd] at this
        exact this
      · have := ih _ _ h2 (k - len / 2) (by omega)
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
        exact this

/-! ## Divide-and-conquer evaluation -/

/-- Same value as `evalI l B`, computed by splitting the list in halves (fast on big integers). -/
def evalFast : Nat → List Int → Int → Int
  | 0, l, B => evalI l B
  | f + 1, l, B =>
    if l.length ≤ 1 then evalI l B
    else evalFast f (l.take (l.length / 2)) B + B ^ (l.length / 2) * evalFast f (l.drop (l.length / 2)) B

theorem evalFast_eq (f : Nat) (l : List Int) (B : Int) : evalFast f l B = evalI l B := by
  induction f generalizing l with
  | zero => rfl
  | succ f ih =>
    unfold evalFast
    split
    · rfl
    · rw [ih, ih]
      conv => rhs; rw [← List.take_append_drop (l.length / 2) l]
      rw [evalI_append, List.length_take, Nat.min_eq_left (by omega)]

end Autoconv
