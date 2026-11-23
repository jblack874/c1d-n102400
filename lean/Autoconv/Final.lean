import Autoconv.Bits
import Autoconv.Pack
/-!
# Certificate theorem using only a handful of big-integer operations

The heights are the base-`2^K` digits of one number `P`, minus an offset. All checks the kernel runs
are comparisons, one AND per bound, one squaring, and closed-form geometric sums.
-/
namespace Autoconv

theorem unpackK_eq (K o n P : Nat) : unpackK K o n P = (digs K n P).map (fun (d : Nat) => (d : Int) - o) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => simp [unpackK, digs, ih]

theorem evalI_replicate_cast (n B : Nat) :
    evalI (List.replicate n 1) (B : Int) = ((evalN (List.replicate n 1) B : Nat) : Int) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, evalN_cons, ih]

theorem evalI_natCast (l : List Nat) (B : Nat) :
    evalI (l.map (fun (d : Nat) => (d : Int))) (B : Int) = ((evalN l B : Nat) : Int) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [evalN_cons, ih]

theorem gdN_mem (l : List Nat) (k : Nat) (hk : k < l.length) : gdN l k ∈ l := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih => cases k with
    | zero => simp [gdN]
    | succ k => simp only [gdN]; exact List.mem_cons_of_mem _ (ih k (by simp at hk; omega))

theorem sum_le (l : List Nat) (b : Nat) (h : ∀ x ∈ l, x ≤ b) : l.sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp [Nat.succ_mul]; omega

/-- Shared setup: the digits are small, and `evalI v (2^K) = P - o · rep`. -/
theorem setup (K w n P : Nat) (hK : 1 < 2 ^ K) (hwK : w ≤ K) (hP : P < (2 ^ K) ^ n)
    (hA : P &&& (hiMask K w * rep (2 ^ K) n) = 0) :
    (∀ d ∈ digs K n P, d < 2 ^ w) ∧
    evalI (unpackK K (2 ^ (w - 1)) n P) ((2 ^ K : Nat) : Int) =
      (P : Int) - ((2 ^ (w - 1) : Nat) : Int) * ((rep (2 ^ K) n : Nat) : Int) := by
  have hev : evalN (digs K n P) (2 ^ K) = P := by rw [evalN_digs, Nat.mod_eq_of_lt (by rwa [Nat.pow_mul])]
  constructor
  · apply digits_lt_of_land _ K w hwK (digs_lt K n P)
    rw [hev, length_digs, evalN_replicate, evalN_replicate_one _ _ hK]; exact hA
  · rw [unpackK_eq]
    have e1 : (digs K n P).map (fun (d : Nat) => (d : Int) - ((2 ^ (w - 1) : Nat) : Int)) =
        ((digs K n P).map (fun (d : Nat) => (d : Int))).map (· + -((2 ^ (w - 1) : Nat) : Int)) := by
      rw [List.map_map]; apply List.map_congr_left; intro d _; simp [Int.sub_eq_add_neg]
    rw [e1, evalI_map_add, evalI_natCast, hev, List.length_map, length_digs, evalI_replicate_cast,
      evalN_replicate_one _ _ hK]
    simp [Int.sub_eq_add_neg, Int.neg_mul]


/-- The a-priori bound `n · m²` with `m = 2^(w-1)`. -/
def M0f (n w : Nat) : Nat := n * (2 ^ (w - 1) * 2 ^ (w - 1))

/-- The Kronecker number: base-`2^K` digits are `c_k + M0f` for `k < 2n-1`. -/
def Nf (K w n P : Nat) : Nat :=
  (((P : Int) - ((2 ^ (w - 1) : Nat) : Int) * ((rep (2 ^ K) n : Nat) : Int)) ^ 2 +
    ((M0f n w : Nat) : Int) * ((rep (2 ^ K) (2 * n - 1) : Nat) : Int)).toNat

theorem length_unpackK (K o n P : Nat) : (unpackK K o n P).length = n := by
  rw [unpackK_eq, List.length_map, length_digs]

theorem natAbs_unpackK_le (K w n P : Nat) (hw : 1 ≤ w) (hd : ∀ d ∈ digs K n P, d < 2 ^ w) :
    ∀ x ∈ unpackK K (2 ^ (w - 1)) n P, x.natAbs ≤ 2 ^ (w - 1) := by
  intro x hx
  rw [unpackK_eq] at hx
  obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hx
  have h1 := hd d hdm
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  omega

/-- Digits of `Nf`, as a list, with the facts the checks need. -/
theorem kron (K w n P : Nat) (hK : 1 < 2 ^ K) (hw : 1 ≤ w) (hwK : w ≤ K) (hn : 0 < n)
    (hP : P < (2 ^ K) ^ n) (hA : P &&& (hiMask K w * rep (2 ^ K) n) = 0)
    (hM0 : 2 * M0f n w < 2 ^ K) :
    let v := unpackK K (2 ^ (w - 1)) n P
    let dN := ((mulL v v).map (· + ((M0f n w : Nat) : Int))).map Int.toNat
    dN.length = 2 * n - 1 ∧ (∀ d ∈ dN, d ≤ 2 * M0f n w) ∧ evalN dN (2 ^ K) = Nf K w n P ∧
    ∀ k < 2 * n - 1, (gdN dN k : Int) = conv v v k + M0f n w := by
  intro v dN
  obtain ⟨hdl, hev⟩ := setup K w n P hK hwK hP hA
  have hlen : v.length = n := length_unpackK _ _ _ _
  have hv : v ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  have hm : ∀ x ∈ v, x.natAbs ≤ 2 ^ (w - 1) := natAbs_unpackK_le K w n P hw hdl
  have hL : (mulL v v).length = 2 * n - 1 := by rw [length_mulL v v hv hv, hlen]; omega
  have hbd : ∀ j, (gd (mulL v v) j).natAbs ≤ M0f n w := by
    intro j; have := natAbs_gd_mulL_le v v _ _ hm hm j; rw [hlen] at this; exact this
  have hmem : ∀ x ∈ mulL v v, x.natAbs ≤ M0f n w := by
    intro x hx; obtain ⟨j, hj⟩ := mem_gd _ x hx; rw [← hj]; exact hbd j
  have he0 : ∀ y ∈ (mulL v v).map (· + ((M0f n w : Nat) : Int)), 0 ≤ y := by
    intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; have := hmem x hx; omega
  refine ⟨by simp [dN, hL], ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    have := hmem x hx; omega
  · have hc := evalN_cast _ (2 ^ K) he0
    unfold Nf
    rw [← hev, Int.pow_succ, Int.pow_one, ← evalI_mulL]
    have : evalI ((mulL v v).map (· + ((M0f n w : Nat) : Int))) ((2 ^ K : Nat) : Int) =
        evalI (mulL v v) ((2 ^ K : Nat) : Int) + ((M0f n w : Nat) : Int) * ((rep (2 ^ K) (2 * n - 1) : Nat) : Int) := by
      rw [evalI_map_add, hL, evalI_replicate_cast, evalN_replicate_one _ _ hK]
    rw [← this, ← hc, Int.toNat_natCast]
  · intro k hk
    have hk' : k < (mulL v v).length := by omega
    simp only [dN, gdN_map_toNat, gd_map_add _ _ _ hk', gd_mulL]
    have := hbd k; rw [gd_mulL] at this
    rw [Int.toNat_of_nonneg (by omega)]

/-- **Main bound.** Two AND checks give `|c_k| ≤ M` for every `k`. -/
theorem final_bound (K w n P t M : Nat) (hK : 1 < 2 ^ K) (hw : 1 ≤ w) (hwK : w ≤ K) (htK : t ≤ K)
    (hn : 0 < n) (hP : P < (2 ^ K) ^ n) (hA : P &&& (hiMask K w * rep (2 ^ K) n) = 0)
    (hU : M0f n w + M < 2 ^ t)
    (hC : 2 * M0f n w + (2 ^ t - 1 - (M0f n w + M)) < 2 ^ K)
    (h1 : (Nf K w n P + (2 ^ t - 1 - (M0f n w + M)) * rep (2 ^ K) (2 * n - 1)) &&&
      (hiMask K t * rep (2 ^ K) (2 * n - 1)) = 0)
    (h2 : (2 * M0f n w * rep (2 ^ K) (2 * n - 1) - Nf K w n P + (2 ^ t - 1 - (M0f n w + M)) * rep (2 ^ K) (2 * n - 1)) &&&
      (hiMask K t * rep (2 ^ K) (2 * n - 1)) = 0) :
    ∀ k, (conv (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P) k).natAbs ≤ M := by
  have hM0 : 2 * M0f n w < 2 ^ K := by omega
  obtain ⟨hlen, hle, hev, hdig⟩ := kron K w n P hK hw hwK hn hP hA hM0
  generalize hc1 : 2 ^ t - 1 - (M0f n w + M) = c1 at hC h1 h2
  generalize hdN : (((mulL (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P)).map
    (· + ((M0f n w : Nat) : Int))).map Int.toNat) = dN at hlen hle hev hdig
  -- upper check
  have up : ∀ d ∈ dN, d + c1 < 2 ^ t := by
    have hl : ∀ x ∈ dN.map (· + c1), x < 2 ^ K := by
      intro x hx; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx; have := hle d hd; omega
    have := digits_lt_of_land _ K t htK hl (by
      rw [evalN_map_add, evalN_replicate_one _ _ hK, List.length_map, evalN_replicate, evalN_replicate_one _ _ hK,
        hlen, hev]; exact h1)
    intro d hd; exact this _ (List.mem_map_of_mem hd)
  -- lower check
  have lo : ∀ d ∈ dN, 2 * M0f n w - d + c1 < 2 ^ t := by
    have hs := evalN_map_sub dN (2 * M0f n w) (2 ^ K) hle
    rw [evalN_replicate_one _ _ hK, hlen, hev] at hs
    have hl : ∀ x ∈ (dN.map (2 * M0f n w - ·)).map (· + c1), x < 2 ^ K := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
      omega
    have := digits_lt_of_land _ K t htK hl (by
      rw [evalN_map_add, evalN_replicate_one _ _ hK, List.length_map, List.length_map, evalN_replicate,
        evalN_replicate_one _ _ hK, hlen]
      have : evalN (dN.map (2 * M0f n w - ·)) (2 ^ K) = 2 * M0f n w * rep (2 ^ K) (2 * n - 1) - Nf K w n P := by
        omega
      simp only [List.length_map, hlen]
      rw [this]; exact h2)
    intro d hd; exact this _ (List.mem_map_of_mem (List.mem_map_of_mem hd))
  intro k
  by_cases hk : k < 2 * n - 1
  · have hmem := gdN_mem dN k (by omega)
    have u := up _ hmem
    have l := lo _ hmem
    have e := hdig k hk
    omega
  · have hv : (unpackK K (2 ^ (w - 1)) n P) ≠ [] := by
      intro h; have := length_unpackK K (2 ^ (w - 1)) n P; rw [h] at this; simp at this; omega
    rw [← gd_mulL, gd_of_length_le]; · simp
    rw [length_mulL _ _ hv hv, length_unpackK]; omega

/-- The coefficient at `k` is one digit of `Nf`. -/
theorem final_digit (K w n P : Nat) (hK : 1 < 2 ^ K) (hw : 1 ≤ w) (hwK : w ≤ K) (hn : 0 < n)
    (hP : P < (2 ^ K) ^ n) (hA : P &&& (hiMask K w * rep (2 ^ K) n) = 0)
    (hM0 : 2 * M0f n w < 2 ^ K) (k : Nat) (hk : k < 2 * n - 1) :
    conv (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P) k =
      ((Nf K w n P >>> (K * k) % 2 ^ K : Nat) : Int) - M0f n w := by
  obtain ⟨hlen, hle, hev, hdig⟩ := kron K w n P hK hw hwK hn hP hA hM0
  have hlt : ∀ x ∈ (((mulL (unpackK K (2 ^ (w - 1)) n P) (unpackK K (2 ^ (w - 1)) n P)).map
      (· + ((M0f n w : Nat) : Int))).map Int.toNat), x < 2 ^ K := by
    intro x hx; have := hle x hx; omega
  rw [Nat.shiftRight_eq_div_pow, ← hev, Nat.pow_mul, evalN_digit _ _ (by omega) hlt, hdig k hk]; omega

theorem sum_map_sub (l : List Nat) (o : Int) :
    (l.map (fun (d : Nat) => (d : Int) - o)).sum = (l.sum : Int) - o * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Int.mul_add]; omega

/-- The sum of the entries, from one remainder. -/
theorem final_sum (K w n P : Nat) (hK : 1 < 2 ^ K) (hwK : w ≤ K) (hP : P < (2 ^ K) ^ n)
    (hA : P &&& (hiMask K w * rep (2 ^ K) n) = 0) (hS : n * 2 ^ w < 2 ^ K - 1) :
    (unpackK K (2 ^ (w - 1)) n P).sum = ((P % (2 ^ K - 1) : Nat) : Int) - ((2 ^ (w - 1) : Nat) : Int) * n := by
  obtain ⟨hdl, _⟩ := setup K w n P hK hwK hP hA
  have hev : evalN (digs K n P) (2 ^ K) = P := by rw [evalN_digs, Nat.mod_eq_of_lt (by rwa [Nat.pow_mul])]
  have hsum : (digs K n P).sum ≤ n * 2 ^ w := by
    have := sum_le (digs K n P) (2 ^ w) (fun d hd => Nat.le_of_lt (hdl d hd)); rwa [length_digs] at this
  have hmod := evalN_mod_sum (digs K n P) (2 ^ K) (by omega)
  rw [hev, Nat.mod_eq_of_lt (by omega : (digs K n P).sum < 2 ^ K - 1)] at hmod
  rw [unpackK_eq, sum_map_sub, length_digs, hmod]

end Autoconv
