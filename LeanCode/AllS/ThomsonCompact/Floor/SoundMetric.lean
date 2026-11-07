import ThomsonCompact.Floor.Check
import AllS.Units.N_AI.N_gram_replay.LiteralGramSupport
import AllS.Units.N_AI.N_correction_bounds.N_weighted_quadratic

/-!
# Soundness of the short-metric, total and gap checks (F3a)

* `short_metric_sound`: `checkTheta … = true` gives the `Active12.short_metric` field for
  `Z = Zi 2^-32` (the decoded short metric) and `θ = claim 2^-(32+mb)`, for any literal block whose metric
  data are the checked lists.
* `total_sound`, `gap_sound`: `checkTotal … = true` gives `Active12.total` and `Active12.gap`.
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.Floor

open Blueprint.CAP

/-! ## Finite sums and maxima of the kernel -/

theorem sumZ_eq (n : ℕ) (f : ℕ → ℤ) : sumZ n f = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem sumN_eq (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

theorem le_maxN (n : ℕ) (f : ℕ → ℕ) : ∀ j < n, f j ≤ maxN n f := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    show f j ≤ Nat.max (maxN n f) (f n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact (ih j h).trans (Nat.le_max_left _ _)
    · subst h; exact Nat.le_max_right _ _

/-! ## A quadratic bound from absolute row sums -/

theorem quadraticBound_of_rows {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ)
    (hsym : ∀ i j, S i j = S j i) (hθ : 0 ≤ θ) (hrow : ∀ i, ∑ j, |S i j| ≤ θ) :
    QuadraticBound S θ := by
  apply correction_bounds_weighted_quadratic S (fun i j => |S i j|) (fun _ => 1) θ hsym
  · intro i j; rw [hsym i j]
  · intro i j; exact abs_nonneg _
  · intro i j; exact le_rfl
  · intro _; exact one_pos
  · exact hθ
  · intro i; simpa using hrow i

/-! ## The literal metric in integer form -/

theorem literalMetric_eq (X : Literals.Block) (bits mb : ℕ) (ex kl : List ℤ)
    (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl) (hmb : bits ≤ mb)
    (hpos : ∀ i < X.order, 0 ≤ (mb : ℤ) + ex.getD i 0) (i j : Fin X.order) :
    literalMetric X bits i j = (kzent bits mb ex kl i j : ℝ) / 2 ^ mb := by
  have h2 : (0 : ℝ) < 2 ^ mb := by positivity
  unfold literalMetric kzent
  rw [hex, hkl]
  by_cases hji : j < i
  · have hji' : j.val < i.val := hji
    simp only [hji, hji', if_true]
    push_cast
    rw [show (2 : ℝ) ^ mb = 2 ^ (mb - bits) * 2 ^ bits by rw [← pow_add]; congr 1; omega]
    field_simp
  · have hji' : ¬ j.val < i.val := hji
    simp only [hji, hji', if_false]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have hp := hpos i.val i.isLt
      have ht : ((Int.toNat ((mb : ℤ) + ex.getD i.val 0) : ℕ) : ℤ) = (mb : ℤ) + ex.getD i.val 0 :=
        Int.toNat_of_nonneg hp
      push_cast
      rw [eq_div_iff h2.ne', ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ht]
      congr 1
      ring
    · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp only [hij, hij', if_false]
      simp

/-! ## Short metric -/

/-- The decoded short metric `Z = Zi 2^-32` as a real matrix. -/
def zReal (nb wz : ℕ) (zrows : List ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (zent (zMatrix nb wz zrows) i j : ℝ) / 2 ^ 32

theorem nat_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem checkTheta_parts {nb wz bits mb : ℕ} {zrows : List ℕ} {ex kl : List ℤ} {claim : ℕ}
    (h : checkTheta nb wz bits mb zrows ex kl claim = true) :
    thetaNum (zMatrix nb wz zrows) nb bits mb ex kl (32 + mb) ≤ claim ∧ bits ≤ mb ∧
      (∀ i < nb, 0 ≤ (mb : ℤ) + ex.getD i 0) := by
  unfold checkTheta at h
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, decide_eq_true_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩ := h
  refine ⟨by simpa [Nat.add_comm] using h1, h2, ?_⟩
  intro i hi
  have hi' : i < ex.length := by omega
  rw [List.getD_eq_getElem _ _ hi']
  exact h3 _ (List.getElem_mem hi')

/-- **Short metric.** `θ = claim 2^-(32+mb)` bounds `(Z K - 1) + (Z K - 1)ᵀ` for `Z = Zi 2^-32`. -/
theorem short_metric_sound (X : Literals.Block) (nb wz bits mb : ℕ) (zrows : List ℕ) (ex kl : List ℤ)
    (claim : ℕ) (hX : X.order = nb) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (h : checkTheta nb wz bits mb zrows ex kl claim = true) :
    QuadraticBound ((zReal nb wz zrows X.order * literalMetric X bits - 1) +
        (zReal nb wz zrows X.order * literalMetric X bits - 1).transpose) ((claim : ℝ) / 2 ^ (32 + mb)) := by
  obtain ⟨hth, hmb, hpos⟩ := checkTheta_parts h
  subst hX
  set Z := zMatrix X.order wz zrows
  set sc := 32 + mb
  have hsc : (0 : ℝ) < 2 ^ sc := by positivity
  -- entries of Z K - 1
  have hF : ∀ i j : Fin X.order,
      ((zReal X.order wz zrows X.order * literalMetric X bits - 1) i j) =
        (fent Z X.order bits mb ex kl sc i j : ℝ) / 2 ^ sc := by
    intro i j
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]
    simp only [zReal, Matrix.of_apply]
    simp only [literalMetric_eq X bits mb ex kl hex hkl hmb hpos _ j]
    unfold fent
    rw [sumZ_eq]
    push_cast
    rw [show sc = 32 + mb from rfl, pow_add]
    have hsum : ∑ l : Fin X.order, (zent Z i l : ℝ) / 2 ^ 32 * ((kzent bits mb ex kl l j : ℝ) / 2 ^ mb) =
        (∑ l ∈ Finset.range X.order, ((zent Z i l : ℝ) * (kzent bits mb ex kl l j : ℝ))) / (2 ^ 32 * 2 ^ mb) := by
      rw [Finset.sum_div]
      rw [← Fin.sum_univ_eq_sum_range (fun l => (zent Z i l : ℝ) * (kzent bits mb ex kl l j : ℝ) / (2 ^ 32 * 2 ^ mb))]
      apply Finset.sum_congr rfl
      intro l _
      field_simp
    rw [hsum]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      field_simp
    · have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp only [hij, hij', if_false, sub_zero]
  apply quadraticBound_of_rows
  · intro i j
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    ring
  · positivity
  · intro i
    have hrow : ∑ j : Fin X.order, |((zReal X.order wz zrows X.order * literalMetric X bits - 1) +
        (zReal X.order wz zrows X.order * literalMetric X bits - 1).transpose) i j| =
        ((sumN X.order fun j => (fent Z X.order bits mb ex kl sc i j + fent Z X.order bits mb ex kl sc j i).natAbs : ℕ) : ℝ) /
          2 ^ sc := by
      rw [sumN_eq]
      push_cast
      rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.add_apply, Matrix.transpose_apply, hF, hF]
      rw [← add_div, abs_div, abs_of_pos hsc]
      congr 1
      rw [Nat.cast_natAbs]
      push_cast
      rfl
    rw [hrow]
    apply div_le_div_of_nonneg_right _ hsc.le
    have hm : (sumN X.order fun j => (fent Z X.order bits mb ex kl sc i j +
        fent Z X.order bits mb ex kl sc j i).natAbs) ≤ thetaNum Z X.order bits mb ex kl sc :=
      le_maxN X.order (fun i => sumN X.order fun j => (fent Z X.order bits mb ex kl sc i j +
        fent Z X.order bits mb ex kl sc j i).natAbs) i.val i.isLt
    exact_mod_cast hm.trans hth

/-! ## Total and gap -/

theorem foldl_add_range (f : ℕ → ℕ) : ∀ (n a : ℕ),
    ((List.range n).map f).foldl Nat.add a = a + ∑ k ∈ Finset.range n, f k := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [List.range_succ, List.map_append, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    show a + ∑ k ∈ Finset.range n, f k + f n = a + (∑ k ∈ Finset.range n, f k + f n)
    ring

theorem checkTotal_parts {n eta gamma theta sc E : ℕ} {f : ℕ → ℕ}
    (h : checkTotal ((List.range n).map f) eta gamma theta sc E = true) :
    (∑ k ∈ Finset.range n, f k) + eta ≤ gamma ∧ gamma * 2 ^ (sc + E) < (2 ^ sc - theta) * 2 ^ YSC ∧
      theta < 2 ^ sc := by
  unfold checkTotal at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [foldl_add_range, Nat.zero_add] at h1
  simp only [nat_shiftLeft, Nat.one_mul] at h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Total.** `Σ_k γ_k + η ≤ γ` with `γ_k = f k 2^-YSC`, `η = eta 2^-YSC`, `γ = gamma 2^-YSC`. -/
theorem total_sound {n eta gamma theta sc E : ℕ} {f : ℕ → ℕ}
    (h : checkTotal ((List.range n).map f) eta gamma theta sc E = true) :
    ∑ k : Fin n, ((f k : ℝ) / 2 ^ YSC) + (eta : ℝ) / 2 ^ YSC ≤ (gamma : ℝ) / 2 ^ YSC := by
  obtain ⟨h1, -, -⟩ := checkTotal_parts h
  rw [← Finset.sum_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Fin.sum_univ_eq_sum_range (fun k => (f k : ℝ))]
  exact_mod_cast h1

/-- **Gap.** `γ < 2^(-E) (1 - θ)` with `θ = theta 2^-sc`. -/
theorem gap_sound {n eta gamma theta sc E : ℕ} {f : ℕ → ℕ}
    (h : checkTotal ((List.range n).map f) eta gamma theta sc E = true) :
    (gamma : ℝ) / 2 ^ YSC < (2 : ℝ) ^ (-(E : ℤ)) * (1 - (theta : ℝ) / 2 ^ sc) := by
  obtain ⟨-, h2, h3⟩ := checkTotal_parts h
  have hsub : ((2 ^ sc - theta : ℕ) : ℝ) = (2 : ℝ) ^ sc - theta := by
    rw [Nat.cast_sub h3.le]; push_cast; ring
  have h2' : (gamma : ℝ) * 2 ^ (sc + E) < ((2 : ℝ) ^ sc - theta) * 2 ^ YSC := by
    rw [← hsub]; exact_mod_cast h2
  have hY : (0 : ℝ) < 2 ^ YSC := by positivity
  have hS : (0 : ℝ) < 2 ^ sc := by positivity
  have hE : (0 : ℝ) < 2 ^ E := by positivity
  rw [zpow_neg, zpow_natCast, div_lt_iff₀ hY]
  rw [pow_add] at h2'
  have : (1 - (theta : ℝ) / 2 ^ sc) = ((2 : ℝ) ^ sc - theta) / 2 ^ sc := by field_simp
  rw [this]
  rw [show ((2 : ℝ) ^ E)⁻¹ * (((2 : ℝ) ^ sc - theta) / 2 ^ sc) * 2 ^ YSC =
      ((2 : ℝ) ^ sc - theta) * 2 ^ YSC / (2 ^ sc * 2 ^ E) by field_simp]
  rw [lt_div_iff₀ (by positivity)]
  linarith

#print axioms short_metric_sound
#print axioms total_sound
#print axioms gap_sound

end ThomsonCompact.Floor
