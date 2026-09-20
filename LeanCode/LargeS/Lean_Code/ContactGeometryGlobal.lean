import Lean_Code.RankinBound

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma aInf_lt_one_third : aInf < (1 / 3 : ℝ) := by
  have hs := sqrt_two_lt_two
  have hs2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold aInf
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- A contact `K₄` is impossible in the range relevant to the maximizing
eight-point packing.  The Gram-square bound avoids spectral machinery. -/
theorem no_four_contact_clique_of_card {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 4) (Y : ι → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 ≤ c) (hcupper : c < 1 / 3)
    (heq : ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) = c) : False := by
  classical
  have hinner (i j : ι) : inner ℝ (Y i) (Y j) = if i = j then 1 else c := by
    by_cases hij : i = j
    · subst j; simp [real_inner_self_eq_norm_sq, hY]
    · simp [hij, heq i j hij]
  have h := gram_square_lower_bound Y hY
  have hrow (i : ι) : (∑ j : ι, inner ℝ (Y i) (Y j) ^ 2) = 1 + 3 * c ^ 2 := by
    have hp (j : ι) : inner ℝ (Y i) (Y j) ^ 2 =
        (if i = j then 1 - c ^ 2 else 0) + c ^ 2 := by
      rw [hinner]
      split_ifs <;> ring
    simp_rw [hp]
    simp [Finset.sum_add_distrib, hcard]
    ring
  simp only [hrow] at h
  norm_num [hcard] at h
  nlinarith

theorem no_four_contact_clique (Y : Fin 4 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : 0 ≤ c) (hcupper : c < 1 / 3)
    (heq : ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) = c) : False :=
  no_four_contact_clique_of_card (by simp) Y c hY hc hcupper heq

lemma norm_convex_contact_combination_sq (a b : ℝ³) (c t : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = c) :
    ‖(1 - t) • a + t • b‖ ^ 2 = 1 - 2 * t * (1 - t) * (1 - c) := by
  have hba : inner ℝ b a = c := by rw [real_inner_comm]; exact hab
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [hab, hba]
  simp [real_inner_self_eq_norm_sq, ha, hb]
  ring

lemma norm_convex_contact_combination_lower (a b : ℝ³) (c t : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = c) (hc : c ≤ 1) :
    (1 + c) / 2 ≤ ‖(1 - t) • a + t • b‖ ^ 2 := by
  rw [norm_convex_contact_combination_sq a b c t ha hb hab]
  have h := mul_nonneg (sq_nonneg (t - 1 / 2)) (sub_nonneg.mpr hc)
  nlinarith

/-- Open shorter arcs are represented by normalized strict convex
combinations.  This definition uses no angular-distance conventions. -/
def OpenContactArc (a b : ℝ³) : Set ℝ³ :=
  {q | ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    q = ‖(1 - t) • a + t • b‖⁻¹ • ((1 - t) • a + t • b)}

theorem disjoint_contact_arcs (a b d e : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hc : 0 < c) (hcupper : c < 1)
    (hab : inner ℝ a b = c) (hde : inner ℝ d e = c)
    (had : inner ℝ a d ≤ c) (hae : inner ℝ a e ≤ c)
    (hbd : inner ℝ b d ≤ c) (hbe : inner ℝ b e ≤ c) :
    Disjoint (OpenContactArc a b) (OpenContactArc d e) := by
  apply Set.disjoint_left.mpr
  intro q hqab hqde
  obtain ⟨t, ht, htone, hqt⟩ := hqab
  obtain ⟨u, hu, huone, hqu⟩ := hqde
  let v := (1 - t) • a + t • b
  let w := (1 - u) • d + u • e
  have hvlow : (1 + c) / 2 ≤ ‖v‖ ^ 2 :=
    norm_convex_contact_combination_lower a b c t ha hb hab hcupper.le
  have hwlow : (1 + c) / 2 ≤ ‖w‖ ^ 2 :=
    norm_convex_contact_combination_lower d e c u hd he hde hcupper.le
  have hvpos : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
  have hwpos : 0 < ‖w‖ := by nlinarith [norm_nonneg w]
  have hqnorm : ‖q‖ = 1 := by
    rw [hqt]
    change ‖‖v‖⁻¹ • v‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos), inv_mul_cancel₀ hvpos.ne']
  have hvq : v = ‖v‖ • q := by
    rw [hqt]
    change v = ‖v‖ • (‖v‖⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hwq : w = ‖w‖ • q := by
    rw [hqu]
    change w = ‖w‖ • (‖w‖⁻¹ • w)
    rw [smul_smul, mul_inv_cancel₀ hwpos.ne', one_smul]
  have hinner : inner ℝ v w = ‖v‖ * ‖w‖ := by
    conv_lhs => rw [hvq, hwq]
    simp [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, hqnorm, mul_comm]
  have hupper : inner ℝ v w ≤ c := by
    dsimp [v, w]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    have h₁ := mul_le_mul_of_nonneg_left had (mul_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ 1 - u))
    have h₂ := mul_le_mul_of_nonneg_left hae (mul_nonneg (by linarith : 0 ≤ 1 - t) hu.le)
    have h₃ := mul_le_mul_of_nonneg_left hbd (mul_nonneg ht.le (by linarith : 0 ≤ 1 - u))
    have h₄ := mul_le_mul_of_nonneg_left hbe (mul_nonneg ht.le hu.le)
    nlinarith
  rw [hinner] at hupper
  have hprod := mul_le_mul hvlow hwlow (by positivity : 0 ≤ (1 + c) / 2) (sq_nonneg _)
  nlinarith [sq_nonneg (‖v‖ * ‖w‖ - c)]

end SquareAntiprismVerification
