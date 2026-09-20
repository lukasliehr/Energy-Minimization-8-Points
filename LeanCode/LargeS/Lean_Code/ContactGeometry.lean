import Lean_Code.PositiveStress
import Lean_Code.ContactRankBound

open Real
noncomputable section
namespace SquareAntiprismVerification

/-- The sixteen unordered contacts of the limiting antiprism. -/
def contactPair : Fin 16 → Fin 8 × Fin 8 :=
  ![(0, 1), (1, 2), (2, 3), (0, 3),
    (4, 5), (5, 6), (6, 7), (4, 7),
    (0, 4), (0, 7), (1, 4), (1, 5),
    (2, 5), (2, 6), (3, 6), (3, 7)]

def contactRows (q : InfinitesimalCoordinates) (e : Fin 16) : ℝ :=
  rigidityRow (contactPair e).1 (contactPair e).2 q.1 q.2

def contactWeight (e : Fin 16) : ℝ := if e.val < 8 then stressWeight else 1

lemma contactPair_lt (e : Fin 16) : (contactPair e).1 < (contactPair e).2 := by
  fin_cases e <;> decide

lemma contactWeight_pos (e : Fin 16) : 0 < contactWeight e := by
  unfold contactWeight stressWeight
  split_ifs <;> positivity

lemma rigidityRow_symm (i j : Fin 8) (α β : Fin 8 → ℝ) :
    rigidityRow i j α β = rigidityRow j i α β := by
  unfold rigidityRow
  rw [show azimuth i - azimuth j = -(azimuth j - azimuth i) by ring,
    Real.sin_neg, Real.cos_neg]
  ring

lemma contactRows_weighted_sum (q : InfinitesimalCoordinates) :
    ∑ e : Fin 16, contactWeight e * contactRows q e = 0 := by
  have h := exact_positive_stress q.1 q.2
  rw [rigidityRow_symm 3 0, rigidityRow_symm 7 4] at h
  simp only [contactRows, contactWeight, contactPair, Fin.sum_univ_succ]
  norm_num
  dsimp
  linear_combination h

lemma contactRows_eq_zero {q : InfinitesimalCoordinates}
    (hg : InContactGauge q) (h : ∀ e, contactRows q e = 0) : q = 0 := by
  apply selectedContactRows_eq_zero hg
  funext k
  fin_cases k
  · exact h 2
  · exact h 4
  · exact h 6
  · exact h 1
  · exact h 7
  · exact h 14
  · exact h 5
  · exact h 13
  · exact h 12
  · exact h 15
  · exact h 3
  · exact h 9
  · exact h 11

/-- Positive equilibrium stress forces a strictly positive inner-product
variation in every nonzero direction after fixing the three rotation
coordinates.  Equivalently, some contact distance decreases. -/
theorem exists_positive_contactRow {q : InfinitesimalCoordinates}
    (hg : InContactGauge q) (hq : q ≠ 0) :
    ∃ e : Fin 16, 0 < contactRows q e := by
  by_contra hn
  push_neg at hn
  have hs : ∑ e : Fin 16, -(contactWeight e * contactRows q e) = 0 := by
    rw [Finset.sum_neg_distrib, contactRows_weighted_sum, neg_zero]
  have hnonneg : ∀ e : Fin 16, 0 ≤ -(contactWeight e * contactRows q e) := by
    intro e
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (contactWeight_pos e)) (hn e))
  have hzero : ∀ e : Fin 16, contactRows q e = 0 := by
    intro e
    have he : -(contactWeight e * contactRows q e) ≤ 0 := by
      rw [← hs]
      exact Finset.single_le_sum (fun j hj => hnonneg j) (Finset.mem_univ e)
    have heq : contactWeight e * contactRows q e = 0 := by linarith [hnonneg e]
    exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt (contactWeight_pos e))
  exact hq (contactRows_eq_zero hg hzero)

def positiveContactSum (q : InfinitesimalCoordinates) : ℝ :=
  ∑ e : Fin 16, max (contactRows q e) 0

lemma positiveContactSum_continuous : Continuous positiveContactSum := by
  unfold positiveContactSum contactRows rigidityRow
  fun_prop

lemma positiveContactSum_pos {q : InfinitesimalCoordinates}
    (hg : InContactGauge q) (hq : q ≠ 0) : 0 < positiveContactSum q := by
  obtain ⟨e, he⟩ := exists_positive_contactRow hg hq
  have hle : max (contactRows q e) 0 ≤ positiveContactSum q := by
    exact Finset.single_le_sum (fun i hi => le_max_right _ _) (Finset.mem_univ e)
  exact (he.trans_le (le_max_left _ _)).trans_le hle

lemma positiveContactSum_unit_lower_bound :
    ∃ μ : ℝ, 0 < μ ∧ ∀ q ∈ GaugeUnit, μ ≤ positiveContactSum q := by
  obtain ⟨q₀, hq₀, hmin⟩ := gaugeUnit_compact.exists_isMinOn
    gaugeUnit_nonempty positiveContactSum_continuous.continuousOn
  refine ⟨positiveContactSum q₀, ?_, fun q hq => hmin hq⟩
  apply positiveContactSum_pos hq₀.1
  intro hzero
  have hn := hq₀.2
  rw [hzero, norm_zero] at hn
  norm_num at hn

lemma contactRows_smul (c : ℝ) (q : InfinitesimalCoordinates) (e : Fin 16) :
    contactRows (c • q) e = c * contactRows q e := by
  simp [contactRows, rigidityRow]
  ring

lemma positiveContactSum_smul (c : ℝ) (hc : 0 ≤ c) (q : InfinitesimalCoordinates) :
    positiveContactSum (c • q) = c * positiveContactSum q := by
  unfold positiveContactSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [contactRows_smul]
  by_cases hr : 0 ≤ contactRows q e
  · rw [max_eq_left hr, max_eq_left (mul_nonneg hc hr)]
  · have hr' : contactRows q e ≤ 0 := le_of_lt (lt_of_not_ge hr)
    rw [max_eq_right hr', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hr'),
      mul_zero]

theorem uniform_positive_contactRow :
    ∃ c : ℝ, 0 < c ∧ ∀ q : InfinitesimalCoordinates,
      InContactGauge q → ∃ e : Fin 16, c * ‖q‖ ≤ contactRows q e := by
  obtain ⟨μ, hμ, hunit⟩ := positiveContactSum_unit_lower_bound
  refine ⟨μ / 16, by positivity, ?_⟩
  intro q hg
  by_cases hq : q = 0
  · subst q
    exact ⟨0, by simp [contactRows, rigidityRow]⟩
  have hnpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let u : InfinitesimalCoordinates := ‖q‖⁻¹ • q
  have hunorm : ‖u‖ = 1 := by
    simp [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos), hnpos.ne']
  have hlow := hunit u ⟨inContactGauge_smul _ hg, hunorm⟩
  have hμq : μ * ‖q‖ ≤ positiveContactSum q := by
    change μ ≤ positiveContactSum (‖q‖⁻¹ • q) at hlow
    rw [positiveContactSum_smul _ (le_of_lt (inv_pos.mpr hnpos))] at hlow
    have hh := mul_le_mul_of_nonneg_left hlow (norm_nonneg q)
    simpa [← mul_assoc, hnpos.ne', mul_comm ‖q‖ μ] using hh
  by_contra hn
  push_neg at hn
  have hmax : ∀ e : Fin 16, max (contactRows q e) 0 < μ / 16 * ‖q‖ := by
    intro e
    exact max_lt (hn e) (by positivity)
  have hsum : positiveContactSum q < ∑ _ : Fin 16, μ / 16 * ‖q‖ := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun e he => hmax e)
  norm_num at hsum
  linarith

end SquareAntiprismVerification
