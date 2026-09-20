import Lean_Code.ContactCertificate

open Real
noncomputable section
namespace SquareAntiprismVerification

def GaugeUnit : Set InfinitesimalCoordinates :=
  {q | InContactGauge q ∧ ‖q‖ = 1}

lemma gaugeUnit_compact : IsCompact GaugeUnit := by
  have ha : IsClosed {q : InfinitesimalCoordinates | q.1 0 = 0} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hb0 : IsClosed {q : InfinitesimalCoordinates | q.2 0 = 0} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hb1 : IsClosed {q : InfinitesimalCoordinates | q.2 1 = 0} := by
    exact isClosed_eq (by fun_prop) continuous_const
  have hn : IsClosed {q : InfinitesimalCoordinates | ‖q‖ = 1} := by
    exact isClosed_eq continuous_norm continuous_const
  have hclosed : IsClosed GaugeUnit := by
    simpa only [GaugeUnit, InContactGauge, Set.setOf_and] using
      ((ha.inter (hb0.inter hb1)).inter hn)
  have hsub : GaugeUnit ⊆ Metric.sphere (0 : InfinitesimalCoordinates) 1 := by
    intro q hq
    rw [Metric.mem_sphere, dist_zero_right]
    exact hq.2
  exact (isCompact_sphere (0 : InfinitesimalCoordinates) 1).of_isClosed_subset
    hclosed hsub

lemma gaugeUnit_nonempty : GaugeUnit.Nonempty := by
  let α : Fin 8 → ℝ := Pi.single 1 1
  let q : InfinitesimalCoordinates := (α, 0)
  refine ⟨q, ?_⟩
  constructor
  · dsimp [InContactGauge, q, α]
    simp [Pi.single_apply]
  · dsimp [q, α]
    simp [Prod.norm_def, Pi.norm_single]

lemma selectedContactRows_norm_continuous : Continuous (fun q : InfinitesimalCoordinates =>
    ‖selectedContactRows q‖) := by
  unfold selectedContactRows rigidityRow azimuth layerSign aInf
  fun_prop

lemma contact_unit_lower_bound :
    ∃ μ : ℝ, 0 < μ ∧ ∀ q ∈ GaugeUnit, μ ≤ ‖selectedContactRows q‖ := by
  obtain ⟨q₀, hq₀, hmin⟩ := gaugeUnit_compact.exists_isMinOn
    gaugeUnit_nonempty selectedContactRows_norm_continuous.continuousOn
  let μ := ‖selectedContactRows q₀‖
  have hμ : 0 < μ := by
    have hn : 0 ≤ μ := norm_nonneg _
    rcases hn.eq_or_lt with heq | hpos
    · have hz : selectedContactRows q₀ = 0 := norm_eq_zero.mp heq.symm
      have hqz := selectedContactRows_eq_zero hq₀.1 hz
      rw [hqz] at hq₀
      change InContactGauge 0 ∧ ‖(0 : InfinitesimalCoordinates)‖ = 1 at hq₀
      norm_num at hq₀
    · exact hpos
  exact ⟨μ, hμ, fun q hq => hmin hq⟩

lemma selectedContactRows_smul (c : ℝ) (q : InfinitesimalCoordinates) :
    selectedContactRows (c • q) = c • selectedContactRows q := by
  funext i
  fin_cases i <;> simp [selectedContactRows, rigidityRow] <;> ring

lemma inContactGauge_smul (c : ℝ) {q : InfinitesimalCoordinates}
    (hq : InContactGauge q) : InContactGauge (c • q) := by
  rcases hq with ⟨ha, hb0, hb1⟩
  constructor
  · simp [ha]
  constructor <;> simp [hb0, hb1]

theorem contact_rank_bound :
    ∃ μ : ℝ, 0 < μ ∧ ∀ q : InfinitesimalCoordinates,
      InContactGauge q → μ * ‖q‖ ≤ ‖selectedContactRows q‖ := by
  obtain ⟨μ, hμ, hunit⟩ := contact_unit_lower_bound
  refine ⟨μ, hμ, ?_⟩
  intro q hq
  by_cases hq0 : q = 0
  · subst q
    simp
  · have hnpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hnne : ‖q‖ ≠ 0 := ne_of_gt hnpos
    let c : ℝ := ‖q‖⁻¹
    let u : InfinitesimalCoordinates := c • q
    have hcpos : 0 < c := inv_pos.mpr hnpos
    have hunorm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, abs_of_pos hcpos]
      dsimp [c]
      exact inv_mul_cancel₀ hnne
    have hugauge : InContactGauge u := inContactGauge_smul c hq
    have hlow : μ ≤ ‖selectedContactRows u‖ := hunit u ⟨hugauge, hunorm⟩
    have hrows : ‖selectedContactRows u‖ = c * ‖selectedContactRows q‖ := by
      rw [selectedContactRows_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hrows] at hlow
    have hmul := mul_le_mul_of_nonneg_right hlow (norm_nonneg q)
    have hcancel : c * ‖q‖ = 1 := by
      dsimp [c]
      exact inv_mul_cancel₀ hnne
    calc
      μ * ‖q‖ ≤ (c * ‖selectedContactRows q‖) * ‖q‖ := hmul
      _ = ‖selectedContactRows q‖ := by
        rw [mul_assoc, mul_comm (‖selectedContactRows q‖) ‖q‖,
          ← mul_assoc, hcancel, one_mul]

end SquareAntiprismVerification
