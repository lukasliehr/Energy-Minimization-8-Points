import Lean_Code.LocalChart
import Lean_Code.ContactGeometry
import Lean_Code.EnergyBounds

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

set_option maxHeartbeats 3000000

lemma P_contact_sq (e : Fin 16) :
    ‖P (contactPair e).1 - P (contactPair e).2‖ ^ 2 = tau := by
  unfold P
  rw [X_eq_Xc]
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hra : √(1 - aInf) ^ 2 = 1 - aInf :=
    Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hha : √aInf ^ 2 = aInf := Real.sq_sqrt (le_of_lt aInf_mem_Ioo.1)
  have hrs2 : (√(1 - aInf) * √2) ^ 2 = 2 * (1 - aInf) := by
    rw [mul_pow, hra, hs2]
    ring
  have hrel : 1 - aInf = 2 * √2 * aInf := by
    unfold aInf
    field_simp
    nlinarith [hs2]
  have hrasqrt : √(1 - aInf) ^ 2 * √2 = (1 - aInf) * √2 := by rw [hra]
  fin_cases e <;>
    simp [contactPair, Xc, norm_vec3_sub, r, h, tau] <;>
    (try rw [Real.sq_sqrt (by positivity)]) <;>
    nlinarith [hs2, hra, hha, hrs2, hrel, hrasqrt]

/-- Squared contact lengths in the actual square-root chart. -/
def chartContactDistance (q : InfinitesimalCoordinates) (e : Fin 16) : ℝ :=
  ‖coordinateChart q (contactPair e).1 - coordinateChart q (contactPair e).2‖ ^ 2

@[simp] lemma chartContactDistance_zero (e : Fin 16) :
    chartContactDistance 0 e = tau := by
  simpa only [chartContactDistance, coordinateChart_zero, ← P_eq_polarP]
    using P_contact_sq e

lemma chartContactDistance_differentiableAt (e : Fin 16) :
    DifferentiableAt ℝ (fun q => chartContactDistance q e) 0 := by
  exact (((coordinateChart_contDiffAt (contactPair e).1).sub
    (coordinateChart_contDiffAt (contactPair e).2)).norm_sq ℝ).differentiableAt
      (by norm_num)

lemma chartContactDistance_contDiffAt (e : Fin 16) :
    ContDiffAt ℝ 2 (fun q => chartContactDistance q e) 0 := by
  exact ((coordinateChart_contDiffAt (contactPair e).1).sub
    (coordinateChart_contDiffAt (contactPair e).2)).norm_sq ℝ

lemma chartContactDistance_fderiv (q : InfinitesimalCoordinates) (e : Fin 16) :
    fderiv ℝ (fun q => chartContactDistance q e) 0 q = -2 * contactRows q e := by
  have h := (chartContactDistance_differentiableAt e).hasFDerivAt
  have hray : HasDerivAt (fun t : ℝ => t • q) q 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const q
  have hcomp := (show HasFDerivAt (fun q => chartContactDistance q e)
      (fderiv ℝ (fun q => chartContactDistance q e) 0) ((fun t : ℝ => t • q) 0)
      from by simpa using h).comp_hasDerivAt (0 : ℝ) hray
  have hd := chartSquaredDistance_hasDerivAt q (contactPair e).1 (contactPair e).2
  rw [squaredDistanceDifferential_eq] at hd
  apply HasDerivAt.unique hcomp
  simpa [Function.comp_def, chartContactDistance, coordinateChart_smul,
    chartSquaredDistance, contactRows] using hd

/-- A single neighborhood controls the first-order remainder at all contacts. -/
lemma chartContactDistance_uniform_remainder (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : InfinitesimalCoordinates, ‖q‖ < ε →
      ∀ e : Fin 16,
        |chartContactDistance q e - chartContactDistance 0 e + 2 * contactRows q e|
          ≤ c * ‖q‖ := by
  have he : ∀ e : Fin 16, ∀ᶠ q : InfinitesimalCoordinates in nhds 0,
      |chartContactDistance q e - chartContactDistance 0 e + 2 * contactRows q e|
        ≤ c * ‖q‖ := by
    intro e
    have h := (chartContactDistance_differentiableAt e).hasFDerivAt.isLittleO.bound hc
    simpa [chartContactDistance_fderiv, Real.norm_eq_abs, sub_neg_eq_add] using h
  have hall := Filter.eventually_all.mpr he
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε, hε, fun q hq => hball ?_⟩
  simpa [dist_zero_right] using hq

/-- The qualitative linear packing loss, with constants independent of the
perturbation.  This is the chart form of the paper's linear-loss lemma. -/
theorem chart_linear_packing_loss :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ q : InfinitesimalCoordinates,
      InContactGauge q → ‖q‖ < ε →
        ∃ e : Fin 16, chartContactDistance q e ≤ tau - c * ‖q‖ := by
  obtain ⟨c, hc, hrow⟩ := uniform_positive_contactRow
  obtain ⟨ε, hε, herror⟩ := chartContactDistance_uniform_remainder c hc
  refine ⟨c, ε, hc, hε, ?_⟩
  intro q hg hq
  obtain ⟨e, he⟩ := hrow q hg
  refine ⟨e, ?_⟩
  have herr := (abs_le.mp (herror q hq e)).2
  rw [chartContactDistance_zero] at herr
  linarith

lemma one_sub_rpow_neg_div_le (p : ℝ) :
    1 - (28 : ℝ) ^ (-1 / p) ≤ Real.log 28 / p := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 28)]
  have h := Real.add_one_le_exp (Real.log 28 * (-1 / p))
  have heq : Real.log 28 * (-1 / p) = -(Real.log 28 / p) := by ring
  rw [heq] at h ⊢
  linarith

/-- Once a sublevel configuration is in the fixed chart neighborhood, the
energy bound and linear packing loss put its coordinates in an `O(1/p)` ball.
No global packing-rigidity assumption is used in this estimate. -/
theorem chart_sublevel_localization :
    ∃ K ε : ℝ, 0 < K ∧ 0 < ε ∧ ∀ p : ℝ, 0 < p →
      ∀ q : InfinitesimalCoordinates, InContactGauge q → ‖q‖ < ε →
      IsConfiguration (coordinateChart q) →
      E (2 * p) (coordinateChart q) ≤ E (2 * p) P → ‖q‖ < K / p := by
  obtain ⟨c, ε, hc, hε, hloss⟩ := chart_linear_packing_loss
  have htau : 0 < tau := by unfold tau; linarith [aInf_mem_Ioo.2]
  let K : ℝ := tau * Real.log 28 / c + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, ε, hK, hε, ?_⟩
  intro p hp q hg hq hconfig hsub
  obtain ⟨e, he⟩ := hloss q hg hq
  have hpair := pairwise_sublevel_bound p hp (coordinateChart q) hconfig hsub
    (contactPair e).1 (contactPair e).2 (ne_of_lt (contactPair_lt e))
  change tau * (28 : ℝ) ^ (-1 / p) ≤ chartContactDistance q e at hpair
  have hgap := mul_le_mul_of_nonneg_left (one_sub_rpow_neg_div_le p) htau.le
  have hbound : c * ‖q‖ ≤ tau * (Real.log 28 / p) := by nlinarith
  have hmult := mul_le_mul_of_nonneg_right hbound hp.le
  have hnorm : ‖q‖ * p ≤ tau * Real.log 28 / c := by
    apply (le_div_iff₀ hc).mpr
    have hcancel : tau * (Real.log 28 / p) * p = tau * Real.log 28 := by
      field_simp
    rw [hcancel] at hmult
    nlinarith
  apply (lt_div_iff₀ hp).mpr
  exact hnorm.trans_lt (by dsimp [K]; linarith)

end SquareAntiprismVerification
