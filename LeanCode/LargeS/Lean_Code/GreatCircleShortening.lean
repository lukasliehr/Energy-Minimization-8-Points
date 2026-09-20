import Lean_Code.SphericalArcSupport

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Unit-speed great-circle coordinates relative to an orthonormal pair. -/
def greatCirclePoint (m t : ℝ³) (a : ℝ) : ℝ³ :=
  Real.cos a • m + Real.sin a • t

lemma greatCirclePoint_unit (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (a : ℝ) : ‖greatCirclePoint m t a‖ = 1 := by
  have h := real_inner_self_eq_norm_sq (greatCirclePoint m t a)
  have hrev : inner ℝ t m = 0 := (real_inner_comm m t).trans horth
  simp only [greatCirclePoint, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq,
    hm, ht, horth, hrev] at h
  change ‖Real.cos a • m + Real.sin a • t‖ = 1
  nlinarith [Real.sin_sq_add_cos_sq a, norm_nonneg (Real.cos a • m + Real.sin a • t)]

lemma greatCirclePoint_inner (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (a b : ℝ) :
    inner ℝ (greatCirclePoint m t a) (greatCirclePoint m t b) = Real.cos (a - b) := by
  have hrev : inner ℝ t m = 0 := (real_inner_comm m t).trans horth
  simp only [greatCirclePoint, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq,
    hm, ht, horth, hrev, Real.cos_sub]
  ring

lemma greatCirclePoint_transverse_inner (m t n : ℝ³) (hm : ‖m‖ = 1)
    (hmt : inner ℝ m t = 0) (hmn : inner ℝ m n = 0)
    (htn : inner ℝ t n = 0) (a ε : ℝ) :
    inner ℝ (greatCirclePoint m t a) (greatCirclePoint m n ε) =
      Real.cos a * Real.cos ε := by
  have htm : inner ℝ t m = 0 := (real_inner_comm m t).trans hmt
  simp [greatCirclePoint, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hm, htm, hmn, htn, mul_comm]

lemma sphereAngle_lt_of_cos_lt_inner (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) Real.pi)
    (hcos : Real.cos a < inner ℝ x y) : sphereAngle x y < a := by
  by_contra hnot
  have h := Real.strictAntiOn_cos.antitoneOn ha (sphereAngle_range x y) (le_of_not_gt hnot)
  rw [cos_sphereAngle x y hx hy] at h
  exact (not_lt_of_ge h) hcos

/-- The decisive shortening inequality: for a great-circle subarc of length
`2*a > π`, moving its midpoint transversely makes the sum of the two shorter
endpoint-to-midpoint arcs strictly smaller. No polygon convexity or hemisphere
containment is assumed here. -/
theorem great_circle_transverse_shortening (m t n : ℝ³)
    (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (hn : ‖n‖ = 1)
    (hmt : inner ℝ m t = 0) (hmn : inner ℝ m n = 0) (htn : inner ℝ t n = 0)
    (a ε : ℝ) (ha : a ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (hε : ε ∈ Set.Ioo (0 : ℝ) Real.pi) :
    sphereAngle (greatCirclePoint m t (-a)) (greatCirclePoint m n ε) +
      sphereAngle (greatCirclePoint m n ε) (greatCirclePoint m t a) < 2 * a := by
  have hpi := Real.pi_pos
  have haI : a ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith [ha.1], ha.2.le⟩
  have hcosa : Real.cos a < 0 := by
    have h := Real.strictAntiOn_cos (show Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi by
      constructor <;> linarith) haI ha.1
    simpa only [Real.cos_pi_div_two] using h
  have hcosε : Real.cos ε < 1 := by
    have h := Real.strictAntiOn_cos (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi by
      exact ⟨le_rfl, hpi.le⟩) ⟨hε.1.le, hε.2.le⟩ hε.1
    simpa only [Real.cos_zero] using h
  have hproduct : Real.cos a < Real.cos a * Real.cos ε := by
    nlinarith [mul_pos (neg_pos.mpr hcosa) (sub_pos.mpr hcosε)]
  have hleft : sphereAngle (greatCirclePoint m t (-a)) (greatCirclePoint m n ε) < a := by
    apply sphereAngle_lt_of_cos_lt_inner _ _
      (greatCirclePoint_unit m t hm ht hmt (-a)) (greatCirclePoint_unit m n hm hn hmn ε) a haI
    rw [greatCirclePoint_transverse_inner m t n hm hmt hmn htn, Real.cos_neg]
    exact hproduct
  have hright : sphereAngle (greatCirclePoint m n ε) (greatCirclePoint m t a) < a := by
    rw [sphereAngle_comm]
    apply sphereAngle_lt_of_cos_lt_inner _ _
      (greatCirclePoint_unit m t hm ht hmt a) (greatCirclePoint_unit m n hm hn hmn ε) a haI
    rw [greatCirclePoint_transverse_inner m t n hm hmt hmn htn]
    exact hproduct
  linarith

lemma greatCirclePoint_continuous (m t : ℝ³) : Continuous (greatCirclePoint m t) := by
  unfold greatCirclePoint
  fun_prop

lemma greatCirclePoint_zero (m t : ℝ³) : greatCirclePoint m t 0 = m := by
  simp [greatCirclePoint]

/-- The shortening perturbation can be made arbitrarily small. The separate
region-stability step will ensure that its two arcs remain inside the face. -/
theorem arbitrarily_small_great_circle_shortening (m t n : ℝ³)
    (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (hn : ‖n‖ = 1)
    (hmt : inner ℝ m t = 0) (hmn : inner ℝ m n = 0) (htn : inner ℝ t n = 0)
    (a : ℝ) (ha : a ∈ Set.Ioo (Real.pi / 2) Real.pi)
    (U : Set ℝ³) (hU : U ∈ nhds m) :
    ∃ z ∈ U, ‖z‖ = 1 ∧
      sphereAngle (greatCirclePoint m t (-a)) z +
        sphereAngle z (greatCirclePoint m t a) < 2 * a := by
  have hcont := (greatCirclePoint_continuous m n).continuousAt (x := (0 : ℝ))
  have hU' : U ∈ nhds (greatCirclePoint m n 0) := by
    simpa only [greatCirclePoint_zero] using hU
  have hevent : ∀ᶠ ε in nhds (0 : ℝ), greatCirclePoint m n ε ∈ U := hcont hU'
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let ε : ℝ := min δ Real.pi / 2
  have hε0 : 0 < ε := half_pos (lt_min hδ Real.pi_pos)
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ Real.pi; linarith
  have hεπ : ε < Real.pi := by
    dsimp [ε]
    have := min_le_right δ Real.pi
    linarith [Real.pi_pos]
  refine ⟨greatCirclePoint m n ε, hball ?_, greatCirclePoint_unit m n hm hn hmn ε,
    great_circle_transverse_shortening m t n hm ht hn hmt hmn htn a ε ha ⟨hε0, hεπ⟩⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε0] using hεδ

end SquareAntiprismVerification
