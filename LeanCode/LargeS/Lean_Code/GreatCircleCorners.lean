import Lean_Code.PatchChainSplicing

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Two different outgoing tangent rays form a strictly shortcuttable corner,
unless they are exactly opposite. -/
theorem great_circle_corner_shortening (m t u : ℝ³)
    (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (hu : ‖u‖ = 1)
    (hmt : inner ℝ m t = 0) (hmu : inner ℝ m u = 0) (hne : t ≠ -u)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    sphereAngle (greatCirclePoint m t δ) (greatCirclePoint m u δ) < 2 * δ := by
  have htm : inner ℝ t m = 0 := (real_inner_comm m t).trans hmt
  have hinner : inner ℝ (greatCirclePoint m t δ) (greatCirclePoint m u δ) =
      Real.cos δ ^ 2 + Real.sin δ ^ 2 * inner ℝ t u := by
    simp only [greatCirclePoint, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial,
      real_inner_self_eq_norm_sq, hm, htm, hmu]
    ring
  have htu : 0 < 1 + inner ℝ t u := by
    have h := (unit_pair_sum_support t u ht hu hne).2
    simpa [inner_add_left, hu, add_comm] using h
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ.1
    (by linarith [hδ.2, Real.pi_pos])
  apply sphereAngle_lt_of_cos_lt_inner _ _ (greatCirclePoint_unit m t hm ht hmt δ)
    (greatCirclePoint_unit m u hm hu hmu δ) (2 * δ)
    ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
  rw [hinner, show 2 * δ = δ + δ by ring, Real.cos_add]
  nlinarith [mul_pos (sq_pos_of_pos hsin) htu]

lemma exists_small_positive_in_neighborhood (V : Set ℝ) (hV : V ∈ nhds (0 : ℝ))
    (r : ℝ) (hr : 0 < r) : ∃ δ ∈ V, 0 < δ ∧ δ < r := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let δ : ℝ := min ε r / 2
  have hδ : 0 < δ := half_pos (lt_min hε hr)
  have hδε : δ < ε := by dsimp [δ]; have := min_le_left ε r; linarith
  have hδr : δ < r := by dsimp [δ]; have := min_le_right ε r; linarith
  refine ⟨δ, hball ?_, hδ, hδr⟩
  simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ] using hδε

/-- Corner shortening is available arbitrarily close to the corner, allowing
both cut points to lie in one of the finite local convex patches. -/
theorem great_circle_corner_shortening_near (m t u : ℝ³)
    (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (hu : ‖u‖ = 1)
    (hmt : inner ℝ m t = 0) (hmu : inner ℝ m u = 0) (hne : t ≠ -u)
    (U : Set ℝ³) (hU : U ∈ nhds m) (r : ℝ) (hr : 0 < r) :
    ∃ δ, 0 < δ ∧ δ < r ∧
      greatCirclePoint m t δ ∈ U ∧ greatCirclePoint m u δ ∈ U ∧
      sphereAngle (greatCirclePoint m t δ) (greatCirclePoint m u δ) < 2 * δ := by
  have htU : U ∈ nhds (greatCirclePoint m t 0) := by simpa [greatCirclePoint_zero] using hU
  have huU : U ∈ nhds (greatCirclePoint m u 0) := by simpa [greatCirclePoint_zero] using hU
  have hte : ∀ᶠ δ in nhds (0 : ℝ), greatCirclePoint m t δ ∈ U :=
    (greatCirclePoint_continuous m t).continuousAt htU
  have hue : ∀ᶠ δ in nhds (0 : ℝ), greatCirclePoint m u δ ∈ U :=
    (greatCirclePoint_continuous m u).continuousAt huU
  have hV : {δ | greatCirclePoint m t δ ∈ U ∧ greatCirclePoint m u δ ∈ U} ∈ nhds (0 : ℝ) :=
    Filter.inter_mem hte hue
  obtain ⟨δ, hδU, hδ0, hδsmall⟩ := exists_small_positive_in_neighborhood _ hV
    (min r (Real.pi / 2)) (lt_min hr (by linarith [Real.pi_pos]))
  have hδr : δ < r := hδsmall.trans_le (min_le_left _ _)
  have hδpi : δ < Real.pi / 2 := hδsmall.trans_le (min_le_right _ _)
  exact ⟨δ, hδ0, hδr, hδU.1, hδU.2,
    great_circle_corner_shortening m t u hm ht hu hmt hmu hne δ ⟨hδ0, hδpi⟩⟩

end SquareAntiprismVerification
