import AllS.Units.N_GI.N_stationary_chart.N_sphere_stationarity
import AllS.Units.N_GI.N_nearest_chart.N_chart_unit

noncomputable section
open Filter
namespace Blueprint.Thomson.Tail.Implementation

theorem chart_line_tangent (q ξ : TangentCoordinates) (i : Fin 8) (t : ℝ) :
    tangentVector (q+t • ξ) i=tangentVector q i+t • tangentVector ξ i := by
  rw [tangentVector_add,tangentVector_smul]

theorem chart_line_differentiable (q ξ : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    DifferentiableAt ℝ (fun t : ℝ => orthographicChart (q+t • ξ) i) 0 := by
  have ht : DifferentiableAt ℝ (fun t : ℝ => tangentVector (q+t • ξ) i) 0 := by
    simp only [chart_line_tangent]
    fun_prop
  have hbase : 0 < 1-‖tangentVector q i‖^2 := by
    have hl := (tangentVector_norm_le q i).trans_lt hq
    nlinarith [norm_nonneg (tangentVector q i)]
  have hs : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (1-‖tangentVector (q+t • ξ) i‖^2)) 0 := by
    apply ((differentiableAt_const (1:ℝ)).sub (ht.norm_sq ℝ)).sqrt
    simpa using hbase.ne'
  exact (hs.smul_const (packingReference i)).add ht

theorem chart_line_unit_eventually (q ξ : TangentCoordinates) (hq : ‖q‖ < 1) :
    ∀ᶠ t in nhds (0:ℝ), ∀ i, ‖orthographicChart (q+t • ξ) i‖=1 := by
  have hc : ContinuousAt (fun t : ℝ => ‖q+t • ξ‖) 0 := by fun_prop
  have hh : ‖q+(0:ℝ) • ξ‖ < 1 := by simpa using hq
  have he := hc.eventually (isOpen_Iio.mem_nhds hh)
  filter_upwards [he] with t ht
  exact nearest_chart_chart_unit _ ht

theorem stationary_chart_chart_curve (p a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (q ξ : TangentCoordinates) (hq : ‖q‖ < 1)
    (hc : Thomson.Congruent (orthographicChart q) (X a)) :
    (∀ i, DifferentiableAt ℝ (fun t : ℝ => orthographicChart (q+t • ξ) i) 0) ∧
    (∀ᶠ t in nhds (0:ℝ), ∀ i, ‖orthographicChart (q+t • ξ) i‖=1) ∧
    IsConfiguration (orthographicChart q) := by
  refine ⟨chart_line_differentiable q ξ hq,chart_line_unit_eventually q ξ hq,?_⟩
  obtain ⟨U,σ,h⟩ := hc
  have hX := Blueprint.antiprism_is_configuration a ha
  constructor
  · intro i
    rw [h i,U.norm_map,hX.1]
  · intro i j he
    rw [h i,h j] at he
    exact σ.injective (hX.2 (U.injective he))

#check stationary_chart_chart_curve
#print axioms stationary_chart_chart_curve
end Blueprint.Thomson.Tail.Implementation
