import AllS.Units.N_GI.N_stationary_chart.N_chart_zero

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem stationary_chart_assemble (p a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (hF : F (2*p) a=0) : Stationary p (X a) ∧
    ∀ q ξ : TangentCoordinates, ‖q‖ < 1 → Thomson.Congruent (orthographicChart q) (X a) →
      HasDerivAt (fun t : ℝ => squaredEnergy p (orthographicChart (q+t • ξ))) 0 0 :=
  ⟨(stationary_chart_sphere_stationarity p a ha hF).1,stationary_chart_chart_zero p a ha hF⟩

#check stationary_chart_assemble
#print axioms stationary_chart_assemble
end Blueprint.Thomson.Tail.Implementation
