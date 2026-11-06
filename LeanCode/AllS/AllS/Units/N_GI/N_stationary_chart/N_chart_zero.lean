import AllS.Units.N_GI.N_stationary_chart.N_chart_curve

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem stationary_chart_chart_zero (p a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (hF : F (2*p) a=0) (q ξ : TangentCoordinates) (hq : ‖q‖ < 1)
    (hc : Thomson.Congruent (orthographicChart q) (X a)) :
    HasDerivAt (fun t : ℝ => squaredEnergy p (orthographicChart (q+t • ξ))) 0 0 := by
  have hs := (stationary_chart_sphere_stationarity p a ha hF).2 (orthographicChart q) hc
  obtain ⟨hd,hu,_⟩ := stationary_chart_chart_curve p a ha q ξ hq hc
  exact hs (fun t => orthographicChart (q+t • ξ)) (by simp) hd hu

#check stationary_chart_chart_zero
#print axioms stationary_chart_chart_zero
end Blueprint.Thomson.Tail.Implementation
