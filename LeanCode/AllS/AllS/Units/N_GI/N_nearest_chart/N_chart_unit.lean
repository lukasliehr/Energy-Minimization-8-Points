import AllS.Units.N_GI.N_nearest_chart.N_tangent

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem nearest_chart_chart_unit (q : TangentCoordinates) (hq : ‖q‖ < 1) :
    ∀ i, ‖orthographicChart q i‖=1 := by
  intro i
  exact SquareAntiprismVerification.sphereChart_norm _ _ (packingReference_norm i)
    (tangentVector_orthogonal q i) ((tangentVector_norm_le q i).trans hq.le)

#check nearest_chart_chart_unit
#print axioms nearest_chart_chart_unit
end Blueprint.Thomson.Tail.Implementation
