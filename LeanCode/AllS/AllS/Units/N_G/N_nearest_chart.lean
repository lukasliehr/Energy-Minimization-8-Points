import AllS.Units.N_GI.N_nearest_chart.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem nearest_chart (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1)
    (hr : chordOrbitRadius Y < 1) :
    (∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)) (q : TangentCoordinates),
      q ∈ rotationSlice ∧ ‖q‖ < 1 ∧
      (∀ i, orthographicChart q i=U (Y (σ i))) ∧
      chordSquare (fun i => U (Y (σ i)))=(chordOrbitRadius Y)^2 ∧
      (chordOrbitRadius Y)^2-(chordOrbitRadius Y)^4/4 ≤ ‖q‖^2 ∧
      ‖q‖^2 ≤ (chordOrbitRadius Y)^2) ∧
    (∀ q : TangentCoordinates, ‖q‖ < 1 → ∀ i, ‖orthographicChart q i‖=1) :=
  ⟨nearest_chart_assemble Y hY hr,nearest_chart_chart_unit⟩

#check nearest_chart
#print axioms nearest_chart
end Blueprint.Thomson.Tail
