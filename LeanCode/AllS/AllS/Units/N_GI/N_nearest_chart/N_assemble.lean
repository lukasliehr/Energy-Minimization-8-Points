import AllS.Units.N_GI.N_nearest_chart.N_orthogonal_slice
import AllS.Units.N_GI.N_nearest_chart.N_norm_comparison
import AllS.Units.N_GI.N_nearest_chart.N_chart_unit

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def chordOrbitRadius (Y : Fin 8 → Point) : ℝ := Real.sqrt (chordOrbitSquare Y)

theorem chordOrbitRadius_sq (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    (chordOrbitRadius Y)^2=chordOrbitSquare Y := by
  obtain ⟨U,σ,hZ,he,hmin,hcross⟩ := chord_alignment_exists Y hY
  exact Real.sq_sqrt (he ▸ chordSquare_nonneg (fun i => U (Y (σ i))))

theorem nearest_chart_assemble (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1)
    (hr : chordOrbitRadius Y < 1) :
    ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)) (q : TangentCoordinates),
      q ∈ rotationSlice ∧ ‖q‖ < 1 ∧
      (∀ i, orthographicChart q i=U (Y (σ i))) ∧
      chordSquare (fun i => U (Y (σ i)))=(chordOrbitRadius Y)^2 ∧
      (chordOrbitRadius Y)^2-(chordOrbitRadius Y)^4/4 ≤ ‖q‖^2 ∧
      ‖q‖^2 ≤ (chordOrbitRadius Y)^2 := by
  obtain ⟨U,σ,hZ,he,hmin,hcross⟩ := chord_alignment_exists Y hY
  let Z : Fin 8 → Point := fun i => U (Y (σ i))
  have hrad := chordOrbitRadius_sq Y hY
  have hr0 : 0 ≤ chordOrbitRadius Y := Real.sqrt_nonneg _
  have hsmall : chordSquare Z < 1 := by
    change chordSquare (fun i => U (Y (σ i))) < 1
    rw [he,← hrad]
    nlinarith
  have hroots := nearest_chart_positive_roots Z hZ hsmall
  have hnorm := nearest_chart_norm_comparison Z hZ
  refine ⟨U,σ,inverseCoordinates Z,nearest_chart_orthogonal_slice Z hZ hmin,
    ?_,fun i => (hroots i).2,he.trans hrad.symm,?_,?_⟩
  · nlinarith [norm_nonneg (inverseCoordinates Z)]
  · have h4 : (chordOrbitRadius Y)^4=((chordOrbitRadius Y)^2)^2 := by ring
    rw [h4,hrad,← he]
    exact hnorm.1
  · rw [hrad,← he]
    exact hnorm.2

#check nearest_chart_assemble
#print axioms nearest_chart_assemble
end Blueprint.Thomson.Tail.Implementation
