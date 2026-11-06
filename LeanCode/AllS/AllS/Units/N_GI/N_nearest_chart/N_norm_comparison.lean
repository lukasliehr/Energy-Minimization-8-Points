import AllS.Units.N_GI.N_nearest_chart.N_positive_roots

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem inverseCoordinates_norm_identity (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    ‖inverseCoordinates Y‖^2=chordSquare Y-(∑ i, (‖Y i-packingReference i‖^2)^2)/4 := by
  have ht (i : Fin 8) : ‖tangentVector (inverseCoordinates Y) i‖^2=
      ‖Y i-packingReference i‖^2-(‖Y i-packingReference i‖^2)^2/4 := by
    have hT := SquareAntiprismVerification.inverseSphereChart_norm_sq
      (packingReference i) (Y i) (packingReference_norm i) (hY i)
    rw [← inverseCoordinates_tangent] at hT
    have hN := norm_sub_sq_real (Y i) (packingReference i)
    rw [hY i,packingReference_norm i] at hN
    linear_combination hT+((‖Y i-packingReference i‖^2-2-2*inner ℝ (Y i) (packingReference i))/4)*hN
  rw [← tangentVector_sum_norm_sq]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,Finset.sum_div]
  rfl

theorem nearest_chart_norm_comparison (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    chordSquare Y-(chordSquare Y)^2/4 ≤ ‖inverseCoordinates Y‖^2 ∧
      ‖inverseCoordinates Y‖^2 ≤ chordSquare Y := by
  have he := inverseCoordinates_norm_identity Y hY
  have hn : 0 ≤ ∑ i : Fin 8, (‖Y i-packingReference i‖^2)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : (∑ i : Fin 8, (‖Y i-packingReference i‖^2)^2) ≤ (chordSquare Y)^2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => sq_nonneg ‖Y i-packingReference i‖)
  constructor <;> linarith

#check nearest_chart_norm_comparison
#print axioms nearest_chart_norm_comparison
end Blueprint.Thomson.Tail.Implementation
