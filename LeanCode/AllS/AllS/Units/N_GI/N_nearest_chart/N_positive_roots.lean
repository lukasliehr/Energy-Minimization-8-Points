import AllS.Units.N_GI.N_nearest_chart.N_tangent

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def chordSquare (Y : Fin 8 → Point) : ℝ := ∑ i, ‖Y i-packingReference i‖^2

theorem chordSquare_nonneg (Y : Fin 8 → Point) : 0 ≤ chordSquare Y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem chordSquare_term_le (Y : Fin 8 → Point) (i : Fin 8) :
    ‖Y i-packingReference i‖^2 ≤ chordSquare Y :=
  Finset.single_le_sum (fun j _ => sq_nonneg ‖Y j-packingReference j‖) (Finset.mem_univ i)

theorem nearest_chart_positive_roots (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1)
    (hsmall : chordSquare Y < 1) :
    ∀ i, 0 < inner ℝ (packingReference i) (Y i) ∧ orthographicChart (inverseCoordinates Y) i=Y i := by
  intro i
  have hnorm := norm_sub_sq_real (Y i) (packingReference i)
  rw [hY i,packingReference_norm i] at hnorm
  have ht := chordSquare_term_le Y i
  have hs : 0 < inner ℝ (Y i) (packingReference i) := by nlinarith
  refine ⟨by rw [real_inner_comm]; exact hs,?_⟩
  change SquareAntiprismVerification.sphereChart (packingReference i) (tangentVector (inverseCoordinates Y) i)=Y i
  rw [inverseCoordinates_tangent]
  exact SquareAntiprismVerification.sphereChart_inverse _ _ (packingReference_norm i) (hY i) hs.le

#check nearest_chart_positive_roots
#print axioms nearest_chart_positive_roots
end Blueprint.Thomson.Tail.Implementation
