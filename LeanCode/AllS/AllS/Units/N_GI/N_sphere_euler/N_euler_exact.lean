import AllS.Units.N_GI.N_tiling_data.N_construct_existing_data
import AllS.Units.N_GI.N_rhombus_excess_lower.N_summed_excess
import AllS.Units.N_GI.N_constants.N_angle_cutoff

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem sphere_euler_euler_exact_of_data {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (E : ℕ) (hD : 3*D.triCount + 4*D.quadCount = 2*E) :
    D.triCount + 2*D.quadCount = 12 :=
  Blueprint.TailEulerArithmetic.euler_count_of_excess D.triCount D.quadCount E
    D.alpha D.quadTotal hD D.euler_lower_bound
    (equilateral_angle_gt_two_pi_fifths c hc.1 hcupper)
    (rhombus_excess_lower_summed_excess D hY hc) D.total_excess_before_euler

theorem sphere_euler_euler_exact (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    Fintype.card (BoundaryOfLength Y c hY hc 3) +
      2 * Fintype.card (BoundaryOfLength Y c hY hc 4) = 12 := by
  let D := tiling_data_construct_existing_data Y c hY hc hcupper hirr hbound hne hsupport
  apply sphere_euler_euler_exact_of_data D hY hc hcupper
    (Fintype.card (PermutationOrbit (contactReverse Y c)))
  change 3 * Fintype.card (BoundaryOfLength Y c hY hc 3) +
    4 * Fintype.card (BoundaryOfLength Y c hY hc 4) = _
  rw [(tiling_data_counts Y c hY hc hcupper hirr hsupport).2, contact_reverse_dart_count]

#print axioms sphere_euler_euler_exact

end Blueprint.Thomson.Tail.Implementation
