import AllS.Units.N_GI.N_tiling_data.N_counts
import AllS.Units.N_GI.N_tiling_data.N_angle_sum
import AllS.Units.N_GI.N_weak_euler.N_assemble
import Lean_Code.ContactTilingData

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem tiling_data_euler_lower (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    12 ≤ Fintype.card (BoundaryOfLength Y c hY hc 3) + 2 * Fintype.card (BoundaryOfLength Y c hY hc 4) := by
  have hEuler := weak_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hcounts := tiling_data_counts Y c hY hc hcupper hirr hsupport
  omega

def tiling_data_construct_existing_data (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) : ContactTilingData Y c where
  triCount := Fintype.card (BoundaryOfLength Y c hY hc 3)
  quadCount := Fintype.card (BoundaryOfLength Y c hY hc 4)
  tri := boundaryArray Y c hY hc 3
  quad := boundaryArray Y c hY hc 4
  tri_injective f := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_injective
    exact hsupport _
  quad_injective f := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_injective
    exact hsupport _
  tri_contacts f i j hij := by
    unfold boundaryArray
    exact ContactBoundaryCycle.reindex_triangle_contacts _ _ i j hij
  quad_contacts f j := by
    unfold boundaryArray
    exact ContactBoundaryCycle.reindex_side _ _ j
  quad_diagonal02 f := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_diagonal _ _ hirr hbound (hsupport _) <;> decide
  quad_diagonal13 f := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_diagonal _ _ hirr hbound (hsupport _) <;> decide
  angle_sum v := tiling_data_angle_sum Y c hY hc hcupper hirr hbound hne hsupport v
  euler_lower_bound := tiling_data_euler_lower Y c hY hc hcupper hirr hbound hne hsupport

#print axioms tiling_data_construct_existing_data

end Blueprint.Thomson.Tail.Implementation
