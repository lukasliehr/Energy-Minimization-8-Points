import Lean_Code.BoundaryFaceArrays
import Lean_Code.ContactTilingData

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- All face arrays, their actual angle sums, and the Euler bound are
constructed from the boundary orbits. The only geometric hypothesis left
here is strict support of the actual boundary cycles. -/
def supportedContactTilingData (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
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
  angle_sum v := boundary_array_angle_sum Y c hY hc hcupper hirr hbound hne hsupport v
  euler_lower_bound := boundary_array_euler_bound Y c hY hc hcupper hirr hbound hne hsupport

theorem packing_constant_of_boundary_support (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) : c = aInf :=
  ((supportedContactTilingData Y c hY hc hcupper hirr hbound hne hsupport).packing_and_euler
    hY hc.1 hcupper).1

end SquareAntiprismVerification
