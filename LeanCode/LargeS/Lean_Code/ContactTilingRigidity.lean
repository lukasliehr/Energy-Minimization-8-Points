import Lean_Code.ContactTilingData
import Lean_Code.EqualityReconstruction

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Complete equality reconstruction from explicit contact-face data.
The missing global geometric step is the construction of these data and
their boundary-adjacency property for an irreducible packing. -/
theorem contact_tiling_rigidity (Y : Fin 8 → ℝ³) (hY : IsConfiguration Y)
    (hpacking : PackingInnerBound aInf Y) (D : ContactTilingData Y aInf)
    (hboundary : D.BoundaryAdjacency) : Congruent Y P := by
  have hqcount := (D.equality_face_counts hY).2
  let f : Fin D.quadCount := ⟨0, by omega⟩
  have htriangle : ∀ j : Fin 4, ∃ k : Fin 8,
      (∀ i : Fin 4, k ≠ D.quad f i) ∧ inner ℝ (Y (D.quad f j)) (Y k) = aInf ∧
        inner ℝ (Y (D.quad f (j + 1))) (Y k) = aInf := by
    intro j
    rcases hboundary f j with ht | ⟨g, hgf, i, heq⟩
    · exact ht
    · exact False.elim (hgf (D.equality_quads_disjoint hY g f i j heq))
  have hangle : contactAngle aInf (Y (D.quad f 1)) (Y (D.quad f 3)) =
      contactAngle aInf (Y (D.quad f 0)) (Y (D.quad f 2)) := by
    have h0 := D.equality_quad_angles hY f 0
    have h1 := D.equality_quad_angles hY f 1
    change quadrilateralAngle aInf (fun k => Y (D.quad f k)) 0 = _ at h0
    change quadrilateralAngle aInf (fun k => Y (D.quad f k)) 1 = _ at h1
    rw [quadrilateralAngle_alternates] at h0 h1
    norm_num at h0 h1
    exact h0.trans h1.symm
  exact regular_square_triangle_witness_reconstruction Y (D.quad f) hY (D.quad_injective f)
    hpacking (D.quad_contacts f) hangle htriangle

end SquareAntiprismVerification
