import AllS.Units.N_GI.N_rhombus_angles.N_types
import AllS.Units.N_GI.N_tiling_data.N_face_arrays

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def vertexQuadCornerEquiv {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (v : Fin 8) :
    ↥(faceCornersAt D.quad v) ≃ Fin (faceCornerCount D.quad v) :=
  (Fintype.equivFin _).trans (finIndexEquiv (faceCornerCount_eq_fintype_card D.quad v).symm)

def vertexQuadAngle {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (v : Fin 8) (j : Fin (faceCornerCount D.quad v)) : ℝ :=
  D.angle ((vertexQuadCornerEquiv D v).symm j).val.1
    ((vertexQuadCornerEquiv D v).symm j).val.2

theorem vertexQuadAngle_sum {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (v : Fin 8) :
    (faceCornerCount D.tri v : ℝ)*D.alpha + ∑ j, vertexQuadAngle D v j = 2*Real.pi := by
  have hs : (∑ j, vertexQuadAngle D v j) = faceIncidentSum D.quad D.angle v := by
    rw [faceIncidentSum_eq_subtype_sum]
    exact Equiv.sum_comp (vertexQuadCornerEquiv D v).symm (fun p => D.angle p.val.1 p.val.2)
  rw [hs]
  exact D.angle_sum v

theorem vertexQuadAngle_bounds {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (v : Fin 8) (j : Fin (faceCornerCount D.quad v)) :
    vertexQuadAngle D v j ∈ Set.Ioo D.alpha (2*D.alpha) :=
  (D.corner_geometry hY hc _ _).1

theorem vertexQuadAngle_at_corner {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (f : Fin D.quadCount) (j : Fin 4) :
    vertexQuadAngle D (D.quad f j)
      (vertexQuadCornerEquiv D (D.quad f j) ⟨(f,j),D.corner_mem f j⟩) = D.angle f j := by
  simp only [vertexQuadAngle, Equiv.symm_apply_apply]

theorem rhombus_angles_assemble (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    let D := tiling_data_construct_existing_data Y c hY hc hcupper hirr hbound hne hsupport
    (∀ v, (Fintype.card (ContactNeighbor Y c v)=3 → faceCornerCount D.tri v≤1) ∧
      (Fintype.card (ContactNeighbor Y c v)=4 → faceCornerCount D.tri v≤3)) ∧
    (∀ f j, let v := D.quad f j
      (Fintype.card (ContactNeighbor Y c v)=4 → faceCornerCount D.tri v=3 → D.angle f j=D.beta) ∧
      (Fintype.card (ContactNeighbor Y c v)=4 → faceCornerCount D.tri v≤2 → D.angle f j<D.beta) ∧
      (Fintype.card (ContactNeighbor Y c v)=3 → faceCornerCount D.tri v=1 → D.beta<D.angle f j)) := by
  dsimp only
  let D := tiling_data_construct_existing_data Y c hY hc hcupper hirr hbound hne hsupport
  have hdegree (v : Fin 8) : faceCornerCount D.tri v + faceCornerCount D.quad v =
      Fintype.card (ContactNeighbor Y c v) := tiling_data_vertex_incidence Y c hY hc hcupper hirr hsupport v
  constructor
  · intro v
    exact rhombus_angles_triangle_incidence _ _ _ D.alpha (vertexQuadAngle D v)
      (equilateral_angle_Ioo c hc) (fun j => (vertexQuadAngle_bounds D hY hc v j).2)
      (vertexQuadAngle_sum D v) (hdegree v)
  · intro f j
    let v := D.quad f j
    have h := rhombus_angles_types (faceCornerCount D.tri v) (faceCornerCount D.quad v)
      D.alpha (vertexQuadAngle D v) (vertexQuadAngle_bounds D hY hc v) (vertexQuadAngle_sum D v)
    let idx := vertexQuadCornerEquiv D v ⟨(f,j),D.corner_mem f j⟩
    have heq : vertexQuadAngle D v idx = D.angle f j := vertexQuadAngle_at_corner D f j
    refine ⟨?_, ?_, ?_⟩
    · intro hd ht
      have hh := h.1 ((hdegree v).trans hd) ht idx
      rw [heq] at hh
      exact hh
    · intro hd ht
      have hh := h.2.1 ((hdegree v).trans hd) ht idx
      rw [heq] at hh
      exact hh
    · intro hd ht
      have hh := h.2.2 ((hdegree v).trans hd) ht idx
      rw [heq] at hh
      exact hh

#print axioms rhombus_angles_assemble
end Blueprint.Thomson.Tail.Implementation
