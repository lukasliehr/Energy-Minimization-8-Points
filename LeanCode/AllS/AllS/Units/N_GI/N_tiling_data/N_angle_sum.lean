import AllS.Units.N_GI.N_tiling_data.N_partition_by_length
import AllS.Units.N_GI.N_covering.N_no_rattlers

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem tiling_data_angle_sum (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    (faceCornerCount (boundaryArray Y c hY hc 3) v : ℝ) * Real.arccos (c / (1 + c)) +
      faceIncidentSum (boundaryArray Y c hY hc 4)
        (fun f j => quadrilateralAngle c (fun k => Y (boundaryArray Y c hY hc 4 f k)) j) v =
      2 * Real.pi := by
  classical
  have htri (f) (j : Fin 3) :
      contactAngle c (Y (boundaryArray Y c hY hc 3 f (j + 1)))
        (Y (boundaryArray Y c hY hc 3 f (j - 1))) = Real.arccos (c / (1 + c)) := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_triangle_angle
  have hquad (f) (j : Fin 4) :
      contactAngle c (Y (boundaryArray Y c hY hc 4 f (j + 1)))
        (Y (boundaryArray Y c hY hc 4 f (j - 1))) =
      quadrilateralAngle c (fun k => Y (boundaryArray Y c hY hc 4 f k)) j := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_quadrilateral_angle
  have h3 := boundaryArray_corner_sum Y c hY hc 3 v
  have h4 := boundaryArray_corner_sum Y c hY hc 4 v
  simp_rw [htri] at h3
  simp_rw [hquad] at h4
  rw [← faceIncidentSum_eq_indicator, faceIncidentSum_const] at h3
  rw [← faceIncidentSum_eq_indicator] at h4
  rw [h3, h4, tiling_data_partition_by_length Y c hY hc hcupper hirr hsupport
    (fun f => boundaryCornerSum (boundaryOrbitCycle Y c hY hc f) v)]
  exact boundary_corner_sum_at_vertex Y c hY hc hirr v
    (covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport v)

#print axioms tiling_data_angle_sum

end Blueprint.Thomson.Tail.Implementation
