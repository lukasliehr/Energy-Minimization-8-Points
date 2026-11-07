import AllS.Units.N_GI.N_rhombus_excess_lower.N_angle_interval

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_angles_opposite (c : ℝ) (Y : Fin 4 → Point) (j : Fin 4) :
    quadrilateralAngle c Y (j+2) = quadrilateralAngle c Y j := by
  fin_cases j <;> simp [quadrilateralAngle_alternates]

theorem rhombus_angles_alternating {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (f : Fin D.quadCount) :
    (∀ j, D.angle f j ∈ Set.Ioo D.alpha (2*D.alpha)) ∧
    (∀ j, D.angle f (j+2) = D.angle f j) ∧
    Real.tan (D.angle f 0 / 2) * Real.tan (D.angle f 1 / 2) = 1/c := by
  refine ⟨fun j => (D.corner_geometry hY hc f j).1, ?_, ?_⟩
  · exact fun j => rhombus_angles_opposite c (fun k => Y (D.quad f k)) j
  · have hne02 : Y (D.quad f 0) ≠ Y (D.quad f 2) :=
      fun h => (by decide : (0:Fin 4) ≠ 2) (D.quad_injective f (hY.2 h))
    have hne13 : Y (D.quad f 1) ≠ Y (D.quad f 3) :=
      fun h => (by decide : (1:Fin 4) ≠ 3) (D.quad_injective f (hY.2 h))
    have h := contact_rhombus_relation (fun k => Y (D.quad f k)) c
      (fun k => hY.1 _) hc hne02 hne13 (D.quad_contacts f 0)
      (D.quad_contacts f 1) (D.quad_contacts f 2) (D.quad_contacts f 3)
    simpa [ContactTilingData.angle, quadrilateralAngle, contactAngle_comm] using h.2.2

#print axioms rhombus_angles_alternating

end Blueprint.Thomson.Tail.Implementation
