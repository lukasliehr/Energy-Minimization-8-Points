import Lean_Code.InitialSupportingFace
import Lean_Code.BoundarySupportAssembly

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactBoundaryCycle

theorem weak_support_from_actual_face {Y : Fin 8 → ℝ³} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) : C.WeakSupport := by
  obtain ⟨base, hbase, hbaseG, hinitial⟩ := initial_supporting_face Y c hY hc hcupper hbound hirr (C.point 0)
  let D := contactFaceRegion Y c base
  have hall (i : Fin (C.size + 1)) : FaceSupportsDart Y c D (C.point i) := by
    refine Fin.induction ?_ ?_ i
    · exact hinitial
    · intro j ih
      have hh := face_supports_next_dart Y c hY hc hcupper hbound hirr base hbase hbaseG
        (C.point j.castSucc) ih
      rw [C.step] at hh
      have heq : j.castSucc + 1 = j.succ := by
        apply Fin.ext
        have hj := j.isLt
        have hsize : 1 < C.size + 1 := by omega
        simp [Fin.val_add, Nat.mod_eq_of_lt hsize,
          Nat.mod_eq_of_lt (show j.val + 1 < C.size + 1 by omega)]
      rwa [heq] at hh
  have hvertices (j : Fin (C.size + 1)) : Y (C.vertex j) ∈ D := by
    have hh := (hall j).1 0 ⟨le_rfl, zero_le_one⟩
    change shortSphereArc (Y (C.vertex j)) (Y (C.point j).2.val) 0 ∈ D at hh
    rwa [shortSphereArc_zero _ _ (hY.1 _)] at hh
  intro i j
  rw [C.vertex_next]
  exact (hall i).2 _ (hvertices j)

end ContactBoundaryCycle

/-- The actual contact boundaries have strict support, with their regions,
local models, convexity, and boundary propagation all constructed above. -/
theorem irreducible_boundary_support : IrreducibleBoundarySupport := by
  intro Y c hY hc hcupper hbound hirr hnonempty C
  exact C.strict_support_of_weak_support hirr hbound (C.weak_support_from_actual_face hcupper hbound hirr)

end SquareAntiprismVerification
