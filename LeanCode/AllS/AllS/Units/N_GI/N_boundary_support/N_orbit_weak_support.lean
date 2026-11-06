import AllS.Units.N_GI.N_boundary_support.N_next_dart

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_support_orbit_weak_support {Y : Fin 8 → Point} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) : C.WeakSupport := by
  obtain ⟨base, hbase, hbaseG, hinitial⟩ := boundary_support_initial_left_face Y c hY hc hcupper hbound hirr (C.point 0)
  let D := contactFaceRegion Y c base
  have hall (i : Fin (C.size + 1)) : FaceSupportsDart Y c D (C.point i) := by
    refine Fin.induction ?_ ?_ i
    · exact hinitial
    · intro j ih
      have hh := boundary_support_next_dart Y c hY hc hcupper hbound hirr base hbase hbaseG
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


#print axioms boundary_support_orbit_weak_support

end Blueprint.Thomson.Tail.Implementation
