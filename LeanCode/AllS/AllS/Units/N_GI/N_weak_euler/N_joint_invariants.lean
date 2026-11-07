import AllS.Units.N_GI.N_components.N_component_unique
import AllS.Units.N_GI.N_weak_euler.N_rotation_constant

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem weak_euler_joint_invariants (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hirr : PackingIrreducible c Y)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
    (v : EuclideanSpace ℝ (ContactDart Y c))
    (hrev : ∀ d, v (contactReverse Y c d) = v d)
    (hrot : ∀ d, v ((contactRotate Y c hY hc).symm d) = v d) :
    ∀ d e, v d = v e := by
  have hrot' (d : ContactDart Y c) : v (contactRotate Y c hY hc d) = v d := by
    simpa only [Equiv.symm_apply_apply] using (hrot (contactRotate Y c hY hc d)).symm
  let g : Fin 8 → ℝ := fun i => v (contactBaseDart Y c hne i)
  have hbase (d : ContactDart Y c) : v d = g d.1 :=
    weak_euler_rotation_constant Y c hY hc v hrot' d.1 d.2 (contactBaseDart Y c hne d.1).2
  have hadj (i j : Fin 8) (hij : ContactAdj Y c i j) : g i = g j := by
    let d : ContactDart Y c := ⟨i, ⟨j, hij.1.symm, hij.2⟩⟩
    exact (hbase d).symm.trans ((hrev d).symm.trans (hbase (contactReverse Y c d)))
  have hne' (i : Fin 8) : ∃ j, ContactAdj Y c i j := by
    obtain ⟨j, hj, hc⟩ := hne i
    exact ⟨j, hj.symm, hc⟩
  have hpath (i j : Fin 8) : ContactReachable Y c i j := by
    apply (mem_contactComponent Y c i j).mp
    rw [components_component_unique Y c hY.1 hc.1 hcupper hirr i j (hne' i) (hne' j)]
    exact contactComponent_root Y c j
  have hg (i j : Fin 8) : g i = g j := by
    have hp := hpath i j
    induction hp with
    | refl => rfl
    | tail hpath hstep ih => exact ih.trans (hadj _ _ hstep)
  intro d e
  exact (hbase d).trans ((hg d.1 e.1).trans (hbase e).symm)

#print axioms weak_euler_joint_invariants

end Blueprint.Thomson.Tail.Implementation
