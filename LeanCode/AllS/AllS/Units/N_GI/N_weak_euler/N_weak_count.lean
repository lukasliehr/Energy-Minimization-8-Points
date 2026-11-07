import AllS.Units.N_GI.N_weak_euler.N_joint_invariants
import AllS.Units.N_GI.N_weak_euler.N_permutation_bound
import Lean_Code.ContactEulerBound

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem weak_euler_weak_count (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hirr : PackingIrreducible c Y)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    2 * Fintype.card (ContactBoundaryOrbit Y c hY hc) + 12 ≤ Fintype.card (ContactDart Y c) := by
  have h := weak_euler_permutation_bound (contactReverse Y c) (contactRotate Y c hY hc).symm
    (contactBaseDart Y c hne 0) (weak_euler_joint_invariants Y c hY hc hcupper hirr hne)
  rw [permutation_orbit_symm_card, contact_rotation_orbit_count Y c hY hc hne] at h
  change Fintype.card (PermutationOrbit (contactReverse Y c)) + 8 +
    Fintype.card (ContactBoundaryOrbit Y c hY hc) ≤ Fintype.card (ContactDart Y c) + 2 at h
  have hD := contact_reverse_dart_count Y c
  omega

#print axioms weak_euler_weak_count

end Blueprint.Thomson.Tail.Implementation
