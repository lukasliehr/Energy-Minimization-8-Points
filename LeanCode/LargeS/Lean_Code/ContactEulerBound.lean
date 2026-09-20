import Lean_Code.ContactRotationInvariants
import Lean_Code.BoundaryCoverage
import Lean_Code.BoundaryPartition

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma involution_cycle_length {α : Type*} (e : Equiv.Perm α)
    (hinv : Function.Involutive e) (hne : ∀ x, e x ≠ x) (C : PermutationCycle e) :
    C.size + 1 = 2 := by
  have hn : 1 < C.size + 1 := by
    by_contra hn
    have hs : C.size = 0 := by omega
    have heq : (0 : Fin (C.size + 1)) + 1 = 0 := by apply Fin.ext; simp [hs]
    have h := C.step 0
    rw [heq] at h
    exact hne (C.point 0) h
  have hcycle : C.point ((0 + 1) + 1) = C.point 0 := by
    rw [← C.step, ← C.step]
    exact hinv (C.point 0)
  have hfin := C.injective hcycle
  have hval := congrArg Fin.val hfin
  have hmod : 2 % (C.size + 1) = 0 := by
    simpa [Fin.val_add, Nat.mod_eq_of_lt hn] using hval
  have hle := Nat.le_of_dvd (by decide : 0 < 2) (Nat.dvd_of_mod_eq_zero hmod)
  omega

theorem contact_reverse_dart_count (Y : Fin 8 → ℝ³) (c : ℝ) :
    Fintype.card (ContactDart Y c) = 2 * Fintype.card (PermutationOrbit (contactReverse Y c)) := by
  classical
  have hinv : Function.Involutive (contactReverse Y c) := fun _ => rfl
  have hne (d : ContactDart Y c) : contactReverse Y c d ≠ d := by
    intro h
    exact d.2.property.1 (congrArg Sigma.fst h)
  have hsum := sum_permutation_cycle_lengths (contactReverse Y c)
  simp only [involution_cycle_length (contactReverse Y c) hinv hne] at hsum
  simpa [mul_comm] using hsum.symm

/-- The Euler upper bound for the actual connected rotation system. This
is sufficient for the packing argument: its area inequality forces equality
in the relevant packing range. -/
theorem contact_euler_upper_bound (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    2 * Fintype.card (ContactBoundaryOrbit Y c hY hc) + 12 ≤ Fintype.card (ContactDart Y c) := by
  have h := connected_permutation_cycle_bound (contactReverse Y c) (contactRotate Y c hY hc).symm
    (contactBaseDart Y c hne 0) (contact_joint_invariants_constant Y c hY hc hcupper hirr hne)
  rw [permutation_orbit_symm_card, contact_rotation_orbit_count Y c hY hc hne] at h
  change Fintype.card (PermutationOrbit (contactReverse Y c)) + 8 +
    Fintype.card (ContactBoundaryOrbit Y c hY hc) ≤ Fintype.card (ContactDart Y c) + 2 at h
  have hD := contact_reverse_dart_count Y c
  omega

theorem contact_euler_upper_bound_of_support (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    2 * Fintype.card (ContactBoundaryOrbit Y c hY hc) + 12 ≤ Fintype.card (ContactDart Y c) := by
  exact contact_euler_upper_bound Y c hY hc hcupper hirr
    (no_isolated_vertices_of_boundary_support Y c hY hc hcupper hirr hbound hne hsupport)

end SquareAntiprismVerification
