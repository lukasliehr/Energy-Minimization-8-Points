import Blueprint.FiniteDefinitions
import Blueprint.RootBridge
import Blueprint.Target

/-! Multiplicity and node-order interface for the exact confluent algorithm.
Source: Certificates/Finite/kernel/hermite.py (order=(0,2,1,3,4));
Paper/Thomson8_All_s.tex:430-455. -/
noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

namespace Profile
def Valid (D : ℕ) (m : Fin 5 → ℕ) : Prop :=
  (∑ i, m i) = D + 1 ∧ ∀ i, i ≠ 0 → 0 < m i ∧ Even (m i)
end Profile

def canonicalNodes (a : ℝ) : Fin 5 → ℝ :=
  ![-1, contacts a 3, contacts a 1, contacts a 2, contacts a 0]

def sourceNodes (a : ℝ) : Fin 5 → ℝ :=
  ![contacts a 0, contacts a 2, contacts a 1, contacts a 3, -1]

def sourceNodeOrder : Equiv.Perm (Fin 5) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

theorem profile_interior_ge_two {D : ℕ} {m : Fin 5 → ℕ} (hm : Profile.Valid D m) (i : Fin 5) (hi : i ≠ 0) : 2 ≤ m i := by
  obtain ⟨hp, k, hk⟩ := hm.2 i hi
  omega
#check profile_interior_ge_two
#print axioms profile_interior_ge_two

theorem sourceNodes_eq_canonical (a : ℝ) : sourceNodes a = fun i => canonicalNodes a (sourceNodeOrder i) := by
  funext i
  fin_cases i <;> rfl
#check sourceNodes_eq_canonical
#print axioms sourceNodes_eq_canonical

theorem definitions_profile (D : ℕ) (m : Fin 5 → ℕ) (hm : Profile.Valid D m) : (∑ i, m i) = D + 1 ∧ (∀ i, i ≠ 0 → 2 ≤ m i ∧ Even (m i)) ∧ (∀ a : ℝ, sourceNodes a = fun i => canonicalNodes a (sourceNodeOrder i)) := by
  exact ⟨hm.1, fun i hi => ⟨profile_interior_ge_two hm i hi, (hm.2 i hi).2⟩,
    sourceNodes_eq_canonical⟩
#check definitions_profile
#print axioms definitions_profile
end Blueprint.Thomson.Finite

