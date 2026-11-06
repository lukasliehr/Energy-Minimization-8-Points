import AllS.Units.N_FI.N_definitions.N_profile
import AllS.Units.N_FI.N_definitions.N_tags
import Blueprint.FiniteDefinitions
import Blueprint.RootBridge
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Exact primitive definitions, sorted coordinate enumeration and profile bounds. -/
def FiniteDefinitionsContract : Prop :=
  (∀ s : ℝ, 0 ≤ s → aS s ∈ Set.Ioo (0:ℝ) 1 ∧ F s (aS s) = 0) ∧
  (∀ a : ℝ, a ∈ Set.Ioo (0:ℝ) 1 → IsConfiguration (X a)) ∧
  (∀ D : ℕ, (invariantTagList D).Nodup ∧
    (∀ t, t ∈ invariantTagList D ↔ tagWeight t ≤ D) ∧
    sourceInvariantTagList D = invariantTagList D) ∧
  (∀ (D : ℕ) (m : Fin 5 → ℕ), Profile.Valid D m →
    (∑ i, m i) = D + 1 ∧ ∀ i : Fin 5, i ≠ 0 → 2 ≤ m i ∧ Even (m i))

theorem finiteDefinitions : FiniteDefinitionsContract := by
  refine ⟨aS_mem_and_root, candidate_is_configuration, ?_, ?_⟩
  · intro D
    exact ⟨invariantTagList_nodup D, fun _ => mem_invariantTagList,
      sourceInvariantTagList_eq D⟩
  · intro D m hm
    exact ⟨hm.1, fun i hi => ⟨profile_interior_ge_two hm i hi, (hm.2 i hi).2⟩⟩

#check finiteDefinitions
#print axioms finiteDefinitions
end Blueprint.Thomson.Finite
