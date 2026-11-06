import AllS.Units.N_AI.N_fixed_tables.GramInsertionSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- A physical Gram coordinate has value one in its selected symmetric
positions, including just one copy when the coordinate is diagonal. -/
theorem fixedSymmetricUnit_apply {n : ℕ} (i j r c : Fin n) :
    fixedSymmetricUnit i j r c =
      if (r=i ∧ c=j) ∨ (r=j ∧ c=i) then (1:ℝ) else 0 := by
  by_cases hij : i=j
  · subst j
    by_cases hrc : r=i ∧ c=i <;>
      norm_num [fixedSymmetricUnit,physicalSymmetricEntry,hrc,smul_eq_mul]
  · by_cases hrc : r=i ∧ c=j
    · rcases hrc with ⟨rfl,rfl⟩
      simp [fixedSymmetricUnit,physicalSymmetricEntry,hij,Ne.symm hij,smul_eq_mul]
    · by_cases hcr : r=j ∧ c=i <;>
        simp [fixedSymmetricUnit,physicalSymmetricEntry,hij,hrc,hcr,smul_eq_mul]

theorem fixedGramUnit_same_block {d : ℕ} (b : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) :
    (fixedGramUnit b i j).val b = fixedSymmetricUnit i j := by
  classical
  simp [fixedGramUnit,fixedSingleGram]

theorem fixedGramUnit_other_block {d : ℕ} (b c : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) (hc : c≠b) :
    (fixedGramUnit b i j).val c = 0 := by
  classical
  simp [fixedGramUnit,fixedSingleGram,Pi.single_eq_of_ne hc]

theorem fixedGramUnit_same_block_apply {d : ℕ} (b : GramBlock d)
    (i j r c : Fin (gramBlockDimension d b)) :
    (fixedGramUnit b i j).val b r c =
      if (r=i ∧ c=j) ∨ (r=j ∧ c=i) then (1:ℝ) else 0 := by
  rw [fixedGramUnit_same_block,fixedSymmetricUnit_apply]

def gramEntryLinear {d : ℕ} (b : GramBlock d)
    (r c : Fin (gramBlockDimension d b)) : GramFamily d →ₗ[ℝ] ℝ where
  toFun W := W.val b r c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Entrywise semantics of any linear combination of actual Gram families. -/
theorem fixedGramCombination_apply {n d : ℕ} (U : Fin n → GramFamily d)
    (v : Fin n → ℝ) (b : GramBlock d) (r c : Fin (gramBlockDimension d b)) :
    (∑ j,v j • U j).val b r c = ∑ j,v j*(U j).val b r c := by
  change gramEntryLinear b r c (∑ j,v j • U j) = _
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

#print axioms fixedGramUnit_same_block_apply
#print axioms fixedGramUnit_other_block
#print axioms fixedGramCombination_apply
end Blueprint.Thomson.Finite
