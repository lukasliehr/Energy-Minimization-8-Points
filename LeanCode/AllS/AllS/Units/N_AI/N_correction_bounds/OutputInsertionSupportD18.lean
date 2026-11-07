import AllS.Units.N_AI.N_correction_bounds.OutputInsertionSupport
import AllS.Units.N_AI.N_fixed_tables.D18.Insertion

noncomputable section
namespace Blueprint.CAP

theorem outputEntryQ_D18_cast (k : Fin 272) (name : String) (i j : ℕ) :
    (outputEntryQ FixedTables.D18.outputCoordinates k name i j : ℝ) =
      FixedTables.D18.outputEntry k name i j := by
  unfold outputEntryQ FixedTables.D18.outputEntry
  split_ifs <;> norm_num

theorem d18_insertionLinear_block (v : Fin 272 → ℝ)
    (b : Thomson.Finite.GramBlock 9) :
    (FixedTables.D18.insertionLinear v).val b =
      outputInsertion FixedTables.D18.outputCoordinates
        (FixedTables.D18.insertionBlockName b) v := by
  ext i j
  rw [FixedTables.D18.insertionLinear_entry]
  simp only [outputInsertion, outputEntryQ_D18_cast]

#print axioms outputEntryQ_D18_cast
#print axioms d18_insertionLinear_block
end Blueprint.CAP
