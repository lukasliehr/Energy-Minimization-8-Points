import AllS.Units.N_AI.N_data.OutputInsertionGates
import AllS.Units.N_AI.N_correction_bounds.IntervalMatrixSupport
import AllS.Units.N_AI.N_fixed_tables.D12.Insertion

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def outputInsertion {r n : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (name : String) (v : Fin r → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k, v k * (outputEntryQ coordinates k name i.val j.val : ℝ)

theorem outputEntryQ_symm {r : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (k : Fin r) (name : String) (i j : ℕ) :
    outputEntryQ coordinates k name j i = outputEntryQ coordinates k name i j := by
  simp only [outputEntryQ, and_comm, or_comm]

theorem outputInsertion_symmetric {r n : ℕ}
    (coordinates : Fin r → String × ℕ × ℕ) (name : String) (v : Fin r → ℝ)
    (i j : Fin n) : outputInsertion coordinates name v i j =
      outputInsertion coordinates name v j i := by
  unfold outputInsertion
  simp only [outputEntryQ_symm coordinates _ name i.val j.val]

theorem outputInsertion_isHermitian {r n : ℕ}
    (coordinates : Fin r → String × ℕ × ℕ) (name : String) (v : Fin r → ℝ) :
    (outputInsertion (n := n) coordinates name v).IsHermitian := by
  ext i j
  exact outputInsertion_symmetric coordinates name v j i

def outputInsertionLinear {r n : ℕ} (coordinates : Fin r → String × ℕ × ℕ)
    (name : String) : (Fin r → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := outputInsertion coordinates name
  map_add' v w := by ext i j; simp [outputInsertion, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by ext i j; simp [outputInsertion, Finset.mul_sum, mul_assoc]

theorem outputInsertionIntervalSupport {r n : ℕ}
    (coordinates : Fin r → String × ℕ × ℕ) (name : String)
    (V : Fin r → QInterval) (v : Fin r → ℝ)
    (C : Matrix (Fin n) (Fin n) QInterval)
    (hv : ∀ k, (V k).asBox.Contains (v k))
    (hg : OutputInsertionGate coordinates name V C) :
    QMatrixContains C (outputInsertion coordinates name v) := by
  intro i j
  apply QInterval.subset_contains _ (hg i j)
  have h := QInterval.sum_contains _ _ (fun k =>
    QInterval.scale_contains (outputEntryQ coordinates k name i.val j.val) (hv k))
  simpa only [qOutputInsertion, outputInsertion, mul_comm] using h

theorem outputEntryQ_D12_cast (k : Fin 100) (name : String) (i j : ℕ) :
    (outputEntryQ FixedTables.D12.outputCoordinates k name i j : ℝ) =
      FixedTables.D12.outputEntry k name i j := by
  unfold outputEntryQ FixedTables.D12.outputEntry
  split_ifs <;> norm_num

theorem d12_insertionLinear_block (v : Fin 100 → ℝ)
    (b : Thomson.Finite.GramBlock 6) :
    (FixedTables.D12.insertionLinear v).val b =
      outputInsertion FixedTables.D12.outputCoordinates (FixedTables.D12.insertionBlockName b) v := by
  ext i j
  rw [FixedTables.D12.insertionLinear_entry]
  simp only [outputInsertion, outputEntryQ_D12_cast]

#print axioms outputInsertion_isHermitian
#print axioms outputInsertionLinear
#print axioms outputInsertionIntervalSupport
#print axioms d12_insertionLinear_block
end Blueprint.CAP
