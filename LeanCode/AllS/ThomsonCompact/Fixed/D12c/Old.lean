import ThomsonCompact.Fixed.D12c.Recovery
import ThomsonCompact.Fixed.D12c.OldSound
import ThomsonCompact.Fixed.D12c.OldRows0
import ThomsonCompact.Fixed.D12c.OldRows1
import ThomsonCompact.Fixed.D12c.OldRows2
import ThomsonCompact.Fixed.D12c.OldRows3
import ThomsonCompact.Fixed.D12c.OldRows4
import ThomsonCompact.Fixed.D12c.OldDen
import AllS.Units.N_AI.N_fixed_tables.D12.Insertion

/-!
# The compact D12 right inverse is the old one (workstream F4c)

Kernel-checked identification of `FixedD12` with the old `FixedTables.D12` data (exact equality of the decoded
coefficient lists, leaves `OldRows*`, `OldDen`) and the resulting equalities of the operators:

* `inverseMatrix_eq_old`, `outputCoordinates_eq_old`, `insertionBlockName_eq_old`, `retainedIndex_eq_old`,
  `insertionUnit_eq_old`, `insertionLinear_eq_old`, `inverseLinear_eq_old`, `correctionLinear_eq_old`;
* **`correctionLinear_full_recovery_old`**: the old full-recovery statement for the old `correctionLinear`, proven
  through the compact chain (imports only the old `Insertion` closure, not the old `FullRecovery` closure).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace ThomsonCompact.FixedD12

open Blueprint.CAP Blueprint.Thomson.Finite ThomsonCompact.Fixed ThomsonCompact.Packed
open ThomsonCompact.Fixed.D12c (ltab gtab slices)

theorem slices_eq : slices = [D12c.slice0, D12c.slice1, D12c.slice2, D12c.slice3, D12c.slice4, D12c.slice5,
    D12c.slice6, D12c.slice7] := rfl

/-- The stored `H` entries are the old literals. -/
theorem hC_eq_old (k i : Fin 100) : hC slices k.val i.val = FixedTables.D12.H k i := by
  have hrows : ∀ k, k < 100 → ∀ S ∈ slices, rowOldOk S k
      ((fun k m => if h : k < 100 ∧ m < 100 then FixedTables.D12.H ⟨k, h.1⟩ ⟨m, h.2⟩ else []) k) = true := by
    intro k hk S hS
    rw [slices_eq] at hS
    by_cases h0 : k < 20
    · exact rowsOldOk_spec _ _ 20 0 D12c.oldRows0 k (by omega) (by omega) S hS
    by_cases h1 : k < 40
    · exact rowsOldOk_spec _ _ 20 20 D12c.oldRows1 k (by omega) (by omega) S hS
    by_cases h2 : k < 60
    · exact rowsOldOk_spec _ _ 20 40 D12c.oldRows2 k (by omega) (by omega) S hS
    by_cases h3 : k < 80
    · exact rowsOldOk_spec _ _ 20 60 D12c.oldRows3 k (by omega) (by omega) S hS
    exact rowsOldOk_spec _ _ 20 80 D12c.oldRows4 k (by omega) (by omega) S hS
  have h := hC_old slices 100 _ (fun i hi => D12c.cover i hi) hrows k.val i.val k.isLt i.isLt
  rw [h]
  show (if hh : k.val < 100 ∧ i.val < 100 then FixedTables.D12.H ⟨k.val, hh.1⟩ ⟨i.val, hh.2⟩ else []) = _
  rw [dif_pos ⟨k.isLt, i.isLt⟩]

theorem den_eq_old (k : Fin 100) :
    FixedTables.D12.tableScales k = ((lamG gtab k.val : ℕ) : ℤ) ∧
    FixedTables.D12.tableDenominators k = (dzC gtab k.val).map (fun z : ℤ => (z : ℚ) / ((dqG gtab k.val : ℕ) : ℚ)) := by
  have h := List.all_eq_true.mp D12c.oldDen k.val (List.mem_range.mpr k.isLt)
  simp only [dif_pos k.isLt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.trans (by rw [dzK_eq]; rfl)⟩

theorem evalIntegerList_eq (l : List ℤ) (a : ℝ) : evalIntegerList l a = evalZ l a := by
  unfold evalIntegerList
  induction l with
  | nil => rw [listPolynomial_nil, Polynomial.eval₂_zero]; rfl
  | cons c l ih =>
    rw [listPolynomial_cons, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, ih,
      eq_intCast]
    simp [evalZ]

theorem evalRationalList_div (dz : List ℤ) (dq : ℕ) (a : ℝ) :
    evalRationalList (dz.map fun z : ℤ => (z : ℚ) / (dq : ℚ)) a = evalZ dz a / dq := by
  induction dz with
  | nil => simp [evalRationalList, evalZ]
  | cons c l ih =>
    simp only [List.map_cons, evalRationalList]
    rw [ih]
    simp only [evalZ, List.map_cons, horner_cons]
    push_cast
    ring

theorem div_identity (q x l d : ℝ) : q * x / (l * d) = x / (l * (d / q)) := by
  rw [← mul_div_assoc, div_div_eq_mul_div, mul_comm x q]

/-- **The compact D12 right inverse equals the old one** (all `a`). -/
theorem inverseMatrix_eq_old (a : ℝ) : inverseMatrix a = FixedTables.D12.inverseMatrix a := by
  ext k i
  obtain ⟨hs, hd⟩ := den_eq_old k
  simp only [inverseMatrix, FixedTables.D12.inverseMatrix, hs, hd, ← hC_eq_old k i, evalIntegerList_eq,
    evalRationalList_div]
  push_cast
  exact div_identity _ _ _ _

theorem outputCoordinates_eq_old : outputCoordinates = FixedTables.D12.outputCoordinates := by
  funext k
  revert k
  decide +kernel

theorem insertionBlockName_eq_old : insertionBlockName = FixedTables.D12.insertionBlockName := by
  funext b
  rcases b with k | b
  · rfl
  · cases b <;> rfl

theorem retainedIndex_eq_old : retainedIndex = FixedTables.D12.retainedIndex := rfl

theorem retainedVector_eq (a : ℝ) (f : Compatible a 12) :
    retainedVector a f = fun i => retainCompatible a 12 f (FixedTables.D12.retainedIndex i) := rfl

theorem insertionUnit_eq_old (j : Fin 100) : insertionUnit j = FixedTables.D12.insertionUnit j := by
  apply Subtype.ext
  funext b r c
  show outputEntry j (insertionBlockName b) r.val c.val =
    FixedTables.D12.outputEntry j (FixedTables.D12.insertionBlockName b) r.val c.val
  rw [insertionBlockName_eq_old]
  simp only [outputEntry, FixedTables.D12.outputEntry, outputCoordinates_eq_old]

theorem insertionLinear_eq_old : insertionLinear = FixedTables.D12.insertionLinear := by
  apply LinearMap.ext
  intro v
  rw [insertionLinear_apply, FixedTables.D12.insertionLinear_apply]
  simp only [insertionUnit_eq_old]

theorem inverseLinear_eq_old (a : ℝ) : inverseLinear a = FixedTables.D12.inverseLinear a := by
  apply LinearMap.ext
  intro v
  show (inverseMatrix a).mulVec v = (FixedTables.D12.inverseMatrix a).mulVec v
  rw [inverseMatrix_eq_old]

theorem correctionLinear_eq_old (a : ℝ) : correctionLinear a = FixedTables.D12.correctionLinear a := by
  show insertionLinear.comp (inverseLinear a) = FixedTables.D12.insertionLinear.comp (FixedTables.D12.inverseLinear a)
  rw [insertionLinear_eq_old, inverseLinear_eq_old]

/-- **Full recovery for the old D12 operator**, proven through the compact chain: the statement of the old
`FixedTables.D12.correctionLinear_full_recovery` (with `retainedVector` unfolded to the old `retainedIndex`). -/
theorem correctionLinear_full_recovery_old (a : ℝ) (ha : physical a) (p : MomentPivots 6) (hp : ValidMomentPivots p)
    (hp0 : (p 0).val = 0) (hp1 : (p 1).val = 3) (f : Compatible a 12) :
    gramPoly a 6 p (FixedTables.D12.correctionLinear a
      (fun i => retainCompatible a 12 f (FixedTables.D12.retainedIndex i))) = f.val := by
  rw [← correctionLinear_eq_old, ← retainedVector_eq]
  exact correctionLinear_full_recovery a ha p hp hp0 hp1 f

#print axioms inverseMatrix_eq_old
#print axioms outputCoordinates_eq_old
#print axioms correctionLinear_eq_old
#print axioms correctionLinear_full_recovery_old

end ThomsonCompact.FixedD12
