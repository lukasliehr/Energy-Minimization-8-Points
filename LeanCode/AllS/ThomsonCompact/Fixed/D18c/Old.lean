import ThomsonCompact.Fixed.D18c.Recovery
import ThomsonCompact.Fixed.D12c.OldSound
import ThomsonCompact.Fixed.D18c.OldRows0
import ThomsonCompact.Fixed.D18c.OldRows1
import ThomsonCompact.Fixed.D18c.OldRows2
import ThomsonCompact.Fixed.D18c.OldRows3
import ThomsonCompact.Fixed.D18c.OldRows4
import ThomsonCompact.Fixed.D18c.OldRows5
import ThomsonCompact.Fixed.D18c.OldRows6
import ThomsonCompact.Fixed.D18c.OldRows7
import ThomsonCompact.Fixed.D18c.OldRows8
import ThomsonCompact.Fixed.D18c.OldRows9
import ThomsonCompact.Fixed.D18c.OldRows10
import ThomsonCompact.Fixed.D18c.OldRows11
import ThomsonCompact.Fixed.D18c.OldRows12
import ThomsonCompact.Fixed.D18c.OldRows13
import ThomsonCompact.Fixed.D18c.OldRows14
import ThomsonCompact.Fixed.D18c.OldRows15
import ThomsonCompact.Fixed.D18c.OldRows16
import ThomsonCompact.Fixed.D18c.OldRows17
import ThomsonCompact.Fixed.D18c.OldRows18
import ThomsonCompact.Fixed.D18c.OldRows19
import ThomsonCompact.Fixed.D18c.OldRows20
import ThomsonCompact.Fixed.D18c.OldRows21
import ThomsonCompact.Fixed.D18c.OldRows22
import ThomsonCompact.Fixed.D18c.OldRows23
import ThomsonCompact.Fixed.D18c.OldRows24
import ThomsonCompact.Fixed.D18c.OldRows25
import ThomsonCompact.Fixed.D18c.OldRows26
import ThomsonCompact.Fixed.D18c.OldRows27
import ThomsonCompact.Fixed.D18c.OldRows28
import ThomsonCompact.Fixed.D18c.OldRows29
import ThomsonCompact.Fixed.D18c.OldRows30
import ThomsonCompact.Fixed.D18c.OldDen
import AllS.Units.N_AI.N_fixed_tables.D18.Insertion

/-!
# The compact D18 right inverse is the old one (workstream F4c)

Kernel-checked identification of `FixedD18` with the old `FixedTables.D18` data (exact equality of the decoded
coefficient lists, leaves `OldRows*`, `OldDen`) and the resulting equalities of the operators:

* `inverseMatrix_eq_old`, `outputCoordinates_eq_old`, `insertionBlockName_eq_old`, `retainedIndex_eq_old`,
  `insertionUnit_eq_old`, `insertionLinear_eq_old`, `inverseLinear_eq_old`, `correctionLinear_eq_old`;
* **`correctionLinear_full_recovery_old`**: the old full-recovery statement for the old `correctionLinear`, proven
  through the compact chain (imports only the old `Insertion` closure, not the old `FullRecovery` closure).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace ThomsonCompact.FixedD18

open Blueprint.CAP Blueprint.Thomson.Finite ThomsonCompact.Fixed ThomsonCompact.Packed
open ThomsonCompact.Fixed.D18c (ltab gtab slices)

theorem slices_eq : slices = [D18c.slice0, D18c.slice1, D18c.slice2, D18c.slice3, D18c.slice4, D18c.slice5, D18c.slice6, D18c.slice7, D18c.slice8, D18c.slice9, D18c.slice10, D18c.slice11, D18c.slice12, D18c.slice13, D18c.slice14, D18c.slice15, D18c.slice16, D18c.slice17, D18c.slice18, D18c.slice19] := rfl

/-- Old row `k` (`[]` outside the table). -/
noncomputable def Hrow (k : Nat) : Fin 272 → List Int :=
  if h : k < 272 then FixedTables.D18.H ⟨k, h⟩ else fun _ => []

theorem oldG0_eq (k : Nat) (h1 : 0 ≤ k) (h2 : k < 6) : D18c.oldG0 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG1_eq (k : Nat) (h1 : 6 ≤ k) (h2 : k < 13) : D18c.oldG1 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG2_eq (k : Nat) (h1 : 13 ≤ k) (h2 : k < 17) : D18c.oldG2 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG3_eq (k : Nat) (h1 : 17 ≤ k) (h2 : k < 20) : D18c.oldG3 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG4_eq (k : Nat) (h1 : 20 ≤ k) (h2 : k < 23) : D18c.oldG4 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG5_eq (k : Nat) (h1 : 23 ≤ k) (h2 : k < 27) : D18c.oldG5 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG6_eq (k : Nat) (h1 : 27 ≤ k) (h2 : k < 30) : D18c.oldG6 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG7_eq (k : Nat) (h1 : 30 ≤ k) (h2 : k < 33) : D18c.oldG7 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG8_eq (k : Nat) (h1 : 33 ≤ k) (h2 : k < 36) : D18c.oldG8 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG9_eq (k : Nat) (h1 : 36 ≤ k) (h2 : k < 39) : D18c.oldG9 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG10_eq (k : Nat) (h1 : 39 ≤ k) (h2 : k < 46) : D18c.oldG10 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG11_eq (k : Nat) (h1 : 46 ≤ k) (h2 : k < 58) : D18c.oldG11 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG12_eq (k : Nat) (h1 : 58 ≤ k) (h2 : k < 70) : D18c.oldG12 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG13_eq (k : Nat) (h1 : 70 ≤ k) (h2 : k < 82) : D18c.oldG13 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG14_eq (k : Nat) (h1 : 82 ≤ k) (h2 : k < 94) : D18c.oldG14 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG15_eq (k : Nat) (h1 : 94 ≤ k) (h2 : k < 106) : D18c.oldG15 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG16_eq (k : Nat) (h1 : 106 ≤ k) (h2 : k < 118) : D18c.oldG16 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG17_eq (k : Nat) (h1 : 118 ≤ k) (h2 : k < 130) : D18c.oldG17 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG18_eq (k : Nat) (h1 : 130 ≤ k) (h2 : k < 142) : D18c.oldG18 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG19_eq (k : Nat) (h1 : 142 ≤ k) (h2 : k < 154) : D18c.oldG19 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG20_eq (k : Nat) (h1 : 154 ≤ k) (h2 : k < 166) : D18c.oldG20 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG21_eq (k : Nat) (h1 : 166 ≤ k) (h2 : k < 178) : D18c.oldG21 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG22_eq (k : Nat) (h1 : 178 ≤ k) (h2 : k < 190) : D18c.oldG22 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG23_eq (k : Nat) (h1 : 190 ≤ k) (h2 : k < 202) : D18c.oldG23 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG24_eq (k : Nat) (h1 : 202 ≤ k) (h2 : k < 214) : D18c.oldG24 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG25_eq (k : Nat) (h1 : 214 ≤ k) (h2 : k < 226) : D18c.oldG25 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG26_eq (k : Nat) (h1 : 226 ≤ k) (h2 : k < 238) : D18c.oldG26 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG27_eq (k : Nat) (h1 : 238 ≤ k) (h2 : k < 250) : D18c.oldG27 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG28_eq (k : Nat) (h1 : 250 ≤ k) (h2 : k < 262) : D18c.oldG28 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG29_eq (k : Nat) (h1 : 262 ≤ k) (h2 : k < 271) : D18c.oldG29 k = Hrow k := by
  interval_cases k <;> rfl

theorem oldG30_eq (k : Nat) (h1 : 271 ≤ k) (h2 : k < 272) : D18c.oldG30 k = Hrow k := by
  interval_cases k <;> rfl

/-- The stored `H` entries are the old literals. -/
theorem hC_eq_old (k i : Fin 272) : hC slices k.val i.val = FixedTables.D18.H k i := by
  have hrows : ∀ k, k < 272 → ∀ S ∈ slices, rowOldOk S k
      ((fun k m => if h : m < 272 then Hrow k ⟨m, h⟩ else []) k) = true := by
    intro k hk S hS
    rw [slices_eq] at hS
    by_cases c0 : k < 6
    · have h := rowsOldOk_spec _ _ 6 0 D18c.oldRows0 k (by omega) (by omega) S hS
      rw [oldG0_eq k (by omega) (by omega)] at h
      exact h
    by_cases c1 : k < 13
    · have h := rowsOldOk_spec _ _ 7 6 D18c.oldRows1 k (by omega) (by omega) S hS
      rw [oldG1_eq k (by omega) (by omega)] at h
      exact h
    by_cases c2 : k < 17
    · have h := rowsOldOk_spec _ _ 4 13 D18c.oldRows2 k (by omega) (by omega) S hS
      rw [oldG2_eq k (by omega) (by omega)] at h
      exact h
    by_cases c3 : k < 20
    · have h := rowsOldOk_spec _ _ 3 17 D18c.oldRows3 k (by omega) (by omega) S hS
      rw [oldG3_eq k (by omega) (by omega)] at h
      exact h
    by_cases c4 : k < 23
    · have h := rowsOldOk_spec _ _ 3 20 D18c.oldRows4 k (by omega) (by omega) S hS
      rw [oldG4_eq k (by omega) (by omega)] at h
      exact h
    by_cases c5 : k < 27
    · have h := rowsOldOk_spec _ _ 4 23 D18c.oldRows5 k (by omega) (by omega) S hS
      rw [oldG5_eq k (by omega) (by omega)] at h
      exact h
    by_cases c6 : k < 30
    · have h := rowsOldOk_spec _ _ 3 27 D18c.oldRows6 k (by omega) (by omega) S hS
      rw [oldG6_eq k (by omega) (by omega)] at h
      exact h
    by_cases c7 : k < 33
    · have h := rowsOldOk_spec _ _ 3 30 D18c.oldRows7 k (by omega) (by omega) S hS
      rw [oldG7_eq k (by omega) (by omega)] at h
      exact h
    by_cases c8 : k < 36
    · have h := rowsOldOk_spec _ _ 3 33 D18c.oldRows8 k (by omega) (by omega) S hS
      rw [oldG8_eq k (by omega) (by omega)] at h
      exact h
    by_cases c9 : k < 39
    · have h := rowsOldOk_spec _ _ 3 36 D18c.oldRows9 k (by omega) (by omega) S hS
      rw [oldG9_eq k (by omega) (by omega)] at h
      exact h
    by_cases c10 : k < 46
    · have h := rowsOldOk_spec _ _ 7 39 D18c.oldRows10 k (by omega) (by omega) S hS
      rw [oldG10_eq k (by omega) (by omega)] at h
      exact h
    by_cases c11 : k < 58
    · have h := rowsOldOk_spec _ _ 12 46 D18c.oldRows11 k (by omega) (by omega) S hS
      rw [oldG11_eq k (by omega) (by omega)] at h
      exact h
    by_cases c12 : k < 70
    · have h := rowsOldOk_spec _ _ 12 58 D18c.oldRows12 k (by omega) (by omega) S hS
      rw [oldG12_eq k (by omega) (by omega)] at h
      exact h
    by_cases c13 : k < 82
    · have h := rowsOldOk_spec _ _ 12 70 D18c.oldRows13 k (by omega) (by omega) S hS
      rw [oldG13_eq k (by omega) (by omega)] at h
      exact h
    by_cases c14 : k < 94
    · have h := rowsOldOk_spec _ _ 12 82 D18c.oldRows14 k (by omega) (by omega) S hS
      rw [oldG14_eq k (by omega) (by omega)] at h
      exact h
    by_cases c15 : k < 106
    · have h := rowsOldOk_spec _ _ 12 94 D18c.oldRows15 k (by omega) (by omega) S hS
      rw [oldG15_eq k (by omega) (by omega)] at h
      exact h
    by_cases c16 : k < 118
    · have h := rowsOldOk_spec _ _ 12 106 D18c.oldRows16 k (by omega) (by omega) S hS
      rw [oldG16_eq k (by omega) (by omega)] at h
      exact h
    by_cases c17 : k < 130
    · have h := rowsOldOk_spec _ _ 12 118 D18c.oldRows17 k (by omega) (by omega) S hS
      rw [oldG17_eq k (by omega) (by omega)] at h
      exact h
    by_cases c18 : k < 142
    · have h := rowsOldOk_spec _ _ 12 130 D18c.oldRows18 k (by omega) (by omega) S hS
      rw [oldG18_eq k (by omega) (by omega)] at h
      exact h
    by_cases c19 : k < 154
    · have h := rowsOldOk_spec _ _ 12 142 D18c.oldRows19 k (by omega) (by omega) S hS
      rw [oldG19_eq k (by omega) (by omega)] at h
      exact h
    by_cases c20 : k < 166
    · have h := rowsOldOk_spec _ _ 12 154 D18c.oldRows20 k (by omega) (by omega) S hS
      rw [oldG20_eq k (by omega) (by omega)] at h
      exact h
    by_cases c21 : k < 178
    · have h := rowsOldOk_spec _ _ 12 166 D18c.oldRows21 k (by omega) (by omega) S hS
      rw [oldG21_eq k (by omega) (by omega)] at h
      exact h
    by_cases c22 : k < 190
    · have h := rowsOldOk_spec _ _ 12 178 D18c.oldRows22 k (by omega) (by omega) S hS
      rw [oldG22_eq k (by omega) (by omega)] at h
      exact h
    by_cases c23 : k < 202
    · have h := rowsOldOk_spec _ _ 12 190 D18c.oldRows23 k (by omega) (by omega) S hS
      rw [oldG23_eq k (by omega) (by omega)] at h
      exact h
    by_cases c24 : k < 214
    · have h := rowsOldOk_spec _ _ 12 202 D18c.oldRows24 k (by omega) (by omega) S hS
      rw [oldG24_eq k (by omega) (by omega)] at h
      exact h
    by_cases c25 : k < 226
    · have h := rowsOldOk_spec _ _ 12 214 D18c.oldRows25 k (by omega) (by omega) S hS
      rw [oldG25_eq k (by omega) (by omega)] at h
      exact h
    by_cases c26 : k < 238
    · have h := rowsOldOk_spec _ _ 12 226 D18c.oldRows26 k (by omega) (by omega) S hS
      rw [oldG26_eq k (by omega) (by omega)] at h
      exact h
    by_cases c27 : k < 250
    · have h := rowsOldOk_spec _ _ 12 238 D18c.oldRows27 k (by omega) (by omega) S hS
      rw [oldG27_eq k (by omega) (by omega)] at h
      exact h
    by_cases c28 : k < 262
    · have h := rowsOldOk_spec _ _ 12 250 D18c.oldRows28 k (by omega) (by omega) S hS
      rw [oldG28_eq k (by omega) (by omega)] at h
      exact h
    by_cases c29 : k < 271
    · have h := rowsOldOk_spec _ _ 9 262 D18c.oldRows29 k (by omega) (by omega) S hS
      rw [oldG29_eq k (by omega) (by omega)] at h
      exact h
    have h := rowsOldOk_spec _ _ 1 271 D18c.oldRows30 k (by omega) (by omega) S hS
    rw [oldG30_eq k (by omega) (by omega)] at h
    exact h
  have h := hC_old slices 272 _ (fun i hi => D18c.cover i hi) hrows k.val i.val k.isLt i.isLt
  rw [h]
  show (if hh : i.val < 272 then Hrow k.val ⟨i.val, hh⟩ else []) = _
  rw [dif_pos i.isLt]
  unfold Hrow
  rw [dif_pos k.isLt]

theorem den_eq_old (k : Fin 272) :
    FixedTables.D18.tableScales k = ((lamG gtab k.val : ℕ) : ℤ) ∧
    FixedTables.D18.tableDenominators k = (dzC gtab k.val).map (fun z : ℤ => (z : ℚ) / ((dqG gtab k.val : ℕ) : ℚ)) := by
  have h := List.all_eq_true.mp D18c.oldDen k.val (List.mem_range.mpr k.isLt)
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

/-- **The compact D18 right inverse equals the old one** (all `a`). -/
theorem inverseMatrix_eq_old (a : ℝ) : inverseMatrix a = FixedTables.D18.inverseMatrix a := by
  ext k i
  obtain ⟨hs, hd⟩ := den_eq_old k
  simp only [inverseMatrix, FixedTables.D18.inverseMatrix, hs, hd, ← hC_eq_old k i, evalIntegerList_eq,
    evalRationalList_div]
  push_cast
  exact div_identity _ _ _ _

theorem outputCoordinates_eq_old : outputCoordinates = FixedTables.D18.outputCoordinates := by
  funext k
  revert k
  decide +kernel

theorem insertionBlockName_eq_old : insertionBlockName = FixedTables.D18.insertionBlockName := by
  funext b
  rcases b with k | b
  · rfl
  · cases b <;> rfl

theorem retainedIndex_eq_old : retainedIndex = FixedTables.D18.retainedIndex := rfl

theorem retainedVector_eq (a : ℝ) (f : Compatible a 18) :
    retainedVector a f = fun i => retainCompatible a 18 f (FixedTables.D18.retainedIndex i) := rfl

theorem insertionUnit_eq_old (j : Fin 272) : insertionUnit j = FixedTables.D18.insertionUnit j := by
  apply Subtype.ext
  funext b r c
  show outputEntry j (insertionBlockName b) r.val c.val =
    FixedTables.D18.outputEntry j (FixedTables.D18.insertionBlockName b) r.val c.val
  rw [insertionBlockName_eq_old]
  simp only [outputEntry, FixedTables.D18.outputEntry, outputCoordinates_eq_old]

theorem insertionLinear_eq_old : insertionLinear = FixedTables.D18.insertionLinear := by
  apply LinearMap.ext
  intro v
  rw [insertionLinear_apply, FixedTables.D18.insertionLinear_apply]
  simp only [insertionUnit_eq_old]

theorem inverseLinear_eq_old (a : ℝ) : inverseLinear a = FixedTables.D18.inverseLinear a := by
  apply LinearMap.ext
  intro v
  show (inverseMatrix a).mulVec v = (FixedTables.D18.inverseMatrix a).mulVec v
  rw [inverseMatrix_eq_old]

theorem correctionLinear_eq_old (a : ℝ) : correctionLinear a = FixedTables.D18.correctionLinear a := by
  show insertionLinear.comp (inverseLinear a) = FixedTables.D18.insertionLinear.comp (FixedTables.D18.inverseLinear a)
  rw [insertionLinear_eq_old, inverseLinear_eq_old]

/-- **Full recovery for the old D18 operator**, proven through the compact chain: the statement of the old
`FixedTables.D18.correctionLinear_full_recovery` (with `retainedVector` unfolded to the old `retainedIndex`). -/
theorem correctionLinear_full_recovery_old (a : ℝ) (ha : physical a) (p : MomentPivots 9) (hp : ValidMomentPivots p)
    (hp0 : (p 0).val = 0) (hp1 : (p 1).val = 1) (f : Compatible a 18) :
    gramPoly a 9 p (FixedTables.D18.correctionLinear a
      (fun i => retainCompatible a 18 f (FixedTables.D18.retainedIndex i))) = f.val := by
  rw [← correctionLinear_eq_old, ← retainedVector_eq]
  exact correctionLinear_full_recovery a ha p hp hp0 hp1 f

#print axioms inverseMatrix_eq_old
#print axioms outputCoordinates_eq_old
#print axioms correctionLinear_eq_old
#print axioms correctionLinear_full_recovery_old

end ThomsonCompact.FixedD18
