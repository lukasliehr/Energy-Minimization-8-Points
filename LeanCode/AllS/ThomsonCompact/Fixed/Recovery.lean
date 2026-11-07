import AllS.Units.N_AI.N_fixed_tables.RetainedGramSupport
import AllS.Units.N_AI.N_fixed_tables.LinearSupport

/-!
# Degree-generic full recovery from a fixed right inverse (workstream F4, item v)

The old `FixedTables.D18.correctionLinear_full_recovery` chain (`Operator` + `FullRecovery`), parametrized by
the table data so that D14, D16 (and compact D12/D18) reuse it:

* `idx : Fin n → RetainedIndex (2d)` a bijection (the table's retained coordinate order),
* `U j : GramFamily d` the inserted Gram units and `P j : Poly3` source polynomials with
  `invariantSubst (P j) = gramPoly a d p (U j)` (canonical columns),
* `Dinv` with `C · Dinv = 1` for the coefficient matrix `C i j = coeff (idx i) (P j)`.

Then `Σ_j (Dinv r)_j • U j` recovers every compatible `f` with retained vector `r`.
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.Fixed

open Blueprint.CAP Blueprint.Thomson.Finite

/-- The coefficient matrix of the source columns at the retained coordinates. -/
def coefMatrix {n : ℕ} {D : ℕ} (idx : Fin n → RetainedIndex D) (P : Fin n → Poly3) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => MvPolynomial.coeff (tagExponent (idx i).val) (P j)

/-- **Generic full recovery.** -/
theorem recovery_of_rightInverse (a : ℝ) (ha : physical a) (d : ℕ) (hl : 6 ≤ d) (hu : d ≤ 9)
    (p : MomentPivots d) (hp : ValidMomentPivots p) {n : ℕ} (idx : Fin n → RetainedIndex (2 * d))
    (hidx : Function.Bijective idx) (U : Fin n → GramFamily d) (P : Fin n → Poly3)
    (hP : ∀ j, invariantSubst (P j) = gramPoly a d p (U j)) (Dinv : Matrix (Fin n) (Fin n) ℝ)
    (hinv : coefMatrix idx P * Dinv = 1) (f : Compatible a (2 * d)) :
    gramPoly a d p (∑ j, (Dinv.mulVec (fun i => retainCompatible a (2 * d) f (idx i))) j • U j) = f.val := by
  set r : Fin n → ℝ := fun i => retainCompatible a (2 * d) f (idx i)
  set v := Dinv.mulVec r
  apply fixedGram_full_recovery_of_source a ha d hl hu p hp (∑ j, v j • U j) f
    (fixedSourceCombination P v) (fixedSourceCombination_canonical a p P U hP v)
  intro t
  obtain ⟨i, rfl⟩ := hidx.2 t
  have hc := fixedSourceCombination_coefficient (fun i => (idx i).val) P v i
  rw [hc]
  have h := fixedTableRealRightInverse_apply (coefMatrix idx P) Dinv hinv r
  exact congrFun h i

#print axioms recovery_of_rightInverse

end ThomsonCompact.Fixed
