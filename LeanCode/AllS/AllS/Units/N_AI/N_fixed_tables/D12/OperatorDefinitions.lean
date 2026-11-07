import AllS.Units.N_AI.N_fixed_tables.D12.Domain
import AllS.Units.N_AI.N_fixed_tables.D12.Layout

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP.FixedTables.D12
open Blueprint.Thomson.Finite

/-- Actual polynomial fixed-table right-inverse entries, with the row scaling
    from the supplied exact table. Their denominators are physically nonzero. -/
def inverseMatrix (a : ℝ) : Matrix (Fin 100) (Fin 100) ℝ :=
  fun i j => evalIntegerList (H i j) a /
    ((tableScales i:ℝ)*evalRationalList (tableDenominators i) a)

theorem inverseMatrix_denominator_nonzero (a : ℝ) (ha : physical a) (i : Fin 100) :
    (tableScales i:ℝ)*evalRationalList (tableDenominators i) a≠0 :=
  mul_ne_zero (tableScales_real_nonzero i) (tableDenominators_nonzero a ha i)

#print axioms inverseMatrix_denominator_nonzero
end Blueprint.CAP.FixedTables.D12
