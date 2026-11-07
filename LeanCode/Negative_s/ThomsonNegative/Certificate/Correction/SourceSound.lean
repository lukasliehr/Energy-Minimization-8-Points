import ThomsonNegative.Certificate.Correction.SourceData
import ThomsonNegative.Certificate.Correction.RowSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.Source

/-- Canonical shared-table row. The argument is shifted by `83/256`.
The sentinel row 68 and every later row represent a structurally zero entry. -/
def rowLinear (u : ℝ) (row : ℕ) : (Fin 68 → ℝ) →ₗ[ℝ] ℝ :=
  if row<68 then Correction.rowMap (rowNumerator row) (rowDenominator row) u else 0

lemma rowLinear_apply (u : ℝ) (row : Fin 68) (x : Fin 68 → ℝ) :
    rowLinear u row x=∑ j : Fin 68,
      (Structure.Packed.evalZ (Structure.Exact.recCoeffs (rowNumerator row j)) u /
        Structure.Packed.evalZ (Structure.Exact.recCoeffs (rowDenominator row)) u)*x j := by
  rw [rowLinear,if_pos row.isLt,Correction.rowMap_apply]

lemma rowLinear_sentinel (u : ℝ) : rowLinear u 68=0 := by simp [rowLinear]

end ThomsonNegative.Certificate.Correction.Source
