import ThomsonNegative.Finalization.ExactSource
import ThomsonNegative.Certificate.Correction.Inverse.All

noncomputable section
namespace ThomsonNegative.Finalization
open ThomsonNegative.Structure ThomsonNegative.Certificate ThomsonNegative.Geometry

/-- Every fixed source-table identity is discharged by the kernel leaves. -/
def sourceIdentityChecks : Concrete.SourceIdentityChecks where
  denominators := Correction.Inverse.denominator_checks
  lifts := Correction.Inverse.lift_checks
  inverse := Correction.Inverse.inverse_checks
  shiftNumerators := Correction.Inverse.shift_numerator_checks
  shiftDenom := Correction.Inverse.shift_denominator_check

theorem verified_cell (c : Fin 5) :
    CellSpec (cellLower c) (cellUpper c)
      (fun q => Bridges.sourcePolynomialFamily (aStar (2*q-2))) :=
  cellSpec_from_checks sourceIdentityChecks c

/-- The stationary square antiprism is the unique global minimizer throughout
the complete open negative-exponent interval. -/
theorem negative_s_minimizer (s : ℝ) (hs : s ∈ Set.Ioo (-2:ℝ) 0) :
    IsUniqueMinimizer s (X (aStar s)) :=
  negative_s_minimizer_from_checks sourceIdentityChecks s hs

/-- The exact existential statement requested by the negative-s showcase. -/
theorem negative_s_global_optimality :
    ∃ a : ℝ → ℝ,
      (∀ s ∈ Set.Ioo (-2:ℝ) 0,a s ∈ Set.Ioo 0 1 ∧
        ∀ b ∈ Set.Ioo (0:ℝ) 1,F s b=0 ↔ b=a s) ∧
      ∀ s ∈ Set.Ioo (-2:ℝ) 0,IsUniqueMinimizer s (X (a s)) :=
  negative_s_showcase_from_checks sourceIdentityChecks

#print axioms verified_cell
#print axioms negative_s_minimizer
#print axioms negative_s_global_optimality
end ThomsonNegative.Finalization
