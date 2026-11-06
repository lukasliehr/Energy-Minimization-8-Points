import ThomsonNegative.Finalization.Cellwise
import ThomsonNegative.Structure.Concrete.SourceInverseSound
import ThomsonNegative.Certificate.Correction.CellsDenominators

noncomputable section
namespace ThomsonNegative.Finalization
open ThomsonNegative.Structure ThomsonNegative.Certificate ThomsonNegative.Geometry

/-- The only inputs are literal checks of the fixed source polynomial tables. -/
def exactRepairFromChecks (C : Concrete.SourceIdentityChecks) (c : Fin 5)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    ExactRepair (Compact.Target.ScalarCells.heightFunction c t) := by
  let a := Compact.Target.ScalarCells.heightFunction c t
  have ha := Compact.Target.ScalarCells.height_range c t ht
  have hden : Packed.evalZ (Exact.recCoeffs (Correction.Source.rowDenominator 23)) (a-83/256)≠0 :=
    Correction.Cells.denominator_nonzero c (23:Fin 68) t ht
  let hi := C.matrix_inverse a ha.1.le ha.2 hden
  exact {
    system := Concrete.system a ha.1.le ha.2
    inverse := Concrete.rightInverseOfSourceIdentity a ha.1.le ha.2 hi
    family_eq := rfl
    coefficient_eq := rfl
    value_eq := rfl
    slope_eq := rfl
    correction_eq := rfl }

theorem cellSpec_from_checks (C : Concrete.SourceIdentityChecks) (c : Fin 5) :
    CellSpec (cellLower c) (cellUpper c)
      (fun q => Bridges.sourcePolynomialFamily (aStar (2*q-2))) :=
  cellSpec_of_cellwiseRepair (matrixData c) c (fourFloors c) (exactRepairFromChecks C c)

theorem negative_s_minimizer_from_checks (C : Concrete.SourceIdentityChecks)
    (s : ℝ) (hs : s ∈ Set.Ioo (-2:ℝ) 0) : IsUniqueMinimizer s (X (aStar s)) :=
  negative_thomson_of_cellwiseRepair (exactRepairFromChecks C) s hs

theorem negative_s_showcase_from_checks (C : Concrete.SourceIdentityChecks) :
    ∃ a : ℝ → ℝ,
      (∀ s ∈ Set.Ioo (-2:ℝ) 0,a s ∈ Set.Ioo 0 1 ∧
        ∀ b ∈ Set.Ioo (0:ℝ) 1,F s b=0 ↔ b=a s) ∧
      ∀ s ∈ Set.Ioo (-2:ℝ) 0,IsUniqueMinimizer s (X (a s)) := by
  refine ⟨aStar,?_,?_⟩
  · intro s hs
    exact aStar_spec s hs.1
  · exact negative_s_minimizer_from_checks C

#print axioms exactRepairFromChecks
#print axioms negative_s_showcase_from_checks
end ThomsonNegative.Finalization
