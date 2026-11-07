import ThomsonNegative.Certificate.BasisData
import ThomsonNegative.Certificate.BasisLayout
import ThomsonNegative.Certificate.FactorKernel
import ThomsonNegative.Certificate.TargetData

/-! One shared Init-only index/shape check for all five cells. -/
namespace ThomsonNegative.Certificate

noncomputable def basisIndicesValid : Bool :=
  allBelow 8 (fun b => allBelow (BasisLayout.rawOrder b) (fun i =>
    allBelow (BasisLayout.freeOrder b) (fun j =>
      Nat.blt (BasisLayout.index b i j) BasisData.records.length)))

def targetDegreesValid : Bool :=
  allBelow 68 (fun r => Nat.beq (TargetData.entry r).2.2 0 || Nat.blt (TargetData.entry r).1 8)

theorem basis_indices_pass : basisIndicesValid = true := by decide +kernel
theorem target_degrees_pass : targetDegreesValid = true := by decide +kernel

end ThomsonNegative.Certificate
