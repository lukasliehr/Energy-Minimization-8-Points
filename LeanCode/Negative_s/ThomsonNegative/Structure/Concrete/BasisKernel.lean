import ThomsonNegative.Structure.Concrete.BasisData
namespace ThomsonNegative.Structure.Concrete.BasisKernel
open ThomsonNegative.Structure.Exact
open ThomsonNegative.Certificate
noncomputable def numeratorEquation (b r i : Nat) : Equation :=
  ⟨67,12,19,1,(fun _ => BasisData.sourceNumerator (BasisLayout.index b r i)),
    (fun _ => BasisData.quotient b r i),oneRecord,BasisData.numerator b r i,oneRecord,oneRecord⟩
noncomputable def denominatorEquation (b r i : Nat) : Equation :=
  ⟨67,12,19,1,(fun _ => BasisData.sourceDenominator (BasisLayout.index b r i)),
    (fun _ => BasisData.quotient b r i),oneRecord,BasisData.denominator b,oneRecord,oneRecord⟩
noncomputable def rowCheck (b r n : Nat) : Bool := allBelow n (fun i =>
  (numeratorEquation b r i).check && (denominatorEquation b r i).check)
end ThomsonNegative.Structure.Concrete.BasisKernel
