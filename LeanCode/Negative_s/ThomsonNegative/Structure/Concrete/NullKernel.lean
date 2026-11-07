import ThomsonNegative.Structure.Concrete.NullData
namespace ThomsonNegative.Structure.Concrete.NullKernel
open ThomsonNegative.Structure.Exact ThomsonNegative.Certificate.Bridges
noncomputable def rowWeight (b r s j : Nat) : Signed :=
  sm (Nat.mul (RawData.positiveSlot b j r s) (Nat.div 4 (Factored.FunctionalData.denominator j)))
    (Nat.mul (RawData.negativeSlot b j r s) (Nat.div 4 (Factored.FunctionalData.denominator j)))
noncomputable def sourceEquation (b r s : Nat) : WeightedEquation :=
  ⟨⟨123,13,31,102,Factored.FunctionalData.numerator,(fun _ => oneRecord),
    oneRecord,NullData.numerator b r s,oneRecord,oneRecord⟩,rowWeight b r s,9680⟩
noncomputable def sourceRowCheck (b r : Nat) : Bool :=
  allBelow (RawData.size b) (fun s => (sourceEquation b r s).check)
noncomputable def nullColumnCheck (b j : Nat) : Bool :=
  productColumnCheck (NullData.T b) (NullData.U b)
    (EncodedMatrix.zero (RawData.size b) (ThomsonNegative.Certificate.BasisLayout.freeOrder b)) 123 13 31 j
end ThomsonNegative.Structure.Concrete.NullKernel
