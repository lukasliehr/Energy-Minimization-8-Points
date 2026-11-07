import ThomsonNegative.Structure.Packed.IdentityKernel
import ThomsonNegative.Certificate.Bridges.RawData
namespace ThomsonNegative.Structure.Concrete.SymmetryKernel
open ThomsonNegative.Structure.Exact ThomsonNegative.Certificate.Bridges
noncomputable def entryCheck (b l r s : Nat) : Bool :=
  Nat.beq (RawData.positiveSlot b l r s) (RawData.positiveSlot b l s r) &&
  Nat.beq (RawData.negativeSlot b l r s) (RawData.negativeSlot b l s r)
noncomputable def blockCheck (b : Nat) : Bool :=
  allBelow 102 (fun l => allBelow (RawData.size b) (fun r =>
    allBelow (RawData.size b) (fun s => entryCheck b l r s)))
end ThomsonNegative.Structure.Concrete.SymmetryKernel
