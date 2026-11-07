import ThomsonNegative.Structure.Factored.Data
namespace ThomsonNegative.Structure.Factored.scalar_zero_jets
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Factored.Data
noncomputable def columnCheck (j : Nat) : Bool := productColumnCheck J S (EncodedMatrix.zero 15 36) 153 23 45 j
end ThomsonNegative.Structure.Factored.scalar_zero_jets
