import ThomsonNegative.Structure.Factored.Data
namespace ThomsonNegative.Structure.Factored.scalar_inverse
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Factored.Data
noncomputable def columnCheck (j : Nat) : Bool := productColumnCheck SM SI (EncodedMatrix.identity 36) 323 41 101 j
end ThomsonNegative.Structure.Factored.scalar_inverse
