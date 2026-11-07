import ThomsonNegative.Structure.Factored.Data
namespace ThomsonNegative.Structure.Factored.complement_inverse
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Factored.Data
noncomputable def columnCheck (j : Nat) : Bool := productColumnCheck CI JC (EncodedMatrix.identity 15) 145 23 43 j
end ThomsonNegative.Structure.Factored.complement_inverse
