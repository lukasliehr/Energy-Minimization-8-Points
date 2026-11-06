import ThomsonNegative.Structure.Factored.Data
namespace ThomsonNegative.Structure.Factored.moment_inverse
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Factored.Data
noncomputable def columnCheck (j : Nat) : Bool := productColumnCheck M MI (EncodedMatrix.identity 15) 197 30 60 j
end ThomsonNegative.Structure.Factored.moment_inverse
