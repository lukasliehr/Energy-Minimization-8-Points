import ThomsonNegative.Structure.Concrete.BasisData
import ThomsonNegative.Structure.Factored.HighData
import ThomsonNegative.Certificate.Bridges.RawData
import ThomsonNegative.Structure.Packed.WeightedKernel
namespace ThomsonNegative.Structure.Concrete.MapKernel
open ThomsonNegative.Structure.Exact
open ThomsonNegative.Certificate.Bridges
noncomputable def basisSquare0 : Nat := 0x350000e01000
noncomputable def basisSquare1 : Nat := 0x401b1f43121544ec868f50d8b1396c01107000
noncomputable def basisSquare2 : Nat := 0x800c7f2887145f30d6f40d28b96c01007000
noncomputable def basisSquare3 : Nat := 0x806c7790b4081d90b96c01005000
noncomputable def basisSquare4 : Nat := 0x806c7790b4081d90b96c01005000
noncomputable def basisSquare5 : Nat := 0x412c9c21b222708412c00f05000
noncomputable def basisSquare6 : Nat := 0x400000080000010000401ffff003ff9500804500101dc801d2ba0053702003c95001801340180df00433a90001b0d000
noncomputable def basisSquare7 : Nat := 0x80000000800000008019a1007e65f0008a02e4005ff6c000bb110e003e537000aba634006ffb60008280b9000200b000
noncomputable def basisSquare : Nat → Nat
 | 0 => basisSquare0
 | 1 => basisSquare1
 | 2 => basisSquare2
 | 3 => basisSquare3
 | 4 => basisSquare4
 | 5 => basisSquare5
 | 6 => basisSquare6
 | 7 => basisSquare7
 | _ => oneRecord
def repairBlock (j : Nat) : Nat := (Factored.HighData.repairCoordinate j).1
def repairRow (j : Nat) : Nat := (Factored.HighData.repairCoordinate j).2.1
def repairCol (j : Nat) : Nat := (Factored.HighData.repairCoordinate j).2.2
def multiplicity (j : Nat) : Nat := if repairRow j==repairCol j then 1 else 2
noncomputable def weight (row col k : Nat) : Signed :=
  let b := repairBlock col
  let n := RawData.size b
  sm (Nat.mul (multiplicity col) (RawData.positiveSlot b (ThomsonNegative.Certificate.BasisLayout.fullRow row) (k/n) (k%n)))
    (Nat.mul (multiplicity col) (RawData.negativeSlot b (ThomsonNegative.Certificate.BasisLayout.fullRow row) (k/n) (k%n)))

noncomputable def sourceEquation (row col : Nat) : WeightedEquation :=
  let b := repairBlock col
  let n := RawData.size b
  ⟨⟨218,30,61,Nat.mul n n,
    (fun k => BasisData.numerator b (k/n) (repairRow col)),
    (fun k => BasisData.numerator b (k%n) (repairCol col)),
    Factored.HighData.A.denominator,Factored.HighData.A.numerator row col,basisSquare b,oneRecord⟩,
    weight row col,8192⟩
noncomputable def chunkCheck (col chunk : Nat) : Bool :=
  allBelow (min 8 (68-8*chunk)) (fun i => (sourceEquation (8*chunk+i) col).check)
end ThomsonNegative.Structure.Concrete.MapKernel
