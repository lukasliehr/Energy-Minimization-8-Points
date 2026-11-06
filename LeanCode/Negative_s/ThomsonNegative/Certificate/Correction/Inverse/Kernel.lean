import ThomsonNegative.Certificate.Correction.Inverse.Data
import ThomsonNegative.Certificate.Correction.SourceData

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def inverseLength : Nat := 86
def inverseWidth : Nat := 1039
def inverseRadix : Nat := 3142
noncomputable def denominatorEquation (j : Nat) : Equation where
  radixBits := inverseRadix
  maxLength := inverseLength
  maxWidth := inverseWidth
  terms := 1
  left := fun _ => gamma j
  right := fun _ => Source.rowDenominator j
  scale := oneRecord
  target0 := commonDenominator
  target1 := oneRecord
  target2 := oneRecord
noncomputable def liftEquation (i j : Nat) : Equation where
  radixBits := inverseRadix
  maxLength := inverseLength
  maxWidth := inverseWidth
  terms := 1
  left := fun _ => shiftANumerator i j
  right := fun _ => gamma j
  scale := oneRecord
  target0 := liftANumerator i j
  target1 := oneRecord
  target2 := oneRecord
noncomputable def inverseEquation (i j : Nat) : Equation where
  radixBits := inverseRadix
  maxLength := inverseLength
  maxWidth := inverseWidth
  terms := 68
  left := liftANumerator i
  right := fun k => Source.rowNumerator k j
  scale := oneRecord
  target0 := cond (Nat.beq i j) shiftDenominator zeroRecord
  target1 := commonDenominator
  target2 := oneRecord

end ThomsonNegative.Certificate.Correction.Inverse
