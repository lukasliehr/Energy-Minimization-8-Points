import ThomsonNegative.Certificate.Correction.Inverse.Data00
import ThomsonNegative.Certificate.Correction.Inverse.Data01
import ThomsonNegative.Certificate.Correction.Inverse.Data02
import ThomsonNegative.Certificate.Correction.Inverse.Data03
import ThomsonNegative.Certificate.Correction.Inverse.Data04
import ThomsonNegative.Certificate.Correction.Inverse.Data05
import ThomsonNegative.Certificate.Correction.Inverse.Data06
import ThomsonNegative.Certificate.Correction.Inverse.Data07
import ThomsonNegative.Certificate.Correction.Inverse.Data08
import ThomsonNegative.Certificate.Correction.Inverse.Data09
import ThomsonNegative.Certificate.Correction.Inverse.Data10
import ThomsonNegative.Certificate.Correction.Inverse.Data11
import ThomsonNegative.Certificate.Correction.Inverse.Data12
import ThomsonNegative.Certificate.Correction.Inverse.Data13
import ThomsonNegative.Certificate.Correction.Inverse.Data14
import ThomsonNegative.Certificate.Correction.Inverse.Data15
import ThomsonNegative.Certificate.Correction.Inverse.Data16
import ThomsonNegative.Structure.Packed.MatrixKernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
noncomputable def shiftANumerator : Nat → Nat → Nat
  | 0 => shiftARow0
  | 1 => shiftARow1
  | 2 => shiftARow2
  | 3 => shiftARow3
  | 4 => shiftARow4
  | 5 => shiftARow5
  | 6 => shiftARow6
  | 7 => shiftARow7
  | 8 => shiftARow8
  | 9 => shiftARow9
  | 10 => shiftARow10
  | 11 => shiftARow11
  | 12 => shiftARow12
  | 13 => shiftARow13
  | 14 => shiftARow14
  | 15 => shiftARow15
  | 16 => shiftARow16
  | 17 => shiftARow17
  | 18 => shiftARow18
  | 19 => shiftARow19
  | 20 => shiftARow20
  | 21 => shiftARow21
  | 22 => shiftARow22
  | 23 => shiftARow23
  | 24 => shiftARow24
  | 25 => shiftARow25
  | 26 => shiftARow26
  | 27 => shiftARow27
  | 28 => shiftARow28
  | 29 => shiftARow29
  | 30 => shiftARow30
  | 31 => shiftARow31
  | 32 => shiftARow32
  | 33 => shiftARow33
  | 34 => shiftARow34
  | 35 => shiftARow35
  | 36 => shiftARow36
  | 37 => shiftARow37
  | 38 => shiftARow38
  | 39 => shiftARow39
  | 40 => shiftARow40
  | 41 => shiftARow41
  | 42 => shiftARow42
  | 43 => shiftARow43
  | 44 => shiftARow44
  | 45 => shiftARow45
  | 46 => shiftARow46
  | 47 => shiftARow47
  | 48 => shiftARow48
  | 49 => shiftARow49
  | 50 => shiftARow50
  | 51 => shiftARow51
  | 52 => shiftARow52
  | 53 => shiftARow53
  | 54 => shiftARow54
  | 55 => shiftARow55
  | 56 => shiftARow56
  | 57 => shiftARow57
  | 58 => shiftARow58
  | 59 => shiftARow59
  | 60 => shiftARow60
  | 61 => shiftARow61
  | 62 => shiftARow62
  | 63 => shiftARow63
  | 64 => shiftARow64
  | 65 => shiftARow65
  | 66 => shiftARow66
  | 67 => shiftARow67
  | _ => fun _ => 0x100000
noncomputable def liftANumerator : Nat → Nat → Nat
  | 0 => liftARow0
  | 1 => liftARow1
  | 2 => liftARow2
  | 3 => liftARow3
  | 4 => liftARow4
  | 5 => liftARow5
  | 6 => liftARow6
  | 7 => liftARow7
  | 8 => liftARow8
  | 9 => liftARow9
  | 10 => liftARow10
  | 11 => liftARow11
  | 12 => liftARow12
  | 13 => liftARow13
  | 14 => liftARow14
  | 15 => liftARow15
  | 16 => liftARow16
  | 17 => liftARow17
  | 18 => liftARow18
  | 19 => liftARow19
  | 20 => liftARow20
  | 21 => liftARow21
  | 22 => liftARow22
  | 23 => liftARow23
  | 24 => liftARow24
  | 25 => liftARow25
  | 26 => liftARow26
  | 27 => liftARow27
  | 28 => liftARow28
  | 29 => liftARow29
  | 30 => liftARow30
  | 31 => liftARow31
  | 32 => liftARow32
  | 33 => liftARow33
  | 34 => liftARow34
  | 35 => liftARow35
  | 36 => liftARow36
  | 37 => liftARow37
  | 38 => liftARow38
  | 39 => liftARow39
  | 40 => liftARow40
  | 41 => liftARow41
  | 42 => liftARow42
  | 43 => liftARow43
  | 44 => liftARow44
  | 45 => liftARow45
  | 46 => liftARow46
  | 47 => liftARow47
  | 48 => liftARow48
  | 49 => liftARow49
  | 50 => liftARow50
  | 51 => liftARow51
  | 52 => liftARow52
  | 53 => liftARow53
  | 54 => liftARow54
  | 55 => liftARow55
  | 56 => liftARow56
  | 57 => liftARow57
  | 58 => liftARow58
  | 59 => liftARow59
  | 60 => liftARow60
  | 61 => liftARow61
  | 62 => liftARow62
  | 63 => liftARow63
  | 64 => liftARow64
  | 65 => liftARow65
  | 66 => liftARow66
  | 67 => liftARow67
  | _ => fun _ => 0x100000
noncomputable def shiftedA : EncodedMatrix 68 68 := ⟨shiftANumerator,shiftDenominator⟩
end ThomsonNegative.Certificate.Correction.Inverse
