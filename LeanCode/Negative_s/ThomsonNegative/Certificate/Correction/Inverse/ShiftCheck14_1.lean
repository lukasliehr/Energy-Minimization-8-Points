import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_14_1 : allBelow 52 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 14 (Nat.add 16 k)) (shiftANumerator 14 (Nat.add 16 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
