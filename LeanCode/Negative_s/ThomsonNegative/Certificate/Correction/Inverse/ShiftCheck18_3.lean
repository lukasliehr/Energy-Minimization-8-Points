import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_18_3 : allBelow 10 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 18 (Nat.add 58 k)) (shiftANumerator 18 (Nat.add 58 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
