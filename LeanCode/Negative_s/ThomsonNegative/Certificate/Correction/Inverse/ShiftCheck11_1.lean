import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_11_1 : allBelow 13 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 11 (Nat.add 22 k)) (shiftANumerator 11 (Nat.add 22 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
