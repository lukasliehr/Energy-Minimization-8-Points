import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_5_1 : allBelow 25 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 5 (Nat.add 39 k)) (shiftANumerator 5 (Nat.add 39 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
