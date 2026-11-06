import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_10_3 : allBelow 5 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 10 (Nat.add 63 k)) (shiftANumerator 10 (Nat.add 63 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
