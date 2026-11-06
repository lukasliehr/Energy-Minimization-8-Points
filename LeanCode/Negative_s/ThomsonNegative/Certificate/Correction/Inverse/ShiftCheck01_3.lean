import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_1_3 : allBelow 1 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 1 (Nat.add 67 k)) (shiftANumerator 1 (Nat.add 67 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
