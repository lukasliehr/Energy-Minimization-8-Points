import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_16_2 : allBelow 15 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 16 (Nat.add 50 k)) (shiftANumerator 16 (Nat.add 50 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
