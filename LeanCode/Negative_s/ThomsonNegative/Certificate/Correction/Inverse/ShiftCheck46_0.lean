import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_46_0 : allBelow 53 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 46 (Nat.add 0 k)) (shiftANumerator 46 (Nat.add 0 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
