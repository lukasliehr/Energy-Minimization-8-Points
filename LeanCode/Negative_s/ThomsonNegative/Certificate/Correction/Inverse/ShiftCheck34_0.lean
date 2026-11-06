import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_34_0 : allBelow 48 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 34 (Nat.add 0 k)) (shiftANumerator 34 (Nat.add 0 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
