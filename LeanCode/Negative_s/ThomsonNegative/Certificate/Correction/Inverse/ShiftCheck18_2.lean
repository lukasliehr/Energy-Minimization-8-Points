import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_18_2 : allBelow 24 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 18 (Nat.add 34 k)) (shiftANumerator 18 (Nat.add 34 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
