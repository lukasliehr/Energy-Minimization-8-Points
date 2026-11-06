import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_19_2 : allBelow 14 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 19 (Nat.add 25 k)) (shiftANumerator 19 (Nat.add 25 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
