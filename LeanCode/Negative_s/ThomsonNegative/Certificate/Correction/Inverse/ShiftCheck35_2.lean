import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_35_2 : allBelow 12 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 35 (Nat.add 56 k)) (shiftANumerator 35 (Nat.add 56 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
