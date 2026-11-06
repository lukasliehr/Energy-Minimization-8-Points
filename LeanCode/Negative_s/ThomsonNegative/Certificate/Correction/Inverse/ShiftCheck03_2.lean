import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_3_2 : allBelow 27 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 3 (Nat.add 39 k)) (shiftANumerator 3 (Nat.add 39 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
