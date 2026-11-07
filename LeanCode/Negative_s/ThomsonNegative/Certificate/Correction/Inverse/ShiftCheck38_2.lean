import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_38_2 : allBelow 8 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 38 (Nat.add 31 k)) (shiftANumerator 38 (Nat.add 31 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
