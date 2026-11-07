import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_4_2 : allBelow 8 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 4 (Nat.add 30 k)) (shiftANumerator 4 (Nat.add 30 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
