import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_9_2 : allBelow 16 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 9 (Nat.add 52 k)) (shiftANumerator 9 (Nat.add 52 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
