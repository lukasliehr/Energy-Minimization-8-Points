import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_47_1 : allBelow 2 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 47 (Nat.add 66 k)) (shiftANumerator 47 (Nat.add 66 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
