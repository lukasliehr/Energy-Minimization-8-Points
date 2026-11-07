import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem shift_checked_26_2 : allBelow 18 (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 26 (Nat.add 46 k)) (shiftANumerator 26 (Nat.add 46 k)))=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
