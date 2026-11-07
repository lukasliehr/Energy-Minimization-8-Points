import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem inverse_checked_33_7 : allBelow 8 (fun k => (inverseEquation 33 (Nat.add 56 k)).check)=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
