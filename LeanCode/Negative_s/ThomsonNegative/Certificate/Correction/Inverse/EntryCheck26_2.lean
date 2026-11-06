import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem inverse_checked_26_2 : allBelow 8 (fun k => (inverseEquation 26 (Nat.add 16 k)).check)=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
