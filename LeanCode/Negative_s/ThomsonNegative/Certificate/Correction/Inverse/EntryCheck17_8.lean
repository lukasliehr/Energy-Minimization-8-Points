import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem inverse_checked_17_8 : allBelow 4 (fun k => (inverseEquation 17 (Nat.add 64 k)).check)=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
