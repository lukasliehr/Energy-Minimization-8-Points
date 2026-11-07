import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem inverse_checked_42_4 : allBelow 8 (fun k => (inverseEquation 42 (Nat.add 32 k)).check)=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
