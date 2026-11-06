import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem lifts_checked_57 : allBelow 68 (fun j => (liftEquation 57 j).check)=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
