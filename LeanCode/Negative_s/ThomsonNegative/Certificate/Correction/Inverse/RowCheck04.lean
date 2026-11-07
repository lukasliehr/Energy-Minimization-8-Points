import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem lifts_checked_4 : allBelow 68 (fun j => (liftEquation 4 j).check)=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
