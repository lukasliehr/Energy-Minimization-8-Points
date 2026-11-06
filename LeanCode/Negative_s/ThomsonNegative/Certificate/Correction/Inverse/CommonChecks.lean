import ThomsonNegative.Certificate.Correction.Inverse.Kernel

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem denominators_checked : allBelow 68 (fun j => (denominatorEquation j).check)=true := by decide +kernel
theorem shift_denominator_check : shiftCheck shiftDegree Structure.Factored.HighData.A.denominator shiftDenominator=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.Inverse
