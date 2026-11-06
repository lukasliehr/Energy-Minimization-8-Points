import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError64_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 64 j))=rawError 64 := by decide +kernel
theorem rawError65_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 65 j))=rawError 65 := by decide +kernel
theorem rawError66_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 66 j))=rawError 66 := by decide +kernel
theorem rawError67_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 67 j))=rawError 67 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
