import ThomsonNegative.Certificate.Correction.q05.BlockData

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError56_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 56 j))=rawError 56 := by decide +kernel
theorem rawError57_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 57 j))=rawError 57 := by decide +kernel
theorem rawError58_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 58 j))=rawError 58 := by decide +kernel
theorem rawError59_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 59 j))=rawError 59 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
