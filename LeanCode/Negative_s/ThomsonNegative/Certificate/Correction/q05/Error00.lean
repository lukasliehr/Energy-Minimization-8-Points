import ThomsonNegative.Certificate.Correction.q05.BlockData

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError0_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 0 j))=rawError 0 := by decide +kernel
theorem rawError1_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 1 j))=rawError 1 := by decide +kernel
theorem rawError2_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 2 j))=rawError 2 := by decide +kernel
theorem rawError3_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 3 j))=rawError 3 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
