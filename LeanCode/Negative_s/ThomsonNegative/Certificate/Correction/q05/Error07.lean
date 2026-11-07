import ThomsonNegative.Certificate.Correction.q05.BlockData

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError28_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 28 j))=rawError 28 := by decide +kernel
theorem rawError29_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 29 j))=rawError 29 := by decide +kernel
theorem rawError30_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 30 j))=rawError 30 := by decide +kernel
theorem rawError31_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 31 j))=rawError 31 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
