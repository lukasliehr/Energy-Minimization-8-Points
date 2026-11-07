import ThomsonNegative.Certificate.Correction.q05.BlockData

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError24_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 24 j))=rawError 24 := by decide +kernel
theorem rawError25_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 25 j))=rawError 25 := by decide +kernel
theorem rawError26_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 26 j))=rawError 26 := by decide +kernel
theorem rawError27_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 27 j))=rawError 27 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
