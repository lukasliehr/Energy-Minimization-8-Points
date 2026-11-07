import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError8_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 8 j))=rawError 8 := by decide +kernel
theorem rawError9_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 9 j))=rawError 9 := by decide +kernel
theorem rawError10_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 10 j))=rawError 10 := by decide +kernel
theorem rawError11_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 11 j))=rawError 11 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
