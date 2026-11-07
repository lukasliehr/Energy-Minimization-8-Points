import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError16_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 16 j))=rawError 16 := by decide +kernel
theorem rawError17_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 17 j))=rawError 17 := by decide +kernel
theorem rawError18_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 18 j))=rawError 18 := by decide +kernel
theorem rawError19_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 19 j))=rawError 19 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
