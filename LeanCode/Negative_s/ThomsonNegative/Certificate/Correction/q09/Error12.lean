import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError48_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 48 j))=rawError 48 := by decide +kernel
theorem rawError49_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 49 j))=rawError 49 := by decide +kernel
theorem rawError50_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 50 j))=rawError 50 := by decide +kernel
theorem rawError51_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 51 j))=rawError 51 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
