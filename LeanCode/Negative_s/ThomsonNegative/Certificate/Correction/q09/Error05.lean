import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem rawError20_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 20 j))=rawError 20 := by decide +kernel
theorem rawError21_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 21 j))=rawError 21 := by decide +kernel
theorem rawError22_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 22 j))=rawError 22 := by decide +kernel
theorem rawError23_checked : sumNat 68 (fun j => Nat.mul (residual j).e (rowColumns 23 j))=rawError 23 := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
