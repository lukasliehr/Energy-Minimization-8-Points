import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows10
/-! Bridge of the re-expanded rows 181-193 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge181 : rowBridgeOk 202 68 8 8 3 1 row181 (fun m => FD.hC slicesB 181 m) = true := by decide +kernel

theorem bridge182 : rowBridgeOk 202 68 8 8 3 1 row182 (fun m => FD.hC slicesB 182 m) = true := by decide +kernel

theorem bridge183 : rowBridgeOk 202 68 8 8 3 1 row183 (fun m => FD.hC slicesB 183 m) = true := by decide +kernel

theorem bridge184 : rowBridgeOk 202 68 8 8 3 1 row184 (fun m => FD.hC slicesB 184 m) = true := by decide +kernel

theorem bridge185 : rowBridgeOk 202 68 8 8 7 1 row185 (fun m => FD.hC slicesB 185 m) = true := by decide +kernel

theorem bridge186 : rowBridgeOk 202 68 8 8 3 1 row186 (fun m => FD.hC slicesB 186 m) = true := by decide +kernel

theorem bridge187 : rowBridgeOk 202 68 8 8 3 1 row187 (fun m => FD.hC slicesB 187 m) = true := by decide +kernel

theorem bridge188 : rowBridgeOk 202 68 8 8 3 1 row188 (fun m => FD.hC slicesB 188 m) = true := by decide +kernel

theorem bridge189 : rowBridgeOk 202 68 8 8 3 1 row189 (fun m => FD.hC slicesB 189 m) = true := by decide +kernel

theorem bridge190 : rowBridgeOk 202 68 8 8 3 1 row190 (fun m => FD.hC slicesB 190 m) = true := by decide +kernel

theorem bridge191 : rowBridgeOk 202 68 8 8 3 1 row191 (fun m => FD.hC slicesB 191 m) = true := by decide +kernel

theorem bridge192 : rowBridgeOk 202 68 8 8 3 1 row192 (fun m => FD.hC slicesB 192 m) = true := by decide +kernel

theorem bridge193 : rowBridgeOk 202 68 8 8 3 1 row193 (fun m => FD.hC slicesB 193 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
