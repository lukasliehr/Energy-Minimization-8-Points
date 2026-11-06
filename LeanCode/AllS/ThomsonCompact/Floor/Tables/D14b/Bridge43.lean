import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows10
/-! Bridge of the re-expanded rows 139-144 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge139 : rowBridgeOk 145 35 7 6 376 1 row139 (fun m => FD.hC slicesB 139 m) = true := by decide +kernel

theorem bridge140 : rowBridgeOk 145 35 7 6 65 1 row140 (fun m => FD.hC slicesB 140 m) = true := by decide +kernel

theorem bridge141 : rowBridgeOk 145 35 7 6 4 1 row141 (fun m => FD.hC slicesB 141 m) = true := by decide +kernel

theorem bridge142 : rowBridgeOk 145 35 7 6 72 1 row142 (fun m => FD.hC slicesB 142 m) = true := by decide +kernel

theorem bridge143 : rowBridgeOk 145 35 7 6 4 1 row143 (fun m => FD.hC slicesB 143 m) = true := by decide +kernel

theorem bridge144 : rowBridgeOk 145 35 7 6 4 1 row144 (fun m => FD.hC slicesB 144 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
