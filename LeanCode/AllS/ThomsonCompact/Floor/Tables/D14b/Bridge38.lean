import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows9
/-! Bridge of the re-expanded rows 43-45 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge043 : rowBridgeOk 145 35 7 6 384 1 row043 (fun m => FD.hC slicesB 43 m) = true := by decide +kernel

theorem bridge044 : rowBridgeOk 145 35 7 6 121 1 row044 (fun m => FD.hC slicesB 44 m) = true := by decide +kernel

theorem bridge045 : rowBridgeOk 145 35 7 6 75 1 row045 (fun m => FD.hC slicesB 45 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
