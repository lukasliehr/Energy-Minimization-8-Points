import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows9
/-! Bridge of the re-expanded rows 46-50 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge046 : rowBridgeOk 145 35 7 6 411 1 row046 (fun m => FD.hC slicesB 46 m) = true := by decide +kernel

theorem bridge047 : rowBridgeOk 145 35 7 6 3 1 row047 (fun m => FD.hC slicesB 47 m) = true := by decide +kernel

theorem bridge048 : rowBridgeOk 145 35 7 6 74 1 row048 (fun m => FD.hC slicesB 48 m) = true := by decide +kernel

theorem bridge049 : rowBridgeOk 145 35 7 6 72 1 row049 (fun m => FD.hC slicesB 49 m) = true := by decide +kernel

theorem bridge050 : rowBridgeOk 145 35 7 6 76 1 row050 (fun m => FD.hC slicesB 50 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
