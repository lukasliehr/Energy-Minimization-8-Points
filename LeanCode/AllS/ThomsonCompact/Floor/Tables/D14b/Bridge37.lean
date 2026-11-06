import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows8
/-! Bridge of the re-expanded rows 40-42 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge040 : rowBridgeOk 145 35 7 6 305 1 row040 (fun m => FD.hC slicesB 40 m) = true := by decide +kernel

theorem bridge041 : rowBridgeOk 145 35 7 6 68 1 row041 (fun m => FD.hC slicesB 41 m) = true := by decide +kernel

theorem bridge042 : rowBridgeOk 145 35 7 6 77 1 row042 (fun m => FD.hC slicesB 42 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
