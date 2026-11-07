import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows2
/-! Bridge of the re-expanded rows 10-13 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge010 : rowBridgeOk 145 35 7 6 304 1 row010 (fun m => FD.hC slicesB 10 m) = true := by decide +kernel

theorem bridge011 : rowBridgeOk 145 35 7 6 195 1 row011 (fun m => FD.hC slicesB 11 m) = true := by decide +kernel

theorem bridge012 : rowBridgeOk 145 35 7 6 173 1 row012 (fun m => FD.hC slicesB 12 m) = true := by decide +kernel

theorem bridge013 : rowBridgeOk 145 35 7 6 134 1 row013 (fun m => FD.hC slicesB 13 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
