import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows2
/-! Bridge of the re-expanded rows 11-14 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge011 : rowBridgeOk 202 68 8 8 236 1 row011 (fun m => FD.hC slicesB 11 m) = true := by decide +kernel

theorem bridge012 : rowBridgeOk 202 68 8 8 210 1 row012 (fun m => FD.hC slicesB 12 m) = true := by decide +kernel

theorem bridge013 : rowBridgeOk 202 68 8 8 166 1 row013 (fun m => FD.hC slicesB 13 m) = true := by decide +kernel

theorem bridge014 : rowBridgeOk 202 68 8 8 193 1 row014 (fun m => FD.hC slicesB 14 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
