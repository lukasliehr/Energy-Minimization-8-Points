import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows3
/-! Bridge of the re-expanded rows 18-18 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge018 : rowBridgeOk 202 68 8 8 562 1 row018 (fun m => FD.hC slicesB 18 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
