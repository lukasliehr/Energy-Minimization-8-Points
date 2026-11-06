import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows3
/-! Bridge of the re-expanded rows 16-16 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge016 : rowBridgeOk 202 68 8 8 557 1 row016 (fun m => FD.hC slicesB 16 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
