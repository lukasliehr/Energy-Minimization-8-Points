import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows0
/-! Bridge of the re-expanded rows 3-3 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge003 : rowBridgeOk 202 68 8 8 383 1 row003 (fun m => FD.hC slicesB 3 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
