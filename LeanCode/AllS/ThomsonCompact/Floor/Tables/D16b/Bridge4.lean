import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows0
/-! Bridge of the re-expanded rows 4-4 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge004 : rowBridgeOk 202 68 8 8 373 1 row004 (fun m => FD.hC slicesB 4 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
