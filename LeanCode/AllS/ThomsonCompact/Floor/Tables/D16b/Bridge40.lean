import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows9
/-! Bridge of the re-expanded rows 46-46 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge046 : rowBridgeOk 202 68 8 8 495 1 row046 (fun m => FD.hC slicesB 46 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
