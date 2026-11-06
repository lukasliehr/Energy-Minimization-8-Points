import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows9
/-! Bridge of the re-expanded rows 44-45 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge044 : rowBridgeOk 202 68 8 8 159 1 row044 (fun m => FD.hC slicesB 44 m) = true := by decide +kernel

theorem bridge045 : rowBridgeOk 202 68 8 8 133 1 row045 (fun m => FD.hC slicesB 45 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
