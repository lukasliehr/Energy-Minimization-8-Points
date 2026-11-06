import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows4
/-! Bridge of the re-expanded rows 22-22 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge022 : rowBridgeOk 202 68 8 8 576 1 row022 (fun m => FD.hC slicesB 22 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
