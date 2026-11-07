import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows8
/-! Bridge of the re-expanded rows 37-37 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge037 : rowBridgeOk 202 68 8 8 558 1 row037 (fun m => FD.hC slicesB 37 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
