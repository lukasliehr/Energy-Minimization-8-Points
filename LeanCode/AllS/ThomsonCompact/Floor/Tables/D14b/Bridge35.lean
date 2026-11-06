import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows8
/-! Bridge of the re-expanded rows 38-38 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge038 : rowBridgeOk 145 35 7 6 445 1 row038 (fun m => FD.hC slicesB 38 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
