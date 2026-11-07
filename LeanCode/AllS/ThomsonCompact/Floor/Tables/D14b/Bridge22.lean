import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Floor.Tables.D14b.Rows5
/-! Bridge of the re-expanded rows 25-25 to the compact D14 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D14b
open ThomsonCompact.Floor.B

theorem bridge025 : rowBridgeOk 145 35 7 6 199 1 row025 (fun m => FD.hC slicesB 25 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D14b
