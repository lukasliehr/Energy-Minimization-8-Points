import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Floor.Tables.D16b.Rows10
/-! Bridge of the re-expanded rows 197-201 to the compact D16 right inverse (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D16b
open ThomsonCompact.Floor.B

theorem bridge197 : rowBridgeOk 202 68 8 8 91 1 row197 (fun m => FD.hC slicesB 197 m) = true := by decide +kernel

theorem bridge198 : rowBridgeOk 202 68 8 8 4 1 row198 (fun m => FD.hC slicesB 198 m) = true := by decide +kernel

theorem bridge199 : rowBridgeOk 202 68 8 8 98 1 row199 (fun m => FD.hC slicesB 199 m) = true := by decide +kernel

theorem bridge200 : rowBridgeOk 202 68 8 8 3 1 row200 (fun m => FD.hC slicesB 200 m) = true := by decide +kernel

theorem bridge201 : rowBridgeOk 202 68 8 8 3 1 row201 (fun m => FD.hC slicesB 201 m) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D16b
