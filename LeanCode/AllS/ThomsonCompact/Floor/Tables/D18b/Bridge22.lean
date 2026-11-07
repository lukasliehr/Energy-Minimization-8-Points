import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows5
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle024
/-! Bridge of the re-expanded rows 24-24 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge024 : rowBridgeOk 272 1083 12 10 896 1 row024 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h024 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
