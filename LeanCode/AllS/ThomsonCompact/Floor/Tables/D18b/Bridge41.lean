import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows9
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle044
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle045
/-! Bridge of the re-expanded rows 44-45 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge044 : rowBridgeOk 272 1083 12 10 349 1 row044 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h044 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge045 : rowBridgeOk 272 1083 12 10 240 1 row045 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h045 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
