import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows9
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle041
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle042
/-! Bridge of the re-expanded rows 41-42 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge041 : rowBridgeOk 272 1083 12 10 230 1 row041 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h041 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge042 : rowBridgeOk 272 1083 12 10 241 1 row042 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h042 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
