import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle167
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle168
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle169
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle170
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle171
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle172
/-! Bridge of the re-expanded rows 167-172 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge167 : rowBridgeOk 272 1083 12 10 51 1 row167 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h167 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge168 : rowBridgeOk 272 1083 12 10 51 1 row168 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h168 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge169 : rowBridgeOk 272 1083 12 10 51 1 row169 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h169 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge170 : rowBridgeOk 272 1083 12 10 51 1 row170 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h170 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge171 : rowBridgeOk 272 1083 12 10 51 1 row171 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h171 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge172 : rowBridgeOk 272 1083 12 10 51 1 row172 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h172 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
