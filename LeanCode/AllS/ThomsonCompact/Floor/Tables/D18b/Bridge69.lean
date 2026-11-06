import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle203
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle204
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle205
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle206
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle207
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle208
/-! Bridge of the re-expanded rows 203-208 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge203 : rowBridgeOk 272 1083 12 10 51 1 row203 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h203 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge204 : rowBridgeOk 272 1083 12 10 51 1 row204 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h204 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge205 : rowBridgeOk 272 1083 12 10 51 1 row205 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h205 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge206 : rowBridgeOk 272 1083 12 10 51 1 row206 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h206 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge207 : rowBridgeOk 272 1083 12 10 51 1 row207 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h207 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge208 : rowBridgeOk 272 1083 12 10 51 1 row208 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h208 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
