import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle251
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle252
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle253
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle254
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle255
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle256
/-! Bridge of the re-expanded rows 251-256 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge251 : rowBridgeOk 272 1083 12 10 51 1 row251 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h251 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge252 : rowBridgeOk 272 1083 12 10 52 1 row252 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h252 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge253 : rowBridgeOk 272 1083 12 10 51 1 row253 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h253 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge254 : rowBridgeOk 272 1083 12 10 51 1 row254 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h254 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge255 : rowBridgeOk 272 1083 12 10 51 1 row255 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h255 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge256 : rowBridgeOk 272 1083 12 10 51 1 row256 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h256 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
