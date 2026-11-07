import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle215
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle216
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle217
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle218
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle219
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle220
/-! Bridge of the re-expanded rows 215-220 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge215 : rowBridgeOk 272 1083 12 10 51 1 row215 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h215 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge216 : rowBridgeOk 272 1083 12 10 51 1 row216 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h216 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge217 : rowBridgeOk 272 1083 12 10 51 1 row217 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h217 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge218 : rowBridgeOk 272 1083 12 10 51 1 row218 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h218 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge219 : rowBridgeOk 272 1083 12 10 51 1 row219 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h219 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge220 : rowBridgeOk 272 1083 12 10 51 1 row220 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h220 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
