import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle257
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle258
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle259
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle260
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle261
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle262
/-! Bridge of the re-expanded rows 257-262 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge257 : rowBridgeOk 272 1083 12 10 51 1 row257 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h257 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge258 : rowBridgeOk 272 1083 12 10 51 1 row258 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h258 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge259 : rowBridgeOk 272 1083 12 10 51 1 row259 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h259 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge260 : rowBridgeOk 272 1083 12 10 51 1 row260 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h260 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge261 : rowBridgeOk 272 1083 12 10 51 1 row261 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h261 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge262 : rowBridgeOk 272 1083 12 10 51 1 row262 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h262 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
