import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle239
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle240
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle241
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle242
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle243
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle244
/-! Bridge of the re-expanded rows 239-244 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge239 : rowBridgeOk 272 1083 12 10 51 1 row239 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h239 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge240 : rowBridgeOk 272 1083 12 10 51 1 row240 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h240 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge241 : rowBridgeOk 272 1083 12 10 51 1 row241 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h241 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge242 : rowBridgeOk 272 1083 12 10 51 1 row242 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h242 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge243 : rowBridgeOk 272 1083 12 10 51 1 row243 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h243 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge244 : rowBridgeOk 272 1083 12 10 51 1 row244 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h244 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
