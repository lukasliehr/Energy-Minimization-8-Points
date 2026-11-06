import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle245
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle246
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle247
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle248
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle249
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle250
/-! Bridge of the re-expanded rows 245-250 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge245 : rowBridgeOk 272 1083 12 10 51 1 row245 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h245 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge246 : rowBridgeOk 272 1083 12 10 51 1 row246 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h246 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge247 : rowBridgeOk 272 1083 12 10 51 1 row247 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h247 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge248 : rowBridgeOk 272 1083 12 10 51 1 row248 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h248 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge249 : rowBridgeOk 272 1083 12 10 51 1 row249 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h249 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge250 : rowBridgeOk 272 1083 12 10 51 1 row250 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h250 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
