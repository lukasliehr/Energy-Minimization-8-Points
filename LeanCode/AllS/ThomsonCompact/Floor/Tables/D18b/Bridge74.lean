import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle233
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle234
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle235
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle236
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle237
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle238
/-! Bridge of the re-expanded rows 233-238 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge233 : rowBridgeOk 272 1083 12 10 51 1 row233 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h233 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge234 : rowBridgeOk 272 1083 12 10 51 1 row234 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h234 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge235 : rowBridgeOk 272 1083 12 10 51 1 row235 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h235 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge236 : rowBridgeOk 272 1083 12 10 51 1 row236 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h236 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge237 : rowBridgeOk 272 1083 12 10 51 1 row237 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h237 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge238 : rowBridgeOk 272 1083 12 10 51 1 row238 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h238 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
