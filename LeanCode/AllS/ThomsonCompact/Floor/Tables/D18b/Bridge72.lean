import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle221
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle222
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle223
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle224
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle225
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle226
/-! Bridge of the re-expanded rows 221-226 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge221 : rowBridgeOk 272 1083 12 10 51 1 row221 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h221 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge222 : rowBridgeOk 272 1083 12 10 51 1 row222 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h222 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge223 : rowBridgeOk 272 1083 12 10 51 1 row223 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h223 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge224 : rowBridgeOk 272 1083 12 10 51 1 row224 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h224 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge225 : rowBridgeOk 272 1083 12 10 51 1 row225 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h225 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge226 : rowBridgeOk 272 1083 12 10 51 1 row226 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h226 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
