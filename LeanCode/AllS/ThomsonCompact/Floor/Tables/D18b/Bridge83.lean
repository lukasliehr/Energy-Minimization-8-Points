import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows11
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle268
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle269
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle270
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle271
/-! Bridge of the re-expanded rows 268-271 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge268 : rowBridgeOk 272 1083 12 10 229 1 row268 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h268 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge269 : rowBridgeOk 272 1083 12 10 206 1 row269 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h269 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge270 : rowBridgeOk 272 1083 12 10 233 1 row270 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h270 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge271 : rowBridgeOk 272 1083 12 10 52 1 row271 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h271 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
