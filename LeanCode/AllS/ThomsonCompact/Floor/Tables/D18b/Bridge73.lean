import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle227
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle228
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle229
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle230
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle231
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle232
/-! Bridge of the re-expanded rows 227-232 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge227 : rowBridgeOk 272 1083 12 10 51 1 row227 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h227 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge228 : rowBridgeOk 272 1083 12 10 51 1 row228 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h228 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge229 : rowBridgeOk 272 1083 12 10 51 1 row229 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h229 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge230 : rowBridgeOk 272 1083 12 10 51 1 row230 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h230 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge231 : rowBridgeOk 272 1083 12 10 51 1 row231 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h231 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge232 : rowBridgeOk 272 1083 12 10 51 1 row232 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h232 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
