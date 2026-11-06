import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle071
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle072
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle073
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle074
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle075
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle076
/-! Bridge of the re-expanded rows 71-76 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge071 : rowBridgeOk 272 1083 12 10 407 1 row071 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h071 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge072 : rowBridgeOk 272 1083 12 10 221 1 row072 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h072 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge073 : rowBridgeOk 272 1083 12 10 222 1 row073 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h073 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge074 : rowBridgeOk 272 1083 12 10 302 1 row074 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h074 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge075 : rowBridgeOk 272 1083 12 10 51 1 row075 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h075 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge076 : rowBridgeOk 272 1083 12 10 51 1 row076 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h076 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
