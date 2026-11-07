import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle107
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle108
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle109
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle110
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle111
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle112
/-! Bridge of the re-expanded rows 107-112 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge107 : rowBridgeOk 272 1083 12 10 207 1 row107 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h107 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge108 : rowBridgeOk 272 1083 12 10 181 1 row108 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h108 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge109 : rowBridgeOk 272 1083 12 10 196 1 row109 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h109 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge110 : rowBridgeOk 272 1083 12 10 207 1 row110 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h110 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge111 : rowBridgeOk 272 1083 12 10 196 1 row111 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h111 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge112 : rowBridgeOk 272 1083 12 10 207 1 row112 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h112 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
