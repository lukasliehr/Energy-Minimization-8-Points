import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows9
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle047
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle048
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle049
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle050
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle051
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle052
/-! Bridge of the re-expanded rows 47-52 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge047 : rowBridgeOk 272 1083 12 10 51 1 row047 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h047 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge048 : rowBridgeOk 272 1083 12 10 233 1 row048 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h048 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge049 : rowBridgeOk 272 1083 12 10 235 1 row049 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h049 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge050 : rowBridgeOk 272 1083 12 10 309 1 row050 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h050 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge051 : rowBridgeOk 272 1083 12 10 326 1 row051 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h051 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge052 : rowBridgeOk 272 1083 12 10 51 1 row052 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h052 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
