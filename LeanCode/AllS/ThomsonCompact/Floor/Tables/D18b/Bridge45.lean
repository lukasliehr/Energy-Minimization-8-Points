import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows9
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle059
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle060
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle061
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle062
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle063
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle064
/-! Bridge of the re-expanded rows 59-64 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge059 : rowBridgeOk 272 1083 12 10 328 1 row059 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h059 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge060 : rowBridgeOk 272 1083 12 10 51 1 row060 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h060 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge061 : rowBridgeOk 272 1083 12 10 195 1 row061 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h061 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge062 : rowBridgeOk 272 1083 12 10 286 1 row062 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h062 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge063 : rowBridgeOk 272 1083 12 10 317 1 row063 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h063 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge064 : rowBridgeOk 272 1083 12 10 303 1 row064 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h064 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
