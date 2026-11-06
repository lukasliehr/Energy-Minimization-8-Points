import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle089
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle090
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle091
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle092
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle093
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle094
/-! Bridge of the re-expanded rows 89-94 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge089 : rowBridgeOk 272 1083 12 10 195 1 row089 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h089 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge090 : rowBridgeOk 272 1083 12 10 51 1 row090 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h090 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge091 : rowBridgeOk 272 1083 12 10 51 1 row091 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h091 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge092 : rowBridgeOk 272 1083 12 10 51 1 row092 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h092 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge093 : rowBridgeOk 272 1083 12 10 192 1 row093 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h093 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge094 : rowBridgeOk 272 1083 12 10 193 1 row094 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h094 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
