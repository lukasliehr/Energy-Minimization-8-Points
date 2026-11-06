import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle119
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle120
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle121
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle122
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle123
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle124
/-! Bridge of the re-expanded rows 119-124 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge119 : rowBridgeOk 272 1083 12 10 51 1 row119 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h119 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge120 : rowBridgeOk 272 1083 12 10 51 1 row120 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h120 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge121 : rowBridgeOk 272 1083 12 10 51 1 row121 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h121 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge122 : rowBridgeOk 272 1083 12 10 51 1 row122 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h122 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge123 : rowBridgeOk 272 1083 12 10 51 1 row123 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h123 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge124 : rowBridgeOk 272 1083 12 10 51 1 row124 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h124 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
