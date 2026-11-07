import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle173
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle174
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle175
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle176
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle177
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle178
/-! Bridge of the re-expanded rows 173-178 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge173 : rowBridgeOk 272 1083 12 10 51 1 row173 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h173 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge174 : rowBridgeOk 272 1083 12 10 51 1 row174 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h174 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge175 : rowBridgeOk 272 1083 12 10 51 1 row175 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h175 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge176 : rowBridgeOk 272 1083 12 10 51 1 row176 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h176 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge177 : rowBridgeOk 272 1083 12 10 51 1 row177 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h177 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge178 : rowBridgeOk 272 1083 12 10 51 1 row178 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h178 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
