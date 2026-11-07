import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle179
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle180
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle181
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle182
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle183
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle184
/-! Bridge of the re-expanded rows 179-184 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge179 : rowBridgeOk 272 1083 12 10 51 1 row179 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h179 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge180 : rowBridgeOk 272 1083 12 10 51 1 row180 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h180 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge181 : rowBridgeOk 272 1083 12 10 51 1 row181 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h181 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge182 : rowBridgeOk 272 1083 12 10 51 1 row182 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h182 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge183 : rowBridgeOk 272 1083 12 10 51 1 row183 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h183 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge184 : rowBridgeOk 272 1083 12 10 51 1 row184 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h184 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
