import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle209
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle210
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle211
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle212
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle213
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle214
/-! Bridge of the re-expanded rows 209-214 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge209 : rowBridgeOk 272 1083 12 10 51 1 row209 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h209 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge210 : rowBridgeOk 272 1083 12 10 51 1 row210 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h210 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge211 : rowBridgeOk 272 1083 12 10 51 1 row211 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h211 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge212 : rowBridgeOk 272 1083 12 10 51 1 row212 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h212 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge213 : rowBridgeOk 272 1083 12 10 51 1 row213 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h213 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge214 : rowBridgeOk 272 1083 12 10 51 1 row214 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h214 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
