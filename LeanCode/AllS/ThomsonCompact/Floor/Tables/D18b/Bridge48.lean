import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D18b.Rows10
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle077
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle078
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle079
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle080
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle081
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle082
/-! Bridge of the re-expanded rows 77-82 to the old `FixedTables.D18` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open ThomsonCompact.Floor.B

theorem bridge077 : rowBridgeOk 272 1083 12 10 51 1 row077 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h077 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge078 : rowBridgeOk 272 1083 12 10 51 1 row078 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h078 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge079 : rowBridgeOk 272 1083 12 10 195 1 row079 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h079 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge080 : rowBridgeOk 272 1083 12 10 207 1 row080 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h080 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge081 : rowBridgeOk 272 1083 12 10 206 1 row081 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h081 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge082 : rowBridgeOk 272 1083 12 10 51 1 row082 (fun m => if h : m < 272 then Blueprint.CAP.FixedTables.D18.h082 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D18b
