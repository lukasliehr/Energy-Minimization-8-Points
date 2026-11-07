import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows9
import AllS.Units.N_AI.N_fixed_tables.D12.HRows090
/-! Bridge of the re-expanded rows 90-99 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge090 : rowBridgeOk 100 19 6 4 3 1 row090 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h090 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge091 : rowBridgeOk 100 19 6 4 3 1 row091 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h091 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge092 : rowBridgeOk 100 19 6 4 3 1 row092 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h092 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge093 : rowBridgeOk 100 19 6 4 3 1 row093 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h093 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge094 : rowBridgeOk 100 19 6 4 317 1 row094 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h094 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge095 : rowBridgeOk 100 19 6 4 329 1 row095 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h095 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge096 : rowBridgeOk 100 19 6 4 316 1 row096 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h096 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge097 : rowBridgeOk 100 19 6 4 3 1 row097 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h097 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge098 : rowBridgeOk 100 19 6 4 4 1 row098 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h098 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge099 : rowBridgeOk 100 19 6 4 3 1 row099 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h099 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
