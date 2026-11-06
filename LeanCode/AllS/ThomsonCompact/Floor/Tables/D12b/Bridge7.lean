import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows7
import AllS.Units.N_AI.N_fixed_tables.D12.HRows070
/-! Bridge of the re-expanded rows 70-79 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge070 : rowBridgeOk 100 19 6 4 3 1 row070 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h070 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge071 : rowBridgeOk 100 19 6 4 63 1 row071 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h071 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge072 : rowBridgeOk 100 19 6 4 3 1 row072 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h072 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge073 : rowBridgeOk 100 19 6 4 3 1 row073 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h073 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge074 : rowBridgeOk 100 19 6 4 3 1 row074 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h074 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge075 : rowBridgeOk 100 19 6 4 3 1 row075 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h075 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge076 : rowBridgeOk 100 19 6 4 3 1 row076 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h076 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge077 : rowBridgeOk 100 19 6 4 3 1 row077 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h077 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge078 : rowBridgeOk 100 19 6 4 3 1 row078 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h078 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge079 : rowBridgeOk 100 19 6 4 3 1 row079 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h079 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
