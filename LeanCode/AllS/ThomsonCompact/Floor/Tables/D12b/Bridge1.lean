import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows1
import AllS.Units.N_AI.N_fixed_tables.D12.HRows010
/-! Bridge of the re-expanded rows 10-19 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge010 : rowBridgeOk 100 19 6 4 258 1 row010 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h010 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge011 : rowBridgeOk 100 19 6 4 158 1 row011 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h011 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge012 : rowBridgeOk 100 19 6 4 131 1 row012 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h012 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge013 : rowBridgeOk 100 19 6 4 139 1 row013 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h013 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge014 : rowBridgeOk 100 19 6 4 126 1 row014 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h014 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge015 : rowBridgeOk 100 19 6 4 428 1 row015 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h015 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge016 : rowBridgeOk 100 19 6 4 398 1 row016 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h016 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge017 : rowBridgeOk 100 19 6 4 424 1 row017 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h017 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge018 : rowBridgeOk 100 19 6 4 409 1 row018 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h018 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge019 : rowBridgeOk 100 19 6 4 441 1 row019 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h019 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
