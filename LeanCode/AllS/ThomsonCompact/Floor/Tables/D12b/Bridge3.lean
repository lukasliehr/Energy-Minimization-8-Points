import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows3
import AllS.Units.N_AI.N_fixed_tables.D12.HRows030
/-! Bridge of the re-expanded rows 30-39 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge030 : rowBridgeOk 100 19 6 4 413 1 row030 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h030 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge031 : rowBridgeOk 100 19 6 4 332 1 row031 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h031 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge032 : rowBridgeOk 100 19 6 4 379 1 row032 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h032 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge033 : rowBridgeOk 100 19 6 4 367 1 row033 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h033 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge034 : rowBridgeOk 100 19 6 4 377 1 row034 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h034 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge035 : rowBridgeOk 100 19 6 4 446 1 row035 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h035 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge036 : rowBridgeOk 100 19 6 4 413 1 row036 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h036 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge037 : rowBridgeOk 100 19 6 4 400 1 row037 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h037 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge038 : rowBridgeOk 100 19 6 4 372 1 row038 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h038 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge039 : rowBridgeOk 100 19 6 4 343 1 row039 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h039 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
