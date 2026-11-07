import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.Tables.D12b.Rows2
import AllS.Units.N_AI.N_fixed_tables.D12.HRows020
/-! Bridge of the re-expanded rows 20-29 to the old `FixedTables.D12` literals (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open ThomsonCompact.Floor.B

theorem bridge020 : rowBridgeOk 100 19 6 4 449 1 row020 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h020 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge021 : rowBridgeOk 100 19 6 4 379 1 row021 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h021 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge022 : rowBridgeOk 100 19 6 4 414 1 row022 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h022 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge023 : rowBridgeOk 100 19 6 4 405 1 row023 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h023 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge024 : rowBridgeOk 100 19 6 4 412 1 row024 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h024 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge025 : rowBridgeOk 100 19 6 4 114 1 row025 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h025 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge026 : rowBridgeOk 100 19 6 4 375 1 row026 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h026 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge027 : rowBridgeOk 100 19 6 4 449 1 row027 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h027 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge028 : rowBridgeOk 100 19 6 4 385 1 row028 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h028 ⟨m, h⟩ else []) = true := by decide +kernel

theorem bridge029 : rowBridgeOk 100 19 6 4 369 1 row029 (fun m => if h : m < 100 then Blueprint.CAP.FixedTables.D12.h029 ⟨m, h⟩ else []) = true := by decide +kernel

end ThomsonCompact.Floor.Tables.D12b
