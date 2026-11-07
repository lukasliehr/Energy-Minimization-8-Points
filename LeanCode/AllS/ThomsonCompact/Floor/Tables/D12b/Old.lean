import AllS.Units.N_AI.N_fixed_tables.D12.Data
import ThomsonCompact.Floor.Tables.D12b.Table
import ThomsonCompact.Floor.Tables.D12b.Den
/-! The re-expanded D12 table against the old `FixedTables.D12` literals: denominators, scales, output coordinates, block ranges (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D12b
open Blueprint.CAP.FixedTables.D12

attribute [local instance] Fintype.decidableForallFintype

theorem old000 : tableDenominators ⟨0, by decide⟩ = dz000.map (fun z : ℤ => (z : ℚ) / (dq000 : ℚ)) ∧
    tableScales ⟨0, by decide⟩ = (lam000 : ℤ) ∧
    outputCoordinates ⟨0, by decide⟩ = ("F0", row000.u, row000.v) := by decide +kernel

theorem old001 : tableDenominators ⟨1, by decide⟩ = dz001.map (fun z : ℤ => (z : ℚ) / (dq001 : ℚ)) ∧
    tableScales ⟨1, by decide⟩ = (lam001 : ℤ) ∧
    outputCoordinates ⟨1, by decide⟩ = ("F0", row001.u, row001.v) := by decide +kernel

theorem old002 : tableDenominators ⟨2, by decide⟩ = dz002.map (fun z : ℤ => (z : ℚ) / (dq002 : ℚ)) ∧
    tableScales ⟨2, by decide⟩ = (lam002 : ℤ) ∧
    outputCoordinates ⟨2, by decide⟩ = ("F0", row002.u, row002.v) := by decide +kernel

theorem old003 : tableDenominators ⟨3, by decide⟩ = dz003.map (fun z : ℤ => (z : ℚ) / (dq003 : ℚ)) ∧
    tableScales ⟨3, by decide⟩ = (lam003 : ℤ) ∧
    outputCoordinates ⟨3, by decide⟩ = ("F0", row003.u, row003.v) := by decide +kernel

theorem old004 : tableDenominators ⟨4, by decide⟩ = dz004.map (fun z : ℤ => (z : ℚ) / (dq004 : ℚ)) ∧
    tableScales ⟨4, by decide⟩ = (lam004 : ℤ) ∧
    outputCoordinates ⟨4, by decide⟩ = ("F0", row004.u, row004.v) := by decide +kernel

theorem old005 : tableDenominators ⟨5, by decide⟩ = dz005.map (fun z : ℤ => (z : ℚ) / (dq005 : ℚ)) ∧
    tableScales ⟨5, by decide⟩ = (lam005 : ℤ) ∧
    outputCoordinates ⟨5, by decide⟩ = ("F0", row005.u, row005.v) := by decide +kernel

theorem old006 : tableDenominators ⟨6, by decide⟩ = dz006.map (fun z : ℤ => (z : ℚ) / (dq006 : ℚ)) ∧
    tableScales ⟨6, by decide⟩ = (lam006 : ℤ) ∧
    outputCoordinates ⟨6, by decide⟩ = ("F0", row006.u, row006.v) := by decide +kernel

theorem old007 : tableDenominators ⟨7, by decide⟩ = dz007.map (fun z : ℤ => (z : ℚ) / (dq007 : ℚ)) ∧
    tableScales ⟨7, by decide⟩ = (lam007 : ℤ) ∧
    outputCoordinates ⟨7, by decide⟩ = ("F0", row007.u, row007.v) := by decide +kernel

theorem old008 : tableDenominators ⟨8, by decide⟩ = dz008.map (fun z : ℤ => (z : ℚ) / (dq008 : ℚ)) ∧
    tableScales ⟨8, by decide⟩ = (lam008 : ℤ) ∧
    outputCoordinates ⟨8, by decide⟩ = ("F0", row008.u, row008.v) := by decide +kernel

theorem old009 : tableDenominators ⟨9, by decide⟩ = dz009.map (fun z : ℤ => (z : ℚ) / (dq009 : ℚ)) ∧
    tableScales ⟨9, by decide⟩ = (lam009 : ℤ) ∧
    outputCoordinates ⟨9, by decide⟩ = ("F0", row009.u, row009.v) := by decide +kernel

theorem old010 : tableDenominators ⟨10, by decide⟩ = dz010.map (fun z : ℤ => (z : ℚ) / (dq010 : ℚ)) ∧
    tableScales ⟨10, by decide⟩ = (lam010 : ℤ) ∧
    outputCoordinates ⟨10, by decide⟩ = ("F0", row010.u, row010.v) := by decide +kernel

theorem old011 : tableDenominators ⟨11, by decide⟩ = dz011.map (fun z : ℤ => (z : ℚ) / (dq011 : ℚ)) ∧
    tableScales ⟨11, by decide⟩ = (lam011 : ℤ) ∧
    outputCoordinates ⟨11, by decide⟩ = ("F1", row011.u, row011.v) := by decide +kernel

theorem old012 : tableDenominators ⟨12, by decide⟩ = dz012.map (fun z : ℤ => (z : ℚ) / (dq012 : ℚ)) ∧
    tableScales ⟨12, by decide⟩ = (lam012 : ℤ) ∧
    outputCoordinates ⟨12, by decide⟩ = ("F1", row012.u, row012.v) := by decide +kernel

theorem old013 : tableDenominators ⟨13, by decide⟩ = dz013.map (fun z : ℤ => (z : ℚ) / (dq013 : ℚ)) ∧
    tableScales ⟨13, by decide⟩ = (lam013 : ℤ) ∧
    outputCoordinates ⟨13, by decide⟩ = ("F1", row013.u, row013.v) := by decide +kernel

theorem old014 : tableDenominators ⟨14, by decide⟩ = dz014.map (fun z : ℤ => (z : ℚ) / (dq014 : ℚ)) ∧
    tableScales ⟨14, by decide⟩ = (lam014 : ℤ) ∧
    outputCoordinates ⟨14, by decide⟩ = ("F1", row014.u, row014.v) := by decide +kernel

theorem old015 : tableDenominators ⟨15, by decide⟩ = dz015.map (fun z : ℤ => (z : ℚ) / (dq015 : ℚ)) ∧
    tableScales ⟨15, by decide⟩ = (lam015 : ℤ) ∧
    outputCoordinates ⟨15, by decide⟩ = ("M0_plus", row015.u, row015.v) := by decide +kernel

theorem old016 : tableDenominators ⟨16, by decide⟩ = dz016.map (fun z : ℤ => (z : ℚ) / (dq016 : ℚ)) ∧
    tableScales ⟨16, by decide⟩ = (lam016 : ℤ) ∧
    outputCoordinates ⟨16, by decide⟩ = ("M0_plus", row016.u, row016.v) := by decide +kernel

theorem old017 : tableDenominators ⟨17, by decide⟩ = dz017.map (fun z : ℤ => (z : ℚ) / (dq017 : ℚ)) ∧
    tableScales ⟨17, by decide⟩ = (lam017 : ℤ) ∧
    outputCoordinates ⟨17, by decide⟩ = ("M0_plus", row017.u, row017.v) := by decide +kernel

theorem old018 : tableDenominators ⟨18, by decide⟩ = dz018.map (fun z : ℤ => (z : ℚ) / (dq018 : ℚ)) ∧
    tableScales ⟨18, by decide⟩ = (lam018 : ℤ) ∧
    outputCoordinates ⟨18, by decide⟩ = ("M0_plus", row018.u, row018.v) := by decide +kernel

theorem old019 : tableDenominators ⟨19, by decide⟩ = dz019.map (fun z : ℤ => (z : ℚ) / (dq019 : ℚ)) ∧
    tableScales ⟨19, by decide⟩ = (lam019 : ℤ) ∧
    outputCoordinates ⟨19, by decide⟩ = ("M0_plus", row019.u, row019.v) := by decide +kernel

theorem old020 : tableDenominators ⟨20, by decide⟩ = dz020.map (fun z : ℤ => (z : ℚ) / (dq020 : ℚ)) ∧
    tableScales ⟨20, by decide⟩ = (lam020 : ℤ) ∧
    outputCoordinates ⟨20, by decide⟩ = ("M0_plus", row020.u, row020.v) := by decide +kernel

theorem old021 : tableDenominators ⟨21, by decide⟩ = dz021.map (fun z : ℤ => (z : ℚ) / (dq021 : ℚ)) ∧
    tableScales ⟨21, by decide⟩ = (lam021 : ℤ) ∧
    outputCoordinates ⟨21, by decide⟩ = ("M0_plus", row021.u, row021.v) := by decide +kernel

theorem old022 : tableDenominators ⟨22, by decide⟩ = dz022.map (fun z : ℤ => (z : ℚ) / (dq022 : ℚ)) ∧
    tableScales ⟨22, by decide⟩ = (lam022 : ℤ) ∧
    outputCoordinates ⟨22, by decide⟩ = ("M0_plus", row022.u, row022.v) := by decide +kernel

theorem old023 : tableDenominators ⟨23, by decide⟩ = dz023.map (fun z : ℤ => (z : ℚ) / (dq023 : ℚ)) ∧
    tableScales ⟨23, by decide⟩ = (lam023 : ℤ) ∧
    outputCoordinates ⟨23, by decide⟩ = ("M0_plus", row023.u, row023.v) := by decide +kernel

theorem old024 : tableDenominators ⟨24, by decide⟩ = dz024.map (fun z : ℤ => (z : ℚ) / (dq024 : ℚ)) ∧
    tableScales ⟨24, by decide⟩ = (lam024 : ℤ) ∧
    outputCoordinates ⟨24, by decide⟩ = ("M0_plus", row024.u, row024.v) := by decide +kernel

theorem old025 : tableDenominators ⟨25, by decide⟩ = dz025.map (fun z : ℤ => (z : ℚ) / (dq025 : ℚ)) ∧
    tableScales ⟨25, by decide⟩ = (lam025 : ℤ) ∧
    outputCoordinates ⟨25, by decide⟩ = ("M0_plus", row025.u, row025.v) := by decide +kernel

theorem old026 : tableDenominators ⟨26, by decide⟩ = dz026.map (fun z : ℤ => (z : ℚ) / (dq026 : ℚ)) ∧
    tableScales ⟨26, by decide⟩ = (lam026 : ℤ) ∧
    outputCoordinates ⟨26, by decide⟩ = ("M0_plus", row026.u, row026.v) := by decide +kernel

theorem old027 : tableDenominators ⟨27, by decide⟩ = dz027.map (fun z : ℤ => (z : ℚ) / (dq027 : ℚ)) ∧
    tableScales ⟨27, by decide⟩ = (lam027 : ℤ) ∧
    outputCoordinates ⟨27, by decide⟩ = ("M0_plus", row027.u, row027.v) := by decide +kernel

theorem old028 : tableDenominators ⟨28, by decide⟩ = dz028.map (fun z : ℤ => (z : ℚ) / (dq028 : ℚ)) ∧
    tableScales ⟨28, by decide⟩ = (lam028 : ℤ) ∧
    outputCoordinates ⟨28, by decide⟩ = ("M0_plus", row028.u, row028.v) := by decide +kernel

theorem old029 : tableDenominators ⟨29, by decide⟩ = dz029.map (fun z : ℤ => (z : ℚ) / (dq029 : ℚ)) ∧
    tableScales ⟨29, by decide⟩ = (lam029 : ℤ) ∧
    outputCoordinates ⟨29, by decide⟩ = ("M0_plus", row029.u, row029.v) := by decide +kernel

theorem old030 : tableDenominators ⟨30, by decide⟩ = dz030.map (fun z : ℤ => (z : ℚ) / (dq030 : ℚ)) ∧
    tableScales ⟨30, by decide⟩ = (lam030 : ℤ) ∧
    outputCoordinates ⟨30, by decide⟩ = ("M0_plus", row030.u, row030.v) := by decide +kernel

theorem old031 : tableDenominators ⟨31, by decide⟩ = dz031.map (fun z : ℤ => (z : ℚ) / (dq031 : ℚ)) ∧
    tableScales ⟨31, by decide⟩ = (lam031 : ℤ) ∧
    outputCoordinates ⟨31, by decide⟩ = ("M0_plus", row031.u, row031.v) := by decide +kernel

theorem old032 : tableDenominators ⟨32, by decide⟩ = dz032.map (fun z : ℤ => (z : ℚ) / (dq032 : ℚ)) ∧
    tableScales ⟨32, by decide⟩ = (lam032 : ℤ) ∧
    outputCoordinates ⟨32, by decide⟩ = ("M0_plus", row032.u, row032.v) := by decide +kernel

theorem old033 : tableDenominators ⟨33, by decide⟩ = dz033.map (fun z : ℤ => (z : ℚ) / (dq033 : ℚ)) ∧
    tableScales ⟨33, by decide⟩ = (lam033 : ℤ) ∧
    outputCoordinates ⟨33, by decide⟩ = ("M0_plus", row033.u, row033.v) := by decide +kernel

theorem old034 : tableDenominators ⟨34, by decide⟩ = dz034.map (fun z : ℤ => (z : ℚ) / (dq034 : ℚ)) ∧
    tableScales ⟨34, by decide⟩ = (lam034 : ℤ) ∧
    outputCoordinates ⟨34, by decide⟩ = ("M0_plus", row034.u, row034.v) := by decide +kernel

theorem old035 : tableDenominators ⟨35, by decide⟩ = dz035.map (fun z : ℤ => (z : ℚ) / (dq035 : ℚ)) ∧
    tableScales ⟨35, by decide⟩ = (lam035 : ℤ) ∧
    outputCoordinates ⟨35, by decide⟩ = ("M0_plus", row035.u, row035.v) := by decide +kernel

theorem old036 : tableDenominators ⟨36, by decide⟩ = dz036.map (fun z : ℤ => (z : ℚ) / (dq036 : ℚ)) ∧
    tableScales ⟨36, by decide⟩ = (lam036 : ℤ) ∧
    outputCoordinates ⟨36, by decide⟩ = ("M0_plus", row036.u, row036.v) := by decide +kernel

theorem old037 : tableDenominators ⟨37, by decide⟩ = dz037.map (fun z : ℤ => (z : ℚ) / (dq037 : ℚ)) ∧
    tableScales ⟨37, by decide⟩ = (lam037 : ℤ) ∧
    outputCoordinates ⟨37, by decide⟩ = ("M0_plus", row037.u, row037.v) := by decide +kernel

theorem old038 : tableDenominators ⟨38, by decide⟩ = dz038.map (fun z : ℤ => (z : ℚ) / (dq038 : ℚ)) ∧
    tableScales ⟨38, by decide⟩ = (lam038 : ℤ) ∧
    outputCoordinates ⟨38, by decide⟩ = ("M0_plus", row038.u, row038.v) := by decide +kernel

theorem old039 : tableDenominators ⟨39, by decide⟩ = dz039.map (fun z : ℤ => (z : ℚ) / (dq039 : ℚ)) ∧
    tableScales ⟨39, by decide⟩ = (lam039 : ℤ) ∧
    outputCoordinates ⟨39, by decide⟩ = ("M0_plus", row039.u, row039.v) := by decide +kernel

theorem old040 : tableDenominators ⟨40, by decide⟩ = dz040.map (fun z : ℤ => (z : ℚ) / (dq040 : ℚ)) ∧
    tableScales ⟨40, by decide⟩ = (lam040 : ℤ) ∧
    outputCoordinates ⟨40, by decide⟩ = ("M0_plus", row040.u, row040.v) := by decide +kernel

theorem old041 : tableDenominators ⟨41, by decide⟩ = dz041.map (fun z : ℤ => (z : ℚ) / (dq041 : ℚ)) ∧
    tableScales ⟨41, by decide⟩ = (lam041 : ℤ) ∧
    outputCoordinates ⟨41, by decide⟩ = ("M0_plus", row041.u, row041.v) := by decide +kernel

theorem old042 : tableDenominators ⟨42, by decide⟩ = dz042.map (fun z : ℤ => (z : ℚ) / (dq042 : ℚ)) ∧
    tableScales ⟨42, by decide⟩ = (lam042 : ℤ) ∧
    outputCoordinates ⟨42, by decide⟩ = ("M0_plus", row042.u, row042.v) := by decide +kernel

theorem old043 : tableDenominators ⟨43, by decide⟩ = dz043.map (fun z : ℤ => (z : ℚ) / (dq043 : ℚ)) ∧
    tableScales ⟨43, by decide⟩ = (lam043 : ℤ) ∧
    outputCoordinates ⟨43, by decide⟩ = ("M0_plus", row043.u, row043.v) := by decide +kernel

theorem old044 : tableDenominators ⟨44, by decide⟩ = dz044.map (fun z : ℤ => (z : ℚ) / (dq044 : ℚ)) ∧
    tableScales ⟨44, by decide⟩ = (lam044 : ℤ) ∧
    outputCoordinates ⟨44, by decide⟩ = ("M0_plus", row044.u, row044.v) := by decide +kernel

theorem old045 : tableDenominators ⟨45, by decide⟩ = dz045.map (fun z : ℤ => (z : ℚ) / (dq045 : ℚ)) ∧
    tableScales ⟨45, by decide⟩ = (lam045 : ℤ) ∧
    outputCoordinates ⟨45, by decide⟩ = ("M0_plus", row045.u, row045.v) := by decide +kernel

theorem old046 : tableDenominators ⟨46, by decide⟩ = dz046.map (fun z : ℤ => (z : ℚ) / (dq046 : ℚ)) ∧
    tableScales ⟨46, by decide⟩ = (lam046 : ℤ) ∧
    outputCoordinates ⟨46, by decide⟩ = ("M0_plus", row046.u, row046.v) := by decide +kernel

theorem old047 : tableDenominators ⟨47, by decide⟩ = dz047.map (fun z : ℤ => (z : ℚ) / (dq047 : ℚ)) ∧
    tableScales ⟨47, by decide⟩ = (lam047 : ℤ) ∧
    outputCoordinates ⟨47, by decide⟩ = ("M0_plus", row047.u, row047.v) := by decide +kernel

theorem old048 : tableDenominators ⟨48, by decide⟩ = dz048.map (fun z : ℤ => (z : ℚ) / (dq048 : ℚ)) ∧
    tableScales ⟨48, by decide⟩ = (lam048 : ℤ) ∧
    outputCoordinates ⟨48, by decide⟩ = ("M0_plus", row048.u, row048.v) := by decide +kernel

theorem old049 : tableDenominators ⟨49, by decide⟩ = dz049.map (fun z : ℤ => (z : ℚ) / (dq049 : ℚ)) ∧
    tableScales ⟨49, by decide⟩ = (lam049 : ℤ) ∧
    outputCoordinates ⟨49, by decide⟩ = ("M0_plus", row049.u, row049.v) := by decide +kernel

theorem old050 : tableDenominators ⟨50, by decide⟩ = dz050.map (fun z : ℤ => (z : ℚ) / (dq050 : ℚ)) ∧
    tableScales ⟨50, by decide⟩ = (lam050 : ℤ) ∧
    outputCoordinates ⟨50, by decide⟩ = ("M0_plus", row050.u, row050.v) := by decide +kernel

theorem old051 : tableDenominators ⟨51, by decide⟩ = dz051.map (fun z : ℤ => (z : ℚ) / (dq051 : ℚ)) ∧
    tableScales ⟨51, by decide⟩ = (lam051 : ℤ) ∧
    outputCoordinates ⟨51, by decide⟩ = ("M0_plus", row051.u, row051.v) := by decide +kernel

theorem old052 : tableDenominators ⟨52, by decide⟩ = dz052.map (fun z : ℤ => (z : ℚ) / (dq052 : ℚ)) ∧
    tableScales ⟨52, by decide⟩ = (lam052 : ℤ) ∧
    outputCoordinates ⟨52, by decide⟩ = ("M0_plus", row052.u, row052.v) := by decide +kernel

theorem old053 : tableDenominators ⟨53, by decide⟩ = dz053.map (fun z : ℤ => (z : ℚ) / (dq053 : ℚ)) ∧
    tableScales ⟨53, by decide⟩ = (lam053 : ℤ) ∧
    outputCoordinates ⟨53, by decide⟩ = ("M0_plus", row053.u, row053.v) := by decide +kernel

theorem old054 : tableDenominators ⟨54, by decide⟩ = dz054.map (fun z : ℤ => (z : ℚ) / (dq054 : ℚ)) ∧
    tableScales ⟨54, by decide⟩ = (lam054 : ℤ) ∧
    outputCoordinates ⟨54, by decide⟩ = ("M0_plus", row054.u, row054.v) := by decide +kernel

theorem old055 : tableDenominators ⟨55, by decide⟩ = dz055.map (fun z : ℤ => (z : ℚ) / (dq055 : ℚ)) ∧
    tableScales ⟨55, by decide⟩ = (lam055 : ℤ) ∧
    outputCoordinates ⟨55, by decide⟩ = ("M0_plus", row055.u, row055.v) := by decide +kernel

theorem old056 : tableDenominators ⟨56, by decide⟩ = dz056.map (fun z : ℤ => (z : ℚ) / (dq056 : ℚ)) ∧
    tableScales ⟨56, by decide⟩ = (lam056 : ℤ) ∧
    outputCoordinates ⟨56, by decide⟩ = ("M0_plus", row056.u, row056.v) := by decide +kernel

theorem old057 : tableDenominators ⟨57, by decide⟩ = dz057.map (fun z : ℤ => (z : ℚ) / (dq057 : ℚ)) ∧
    tableScales ⟨57, by decide⟩ = (lam057 : ℤ) ∧
    outputCoordinates ⟨57, by decide⟩ = ("M0_plus", row057.u, row057.v) := by decide +kernel

theorem old058 : tableDenominators ⟨58, by decide⟩ = dz058.map (fun z : ℤ => (z : ℚ) / (dq058 : ℚ)) ∧
    tableScales ⟨58, by decide⟩ = (lam058 : ℤ) ∧
    outputCoordinates ⟨58, by decide⟩ = ("M0_plus", row058.u, row058.v) := by decide +kernel

theorem old059 : tableDenominators ⟨59, by decide⟩ = dz059.map (fun z : ℤ => (z : ℚ) / (dq059 : ℚ)) ∧
    tableScales ⟨59, by decide⟩ = (lam059 : ℤ) ∧
    outputCoordinates ⟨59, by decide⟩ = ("M0_plus", row059.u, row059.v) := by decide +kernel

theorem old060 : tableDenominators ⟨60, by decide⟩ = dz060.map (fun z : ℤ => (z : ℚ) / (dq060 : ℚ)) ∧
    tableScales ⟨60, by decide⟩ = (lam060 : ℤ) ∧
    outputCoordinates ⟨60, by decide⟩ = ("M0_plus", row060.u, row060.v) := by decide +kernel

theorem old061 : tableDenominators ⟨61, by decide⟩ = dz061.map (fun z : ℤ => (z : ℚ) / (dq061 : ℚ)) ∧
    tableScales ⟨61, by decide⟩ = (lam061 : ℤ) ∧
    outputCoordinates ⟨61, by decide⟩ = ("M0_plus", row061.u, row061.v) := by decide +kernel

theorem old062 : tableDenominators ⟨62, by decide⟩ = dz062.map (fun z : ℤ => (z : ℚ) / (dq062 : ℚ)) ∧
    tableScales ⟨62, by decide⟩ = (lam062 : ℤ) ∧
    outputCoordinates ⟨62, by decide⟩ = ("M0_plus", row062.u, row062.v) := by decide +kernel

theorem old063 : tableDenominators ⟨63, by decide⟩ = dz063.map (fun z : ℤ => (z : ℚ) / (dq063 : ℚ)) ∧
    tableScales ⟨63, by decide⟩ = (lam063 : ℤ) ∧
    outputCoordinates ⟨63, by decide⟩ = ("M0_plus", row063.u, row063.v) := by decide +kernel

theorem old064 : tableDenominators ⟨64, by decide⟩ = dz064.map (fun z : ℤ => (z : ℚ) / (dq064 : ℚ)) ∧
    tableScales ⟨64, by decide⟩ = (lam064 : ℤ) ∧
    outputCoordinates ⟨64, by decide⟩ = ("M0_plus", row064.u, row064.v) := by decide +kernel

theorem old065 : tableDenominators ⟨65, by decide⟩ = dz065.map (fun z : ℤ => (z : ℚ) / (dq065 : ℚ)) ∧
    tableScales ⟨65, by decide⟩ = (lam065 : ℤ) ∧
    outputCoordinates ⟨65, by decide⟩ = ("M0_plus", row065.u, row065.v) := by decide +kernel

theorem old066 : tableDenominators ⟨66, by decide⟩ = dz066.map (fun z : ℤ => (z : ℚ) / (dq066 : ℚ)) ∧
    tableScales ⟨66, by decide⟩ = (lam066 : ℤ) ∧
    outputCoordinates ⟨66, by decide⟩ = ("M0_plus", row066.u, row066.v) := by decide +kernel

theorem old067 : tableDenominators ⟨67, by decide⟩ = dz067.map (fun z : ℤ => (z : ℚ) / (dq067 : ℚ)) ∧
    tableScales ⟨67, by decide⟩ = (lam067 : ℤ) ∧
    outputCoordinates ⟨67, by decide⟩ = ("M0_plus", row067.u, row067.v) := by decide +kernel

theorem old068 : tableDenominators ⟨68, by decide⟩ = dz068.map (fun z : ℤ => (z : ℚ) / (dq068 : ℚ)) ∧
    tableScales ⟨68, by decide⟩ = (lam068 : ℤ) ∧
    outputCoordinates ⟨68, by decide⟩ = ("M0_plus", row068.u, row068.v) := by decide +kernel

theorem old069 : tableDenominators ⟨69, by decide⟩ = dz069.map (fun z : ℤ => (z : ℚ) / (dq069 : ℚ)) ∧
    tableScales ⟨69, by decide⟩ = (lam069 : ℤ) ∧
    outputCoordinates ⟨69, by decide⟩ = ("M0_plus", row069.u, row069.v) := by decide +kernel

theorem old070 : tableDenominators ⟨70, by decide⟩ = dz070.map (fun z : ℤ => (z : ℚ) / (dq070 : ℚ)) ∧
    tableScales ⟨70, by decide⟩ = (lam070 : ℤ) ∧
    outputCoordinates ⟨70, by decide⟩ = ("M0_plus", row070.u, row070.v) := by decide +kernel

theorem old071 : tableDenominators ⟨71, by decide⟩ = dz071.map (fun z : ℤ => (z : ℚ) / (dq071 : ℚ)) ∧
    tableScales ⟨71, by decide⟩ = (lam071 : ℤ) ∧
    outputCoordinates ⟨71, by decide⟩ = ("M0_plus", row071.u, row071.v) := by decide +kernel

theorem old072 : tableDenominators ⟨72, by decide⟩ = dz072.map (fun z : ℤ => (z : ℚ) / (dq072 : ℚ)) ∧
    tableScales ⟨72, by decide⟩ = (lam072 : ℤ) ∧
    outputCoordinates ⟨72, by decide⟩ = ("M0_plus", row072.u, row072.v) := by decide +kernel

theorem old073 : tableDenominators ⟨73, by decide⟩ = dz073.map (fun z : ℤ => (z : ℚ) / (dq073 : ℚ)) ∧
    tableScales ⟨73, by decide⟩ = (lam073 : ℤ) ∧
    outputCoordinates ⟨73, by decide⟩ = ("M0_plus", row073.u, row073.v) := by decide +kernel

theorem old074 : tableDenominators ⟨74, by decide⟩ = dz074.map (fun z : ℤ => (z : ℚ) / (dq074 : ℚ)) ∧
    tableScales ⟨74, by decide⟩ = (lam074 : ℤ) ∧
    outputCoordinates ⟨74, by decide⟩ = ("M0_plus", row074.u, row074.v) := by decide +kernel

theorem old075 : tableDenominators ⟨75, by decide⟩ = dz075.map (fun z : ℤ => (z : ℚ) / (dq075 : ℚ)) ∧
    tableScales ⟨75, by decide⟩ = (lam075 : ℤ) ∧
    outputCoordinates ⟨75, by decide⟩ = ("M0_plus", row075.u, row075.v) := by decide +kernel

theorem old076 : tableDenominators ⟨76, by decide⟩ = dz076.map (fun z : ℤ => (z : ℚ) / (dq076 : ℚ)) ∧
    tableScales ⟨76, by decide⟩ = (lam076 : ℤ) ∧
    outputCoordinates ⟨76, by decide⟩ = ("M0_plus", row076.u, row076.v) := by decide +kernel

theorem old077 : tableDenominators ⟨77, by decide⟩ = dz077.map (fun z : ℤ => (z : ℚ) / (dq077 : ℚ)) ∧
    tableScales ⟨77, by decide⟩ = (lam077 : ℤ) ∧
    outputCoordinates ⟨77, by decide⟩ = ("M0_plus", row077.u, row077.v) := by decide +kernel

theorem old078 : tableDenominators ⟨78, by decide⟩ = dz078.map (fun z : ℤ => (z : ℚ) / (dq078 : ℚ)) ∧
    tableScales ⟨78, by decide⟩ = (lam078 : ℤ) ∧
    outputCoordinates ⟨78, by decide⟩ = ("M0_plus", row078.u, row078.v) := by decide +kernel

theorem old079 : tableDenominators ⟨79, by decide⟩ = dz079.map (fun z : ℤ => (z : ℚ) / (dq079 : ℚ)) ∧
    tableScales ⟨79, by decide⟩ = (lam079 : ℤ) ∧
    outputCoordinates ⟨79, by decide⟩ = ("M0_plus", row079.u, row079.v) := by decide +kernel

theorem old080 : tableDenominators ⟨80, by decide⟩ = dz080.map (fun z : ℤ => (z : ℚ) / (dq080 : ℚ)) ∧
    tableScales ⟨80, by decide⟩ = (lam080 : ℤ) ∧
    outputCoordinates ⟨80, by decide⟩ = ("M0_plus", row080.u, row080.v) := by decide +kernel

theorem old081 : tableDenominators ⟨81, by decide⟩ = dz081.map (fun z : ℤ => (z : ℚ) / (dq081 : ℚ)) ∧
    tableScales ⟨81, by decide⟩ = (lam081 : ℤ) ∧
    outputCoordinates ⟨81, by decide⟩ = ("M0_plus", row081.u, row081.v) := by decide +kernel

theorem old082 : tableDenominators ⟨82, by decide⟩ = dz082.map (fun z : ℤ => (z : ℚ) / (dq082 : ℚ)) ∧
    tableScales ⟨82, by decide⟩ = (lam082 : ℤ) ∧
    outputCoordinates ⟨82, by decide⟩ = ("M0_plus", row082.u, row082.v) := by decide +kernel

theorem old083 : tableDenominators ⟨83, by decide⟩ = dz083.map (fun z : ℤ => (z : ℚ) / (dq083 : ℚ)) ∧
    tableScales ⟨83, by decide⟩ = (lam083 : ℤ) ∧
    outputCoordinates ⟨83, by decide⟩ = ("M0_plus", row083.u, row083.v) := by decide +kernel

theorem old084 : tableDenominators ⟨84, by decide⟩ = dz084.map (fun z : ℤ => (z : ℚ) / (dq084 : ℚ)) ∧
    tableScales ⟨84, by decide⟩ = (lam084 : ℤ) ∧
    outputCoordinates ⟨84, by decide⟩ = ("M0_plus", row084.u, row084.v) := by decide +kernel

theorem old085 : tableDenominators ⟨85, by decide⟩ = dz085.map (fun z : ℤ => (z : ℚ) / (dq085 : ℚ)) ∧
    tableScales ⟨85, by decide⟩ = (lam085 : ℤ) ∧
    outputCoordinates ⟨85, by decide⟩ = ("M0_plus", row085.u, row085.v) := by decide +kernel

theorem old086 : tableDenominators ⟨86, by decide⟩ = dz086.map (fun z : ℤ => (z : ℚ) / (dq086 : ℚ)) ∧
    tableScales ⟨86, by decide⟩ = (lam086 : ℤ) ∧
    outputCoordinates ⟨86, by decide⟩ = ("M0_plus", row086.u, row086.v) := by decide +kernel

theorem old087 : tableDenominators ⟨87, by decide⟩ = dz087.map (fun z : ℤ => (z : ℚ) / (dq087 : ℚ)) ∧
    tableScales ⟨87, by decide⟩ = (lam087 : ℤ) ∧
    outputCoordinates ⟨87, by decide⟩ = ("M0_plus", row087.u, row087.v) := by decide +kernel

theorem old088 : tableDenominators ⟨88, by decide⟩ = dz088.map (fun z : ℤ => (z : ℚ) / (dq088 : ℚ)) ∧
    tableScales ⟨88, by decide⟩ = (lam088 : ℤ) ∧
    outputCoordinates ⟨88, by decide⟩ = ("M0_plus", row088.u, row088.v) := by decide +kernel

theorem old089 : tableDenominators ⟨89, by decide⟩ = dz089.map (fun z : ℤ => (z : ℚ) / (dq089 : ℚ)) ∧
    tableScales ⟨89, by decide⟩ = (lam089 : ℤ) ∧
    outputCoordinates ⟨89, by decide⟩ = ("M0_plus", row089.u, row089.v) := by decide +kernel

theorem old090 : tableDenominators ⟨90, by decide⟩ = dz090.map (fun z : ℤ => (z : ℚ) / (dq090 : ℚ)) ∧
    tableScales ⟨90, by decide⟩ = (lam090 : ℤ) ∧
    outputCoordinates ⟨90, by decide⟩ = ("M0_plus", row090.u, row090.v) := by decide +kernel

theorem old091 : tableDenominators ⟨91, by decide⟩ = dz091.map (fun z : ℤ => (z : ℚ) / (dq091 : ℚ)) ∧
    tableScales ⟨91, by decide⟩ = (lam091 : ℤ) ∧
    outputCoordinates ⟨91, by decide⟩ = ("M0_plus", row091.u, row091.v) := by decide +kernel

theorem old092 : tableDenominators ⟨92, by decide⟩ = dz092.map (fun z : ℤ => (z : ℚ) / (dq092 : ℚ)) ∧
    tableScales ⟨92, by decide⟩ = (lam092 : ℤ) ∧
    outputCoordinates ⟨92, by decide⟩ = ("M0_plus", row092.u, row092.v) := by decide +kernel

theorem old093 : tableDenominators ⟨93, by decide⟩ = dz093.map (fun z : ℤ => (z : ℚ) / (dq093 : ℚ)) ∧
    tableScales ⟨93, by decide⟩ = (lam093 : ℤ) ∧
    outputCoordinates ⟨93, by decide⟩ = ("M0_plus", row093.u, row093.v) := by decide +kernel

theorem old094 : tableDenominators ⟨94, by decide⟩ = dz094.map (fun z : ℤ => (z : ℚ) / (dq094 : ℚ)) ∧
    tableScales ⟨94, by decide⟩ = (lam094 : ℤ) ∧
    outputCoordinates ⟨94, by decide⟩ = ("M0_standard", row094.u, row094.v) := by decide +kernel

theorem old095 : tableDenominators ⟨95, by decide⟩ = dz095.map (fun z : ℤ => (z : ℚ) / (dq095 : ℚ)) ∧
    tableScales ⟨95, by decide⟩ = (lam095 : ℤ) ∧
    outputCoordinates ⟨95, by decide⟩ = ("M0_standard", row095.u, row095.v) := by decide +kernel

theorem old096 : tableDenominators ⟨96, by decide⟩ = dz096.map (fun z : ℤ => (z : ℚ) / (dq096 : ℚ)) ∧
    tableScales ⟨96, by decide⟩ = (lam096 : ℤ) ∧
    outputCoordinates ⟨96, by decide⟩ = ("M0_standard", row096.u, row096.v) := by decide +kernel

theorem old097 : tableDenominators ⟨97, by decide⟩ = dz097.map (fun z : ℤ => (z : ℚ) / (dq097 : ℚ)) ∧
    tableScales ⟨97, by decide⟩ = (lam097 : ℤ) ∧
    outputCoordinates ⟨97, by decide⟩ = ("M0_standard", row097.u, row097.v) := by decide +kernel

theorem old098 : tableDenominators ⟨98, by decide⟩ = dz098.map (fun z : ℤ => (z : ℚ) / (dq098 : ℚ)) ∧
    tableScales ⟨98, by decide⟩ = (lam098 : ℤ) ∧
    outputCoordinates ⟨98, by decide⟩ = ("M0_standard", row098.u, row098.v) := by decide +kernel

theorem old099 : tableDenominators ⟨99, by decide⟩ = dz099.map (fun z : ℤ => (z : ℚ) / (dq099 : ℚ)) ∧
    tableScales ⟨99, by decide⟩ = (lam099 : ℤ) ∧
    outputCoordinates ⟨99, by decide⟩ = ("M0_standard", row099.u, row099.v) := by decide +kernel

theorem namesF0 : ∀ k : Fin 100, (outputCoordinates k).1 = "F0" ↔ (0 ≤ k.val ∧ k.val < 0 + 11) := by
  decide +kernel

theorem namesF1 : ∀ k : Fin 100, (outputCoordinates k).1 = "F1" ↔ (11 ≤ k.val ∧ k.val < 11 + 4) := by
  decide +kernel

theorem namesM0plus : ∀ k : Fin 100, (outputCoordinates k).1 = "M0_plus" ↔ (15 ≤ k.val ∧ k.val < 15 + 79) := by
  decide +kernel

theorem namesM0standard : ∀ k : Fin 100, (outputCoordinates k).1 = "M0_standard" ↔ (94 ≤ k.val ∧ k.val < 94 + 6) := by
  decide +kernel

end ThomsonCompact.Floor.Tables.D12b
