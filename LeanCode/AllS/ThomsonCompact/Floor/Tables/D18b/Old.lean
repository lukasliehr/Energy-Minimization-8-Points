import AllS.Units.N_AI.N_fixed_tables.D18.Data
import ThomsonCompact.Floor.Tables.D18b.Table
import ThomsonCompact.Floor.Tables.D18b.Den
/-! The re-expanded D18 table against the old `FixedTables.D18` literals: denominators, scales, output coordinates, block ranges (generated). -/


set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace ThomsonCompact.Floor.Tables.D18b
open Blueprint.CAP.FixedTables.D18

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
    outputCoordinates ⟨94, by decide⟩ = ("M0_plus", row094.u, row094.v) := by decide +kernel

theorem old095 : tableDenominators ⟨95, by decide⟩ = dz095.map (fun z : ℤ => (z : ℚ) / (dq095 : ℚ)) ∧
    tableScales ⟨95, by decide⟩ = (lam095 : ℤ) ∧
    outputCoordinates ⟨95, by decide⟩ = ("M0_plus", row095.u, row095.v) := by decide +kernel

theorem old096 : tableDenominators ⟨96, by decide⟩ = dz096.map (fun z : ℤ => (z : ℚ) / (dq096 : ℚ)) ∧
    tableScales ⟨96, by decide⟩ = (lam096 : ℤ) ∧
    outputCoordinates ⟨96, by decide⟩ = ("M0_plus", row096.u, row096.v) := by decide +kernel

theorem old097 : tableDenominators ⟨97, by decide⟩ = dz097.map (fun z : ℤ => (z : ℚ) / (dq097 : ℚ)) ∧
    tableScales ⟨97, by decide⟩ = (lam097 : ℤ) ∧
    outputCoordinates ⟨97, by decide⟩ = ("M0_plus", row097.u, row097.v) := by decide +kernel

theorem old098 : tableDenominators ⟨98, by decide⟩ = dz098.map (fun z : ℤ => (z : ℚ) / (dq098 : ℚ)) ∧
    tableScales ⟨98, by decide⟩ = (lam098 : ℤ) ∧
    outputCoordinates ⟨98, by decide⟩ = ("M0_plus", row098.u, row098.v) := by decide +kernel

theorem old099 : tableDenominators ⟨99, by decide⟩ = dz099.map (fun z : ℤ => (z : ℚ) / (dq099 : ℚ)) ∧
    tableScales ⟨99, by decide⟩ = (lam099 : ℤ) ∧
    outputCoordinates ⟨99, by decide⟩ = ("M0_plus", row099.u, row099.v) := by decide +kernel

theorem old100 : tableDenominators ⟨100, by decide⟩ = dz100.map (fun z : ℤ => (z : ℚ) / (dq100 : ℚ)) ∧
    tableScales ⟨100, by decide⟩ = (lam100 : ℤ) ∧
    outputCoordinates ⟨100, by decide⟩ = ("M0_plus", row100.u, row100.v) := by decide +kernel

theorem old101 : tableDenominators ⟨101, by decide⟩ = dz101.map (fun z : ℤ => (z : ℚ) / (dq101 : ℚ)) ∧
    tableScales ⟨101, by decide⟩ = (lam101 : ℤ) ∧
    outputCoordinates ⟨101, by decide⟩ = ("M0_plus", row101.u, row101.v) := by decide +kernel

theorem old102 : tableDenominators ⟨102, by decide⟩ = dz102.map (fun z : ℤ => (z : ℚ) / (dq102 : ℚ)) ∧
    tableScales ⟨102, by decide⟩ = (lam102 : ℤ) ∧
    outputCoordinates ⟨102, by decide⟩ = ("M0_plus", row102.u, row102.v) := by decide +kernel

theorem old103 : tableDenominators ⟨103, by decide⟩ = dz103.map (fun z : ℤ => (z : ℚ) / (dq103 : ℚ)) ∧
    tableScales ⟨103, by decide⟩ = (lam103 : ℤ) ∧
    outputCoordinates ⟨103, by decide⟩ = ("M0_plus", row103.u, row103.v) := by decide +kernel

theorem old104 : tableDenominators ⟨104, by decide⟩ = dz104.map (fun z : ℤ => (z : ℚ) / (dq104 : ℚ)) ∧
    tableScales ⟨104, by decide⟩ = (lam104 : ℤ) ∧
    outputCoordinates ⟨104, by decide⟩ = ("M0_plus", row104.u, row104.v) := by decide +kernel

theorem old105 : tableDenominators ⟨105, by decide⟩ = dz105.map (fun z : ℤ => (z : ℚ) / (dq105 : ℚ)) ∧
    tableScales ⟨105, by decide⟩ = (lam105 : ℤ) ∧
    outputCoordinates ⟨105, by decide⟩ = ("M0_plus", row105.u, row105.v) := by decide +kernel

theorem old106 : tableDenominators ⟨106, by decide⟩ = dz106.map (fun z : ℤ => (z : ℚ) / (dq106 : ℚ)) ∧
    tableScales ⟨106, by decide⟩ = (lam106 : ℤ) ∧
    outputCoordinates ⟨106, by decide⟩ = ("M0_plus", row106.u, row106.v) := by decide +kernel

theorem old107 : tableDenominators ⟨107, by decide⟩ = dz107.map (fun z : ℤ => (z : ℚ) / (dq107 : ℚ)) ∧
    tableScales ⟨107, by decide⟩ = (lam107 : ℤ) ∧
    outputCoordinates ⟨107, by decide⟩ = ("M0_plus", row107.u, row107.v) := by decide +kernel

theorem old108 : tableDenominators ⟨108, by decide⟩ = dz108.map (fun z : ℤ => (z : ℚ) / (dq108 : ℚ)) ∧
    tableScales ⟨108, by decide⟩ = (lam108 : ℤ) ∧
    outputCoordinates ⟨108, by decide⟩ = ("M0_plus", row108.u, row108.v) := by decide +kernel

theorem old109 : tableDenominators ⟨109, by decide⟩ = dz109.map (fun z : ℤ => (z : ℚ) / (dq109 : ℚ)) ∧
    tableScales ⟨109, by decide⟩ = (lam109 : ℤ) ∧
    outputCoordinates ⟨109, by decide⟩ = ("M0_plus", row109.u, row109.v) := by decide +kernel

theorem old110 : tableDenominators ⟨110, by decide⟩ = dz110.map (fun z : ℤ => (z : ℚ) / (dq110 : ℚ)) ∧
    tableScales ⟨110, by decide⟩ = (lam110 : ℤ) ∧
    outputCoordinates ⟨110, by decide⟩ = ("M0_plus", row110.u, row110.v) := by decide +kernel

theorem old111 : tableDenominators ⟨111, by decide⟩ = dz111.map (fun z : ℤ => (z : ℚ) / (dq111 : ℚ)) ∧
    tableScales ⟨111, by decide⟩ = (lam111 : ℤ) ∧
    outputCoordinates ⟨111, by decide⟩ = ("M0_plus", row111.u, row111.v) := by decide +kernel

theorem old112 : tableDenominators ⟨112, by decide⟩ = dz112.map (fun z : ℤ => (z : ℚ) / (dq112 : ℚ)) ∧
    tableScales ⟨112, by decide⟩ = (lam112 : ℤ) ∧
    outputCoordinates ⟨112, by decide⟩ = ("M0_plus", row112.u, row112.v) := by decide +kernel

theorem old113 : tableDenominators ⟨113, by decide⟩ = dz113.map (fun z : ℤ => (z : ℚ) / (dq113 : ℚ)) ∧
    tableScales ⟨113, by decide⟩ = (lam113 : ℤ) ∧
    outputCoordinates ⟨113, by decide⟩ = ("M0_plus", row113.u, row113.v) := by decide +kernel

theorem old114 : tableDenominators ⟨114, by decide⟩ = dz114.map (fun z : ℤ => (z : ℚ) / (dq114 : ℚ)) ∧
    tableScales ⟨114, by decide⟩ = (lam114 : ℤ) ∧
    outputCoordinates ⟨114, by decide⟩ = ("M0_plus", row114.u, row114.v) := by decide +kernel

theorem old115 : tableDenominators ⟨115, by decide⟩ = dz115.map (fun z : ℤ => (z : ℚ) / (dq115 : ℚ)) ∧
    tableScales ⟨115, by decide⟩ = (lam115 : ℤ) ∧
    outputCoordinates ⟨115, by decide⟩ = ("M0_plus", row115.u, row115.v) := by decide +kernel

theorem old116 : tableDenominators ⟨116, by decide⟩ = dz116.map (fun z : ℤ => (z : ℚ) / (dq116 : ℚ)) ∧
    tableScales ⟨116, by decide⟩ = (lam116 : ℤ) ∧
    outputCoordinates ⟨116, by decide⟩ = ("M0_plus", row116.u, row116.v) := by decide +kernel

theorem old117 : tableDenominators ⟨117, by decide⟩ = dz117.map (fun z : ℤ => (z : ℚ) / (dq117 : ℚ)) ∧
    tableScales ⟨117, by decide⟩ = (lam117 : ℤ) ∧
    outputCoordinates ⟨117, by decide⟩ = ("M0_plus", row117.u, row117.v) := by decide +kernel

theorem old118 : tableDenominators ⟨118, by decide⟩ = dz118.map (fun z : ℤ => (z : ℚ) / (dq118 : ℚ)) ∧
    tableScales ⟨118, by decide⟩ = (lam118 : ℤ) ∧
    outputCoordinates ⟨118, by decide⟩ = ("M0_plus", row118.u, row118.v) := by decide +kernel

theorem old119 : tableDenominators ⟨119, by decide⟩ = dz119.map (fun z : ℤ => (z : ℚ) / (dq119 : ℚ)) ∧
    tableScales ⟨119, by decide⟩ = (lam119 : ℤ) ∧
    outputCoordinates ⟨119, by decide⟩ = ("M0_plus", row119.u, row119.v) := by decide +kernel

theorem old120 : tableDenominators ⟨120, by decide⟩ = dz120.map (fun z : ℤ => (z : ℚ) / (dq120 : ℚ)) ∧
    tableScales ⟨120, by decide⟩ = (lam120 : ℤ) ∧
    outputCoordinates ⟨120, by decide⟩ = ("M0_plus", row120.u, row120.v) := by decide +kernel

theorem old121 : tableDenominators ⟨121, by decide⟩ = dz121.map (fun z : ℤ => (z : ℚ) / (dq121 : ℚ)) ∧
    tableScales ⟨121, by decide⟩ = (lam121 : ℤ) ∧
    outputCoordinates ⟨121, by decide⟩ = ("M0_plus", row121.u, row121.v) := by decide +kernel

theorem old122 : tableDenominators ⟨122, by decide⟩ = dz122.map (fun z : ℤ => (z : ℚ) / (dq122 : ℚ)) ∧
    tableScales ⟨122, by decide⟩ = (lam122 : ℤ) ∧
    outputCoordinates ⟨122, by decide⟩ = ("M0_plus", row122.u, row122.v) := by decide +kernel

theorem old123 : tableDenominators ⟨123, by decide⟩ = dz123.map (fun z : ℤ => (z : ℚ) / (dq123 : ℚ)) ∧
    tableScales ⟨123, by decide⟩ = (lam123 : ℤ) ∧
    outputCoordinates ⟨123, by decide⟩ = ("M0_plus", row123.u, row123.v) := by decide +kernel

theorem old124 : tableDenominators ⟨124, by decide⟩ = dz124.map (fun z : ℤ => (z : ℚ) / (dq124 : ℚ)) ∧
    tableScales ⟨124, by decide⟩ = (lam124 : ℤ) ∧
    outputCoordinates ⟨124, by decide⟩ = ("M0_plus", row124.u, row124.v) := by decide +kernel

theorem old125 : tableDenominators ⟨125, by decide⟩ = dz125.map (fun z : ℤ => (z : ℚ) / (dq125 : ℚ)) ∧
    tableScales ⟨125, by decide⟩ = (lam125 : ℤ) ∧
    outputCoordinates ⟨125, by decide⟩ = ("M0_plus", row125.u, row125.v) := by decide +kernel

theorem old126 : tableDenominators ⟨126, by decide⟩ = dz126.map (fun z : ℤ => (z : ℚ) / (dq126 : ℚ)) ∧
    tableScales ⟨126, by decide⟩ = (lam126 : ℤ) ∧
    outputCoordinates ⟨126, by decide⟩ = ("M0_plus", row126.u, row126.v) := by decide +kernel

theorem old127 : tableDenominators ⟨127, by decide⟩ = dz127.map (fun z : ℤ => (z : ℚ) / (dq127 : ℚ)) ∧
    tableScales ⟨127, by decide⟩ = (lam127 : ℤ) ∧
    outputCoordinates ⟨127, by decide⟩ = ("M0_plus", row127.u, row127.v) := by decide +kernel

theorem old128 : tableDenominators ⟨128, by decide⟩ = dz128.map (fun z : ℤ => (z : ℚ) / (dq128 : ℚ)) ∧
    tableScales ⟨128, by decide⟩ = (lam128 : ℤ) ∧
    outputCoordinates ⟨128, by decide⟩ = ("M0_plus", row128.u, row128.v) := by decide +kernel

theorem old129 : tableDenominators ⟨129, by decide⟩ = dz129.map (fun z : ℤ => (z : ℚ) / (dq129 : ℚ)) ∧
    tableScales ⟨129, by decide⟩ = (lam129 : ℤ) ∧
    outputCoordinates ⟨129, by decide⟩ = ("M0_plus", row129.u, row129.v) := by decide +kernel

theorem old130 : tableDenominators ⟨130, by decide⟩ = dz130.map (fun z : ℤ => (z : ℚ) / (dq130 : ℚ)) ∧
    tableScales ⟨130, by decide⟩ = (lam130 : ℤ) ∧
    outputCoordinates ⟨130, by decide⟩ = ("M0_plus", row130.u, row130.v) := by decide +kernel

theorem old131 : tableDenominators ⟨131, by decide⟩ = dz131.map (fun z : ℤ => (z : ℚ) / (dq131 : ℚ)) ∧
    tableScales ⟨131, by decide⟩ = (lam131 : ℤ) ∧
    outputCoordinates ⟨131, by decide⟩ = ("M0_plus", row131.u, row131.v) := by decide +kernel

theorem old132 : tableDenominators ⟨132, by decide⟩ = dz132.map (fun z : ℤ => (z : ℚ) / (dq132 : ℚ)) ∧
    tableScales ⟨132, by decide⟩ = (lam132 : ℤ) ∧
    outputCoordinates ⟨132, by decide⟩ = ("M0_plus", row132.u, row132.v) := by decide +kernel

theorem old133 : tableDenominators ⟨133, by decide⟩ = dz133.map (fun z : ℤ => (z : ℚ) / (dq133 : ℚ)) ∧
    tableScales ⟨133, by decide⟩ = (lam133 : ℤ) ∧
    outputCoordinates ⟨133, by decide⟩ = ("M0_plus", row133.u, row133.v) := by decide +kernel

theorem old134 : tableDenominators ⟨134, by decide⟩ = dz134.map (fun z : ℤ => (z : ℚ) / (dq134 : ℚ)) ∧
    tableScales ⟨134, by decide⟩ = (lam134 : ℤ) ∧
    outputCoordinates ⟨134, by decide⟩ = ("M0_plus", row134.u, row134.v) := by decide +kernel

theorem old135 : tableDenominators ⟨135, by decide⟩ = dz135.map (fun z : ℤ => (z : ℚ) / (dq135 : ℚ)) ∧
    tableScales ⟨135, by decide⟩ = (lam135 : ℤ) ∧
    outputCoordinates ⟨135, by decide⟩ = ("M0_plus", row135.u, row135.v) := by decide +kernel

theorem old136 : tableDenominators ⟨136, by decide⟩ = dz136.map (fun z : ℤ => (z : ℚ) / (dq136 : ℚ)) ∧
    tableScales ⟨136, by decide⟩ = (lam136 : ℤ) ∧
    outputCoordinates ⟨136, by decide⟩ = ("M0_plus", row136.u, row136.v) := by decide +kernel

theorem old137 : tableDenominators ⟨137, by decide⟩ = dz137.map (fun z : ℤ => (z : ℚ) / (dq137 : ℚ)) ∧
    tableScales ⟨137, by decide⟩ = (lam137 : ℤ) ∧
    outputCoordinates ⟨137, by decide⟩ = ("M0_plus", row137.u, row137.v) := by decide +kernel

theorem old138 : tableDenominators ⟨138, by decide⟩ = dz138.map (fun z : ℤ => (z : ℚ) / (dq138 : ℚ)) ∧
    tableScales ⟨138, by decide⟩ = (lam138 : ℤ) ∧
    outputCoordinates ⟨138, by decide⟩ = ("M0_plus", row138.u, row138.v) := by decide +kernel

theorem old139 : tableDenominators ⟨139, by decide⟩ = dz139.map (fun z : ℤ => (z : ℚ) / (dq139 : ℚ)) ∧
    tableScales ⟨139, by decide⟩ = (lam139 : ℤ) ∧
    outputCoordinates ⟨139, by decide⟩ = ("M0_plus", row139.u, row139.v) := by decide +kernel

theorem old140 : tableDenominators ⟨140, by decide⟩ = dz140.map (fun z : ℤ => (z : ℚ) / (dq140 : ℚ)) ∧
    tableScales ⟨140, by decide⟩ = (lam140 : ℤ) ∧
    outputCoordinates ⟨140, by decide⟩ = ("M0_plus", row140.u, row140.v) := by decide +kernel

theorem old141 : tableDenominators ⟨141, by decide⟩ = dz141.map (fun z : ℤ => (z : ℚ) / (dq141 : ℚ)) ∧
    tableScales ⟨141, by decide⟩ = (lam141 : ℤ) ∧
    outputCoordinates ⟨141, by decide⟩ = ("M0_plus", row141.u, row141.v) := by decide +kernel

theorem old142 : tableDenominators ⟨142, by decide⟩ = dz142.map (fun z : ℤ => (z : ℚ) / (dq142 : ℚ)) ∧
    tableScales ⟨142, by decide⟩ = (lam142 : ℤ) ∧
    outputCoordinates ⟨142, by decide⟩ = ("M0_plus", row142.u, row142.v) := by decide +kernel

theorem old143 : tableDenominators ⟨143, by decide⟩ = dz143.map (fun z : ℤ => (z : ℚ) / (dq143 : ℚ)) ∧
    tableScales ⟨143, by decide⟩ = (lam143 : ℤ) ∧
    outputCoordinates ⟨143, by decide⟩ = ("M0_plus", row143.u, row143.v) := by decide +kernel

theorem old144 : tableDenominators ⟨144, by decide⟩ = dz144.map (fun z : ℤ => (z : ℚ) / (dq144 : ℚ)) ∧
    tableScales ⟨144, by decide⟩ = (lam144 : ℤ) ∧
    outputCoordinates ⟨144, by decide⟩ = ("M0_plus", row144.u, row144.v) := by decide +kernel

theorem old145 : tableDenominators ⟨145, by decide⟩ = dz145.map (fun z : ℤ => (z : ℚ) / (dq145 : ℚ)) ∧
    tableScales ⟨145, by decide⟩ = (lam145 : ℤ) ∧
    outputCoordinates ⟨145, by decide⟩ = ("M0_plus", row145.u, row145.v) := by decide +kernel

theorem old146 : tableDenominators ⟨146, by decide⟩ = dz146.map (fun z : ℤ => (z : ℚ) / (dq146 : ℚ)) ∧
    tableScales ⟨146, by decide⟩ = (lam146 : ℤ) ∧
    outputCoordinates ⟨146, by decide⟩ = ("M0_plus", row146.u, row146.v) := by decide +kernel

theorem old147 : tableDenominators ⟨147, by decide⟩ = dz147.map (fun z : ℤ => (z : ℚ) / (dq147 : ℚ)) ∧
    tableScales ⟨147, by decide⟩ = (lam147 : ℤ) ∧
    outputCoordinates ⟨147, by decide⟩ = ("M0_plus", row147.u, row147.v) := by decide +kernel

theorem old148 : tableDenominators ⟨148, by decide⟩ = dz148.map (fun z : ℤ => (z : ℚ) / (dq148 : ℚ)) ∧
    tableScales ⟨148, by decide⟩ = (lam148 : ℤ) ∧
    outputCoordinates ⟨148, by decide⟩ = ("M0_plus", row148.u, row148.v) := by decide +kernel

theorem old149 : tableDenominators ⟨149, by decide⟩ = dz149.map (fun z : ℤ => (z : ℚ) / (dq149 : ℚ)) ∧
    tableScales ⟨149, by decide⟩ = (lam149 : ℤ) ∧
    outputCoordinates ⟨149, by decide⟩ = ("M0_plus", row149.u, row149.v) := by decide +kernel

theorem old150 : tableDenominators ⟨150, by decide⟩ = dz150.map (fun z : ℤ => (z : ℚ) / (dq150 : ℚ)) ∧
    tableScales ⟨150, by decide⟩ = (lam150 : ℤ) ∧
    outputCoordinates ⟨150, by decide⟩ = ("M0_plus", row150.u, row150.v) := by decide +kernel

theorem old151 : tableDenominators ⟨151, by decide⟩ = dz151.map (fun z : ℤ => (z : ℚ) / (dq151 : ℚ)) ∧
    tableScales ⟨151, by decide⟩ = (lam151 : ℤ) ∧
    outputCoordinates ⟨151, by decide⟩ = ("M0_plus", row151.u, row151.v) := by decide +kernel

theorem old152 : tableDenominators ⟨152, by decide⟩ = dz152.map (fun z : ℤ => (z : ℚ) / (dq152 : ℚ)) ∧
    tableScales ⟨152, by decide⟩ = (lam152 : ℤ) ∧
    outputCoordinates ⟨152, by decide⟩ = ("M0_plus", row152.u, row152.v) := by decide +kernel

theorem old153 : tableDenominators ⟨153, by decide⟩ = dz153.map (fun z : ℤ => (z : ℚ) / (dq153 : ℚ)) ∧
    tableScales ⟨153, by decide⟩ = (lam153 : ℤ) ∧
    outputCoordinates ⟨153, by decide⟩ = ("M0_plus", row153.u, row153.v) := by decide +kernel

theorem old154 : tableDenominators ⟨154, by decide⟩ = dz154.map (fun z : ℤ => (z : ℚ) / (dq154 : ℚ)) ∧
    tableScales ⟨154, by decide⟩ = (lam154 : ℤ) ∧
    outputCoordinates ⟨154, by decide⟩ = ("M0_plus", row154.u, row154.v) := by decide +kernel

theorem old155 : tableDenominators ⟨155, by decide⟩ = dz155.map (fun z : ℤ => (z : ℚ) / (dq155 : ℚ)) ∧
    tableScales ⟨155, by decide⟩ = (lam155 : ℤ) ∧
    outputCoordinates ⟨155, by decide⟩ = ("M0_plus", row155.u, row155.v) := by decide +kernel

theorem old156 : tableDenominators ⟨156, by decide⟩ = dz156.map (fun z : ℤ => (z : ℚ) / (dq156 : ℚ)) ∧
    tableScales ⟨156, by decide⟩ = (lam156 : ℤ) ∧
    outputCoordinates ⟨156, by decide⟩ = ("M0_plus", row156.u, row156.v) := by decide +kernel

theorem old157 : tableDenominators ⟨157, by decide⟩ = dz157.map (fun z : ℤ => (z : ℚ) / (dq157 : ℚ)) ∧
    tableScales ⟨157, by decide⟩ = (lam157 : ℤ) ∧
    outputCoordinates ⟨157, by decide⟩ = ("M0_plus", row157.u, row157.v) := by decide +kernel

theorem old158 : tableDenominators ⟨158, by decide⟩ = dz158.map (fun z : ℤ => (z : ℚ) / (dq158 : ℚ)) ∧
    tableScales ⟨158, by decide⟩ = (lam158 : ℤ) ∧
    outputCoordinates ⟨158, by decide⟩ = ("M0_plus", row158.u, row158.v) := by decide +kernel

theorem old159 : tableDenominators ⟨159, by decide⟩ = dz159.map (fun z : ℤ => (z : ℚ) / (dq159 : ℚ)) ∧
    tableScales ⟨159, by decide⟩ = (lam159 : ℤ) ∧
    outputCoordinates ⟨159, by decide⟩ = ("M0_plus", row159.u, row159.v) := by decide +kernel

theorem old160 : tableDenominators ⟨160, by decide⟩ = dz160.map (fun z : ℤ => (z : ℚ) / (dq160 : ℚ)) ∧
    tableScales ⟨160, by decide⟩ = (lam160 : ℤ) ∧
    outputCoordinates ⟨160, by decide⟩ = ("M0_plus", row160.u, row160.v) := by decide +kernel

theorem old161 : tableDenominators ⟨161, by decide⟩ = dz161.map (fun z : ℤ => (z : ℚ) / (dq161 : ℚ)) ∧
    tableScales ⟨161, by decide⟩ = (lam161 : ℤ) ∧
    outputCoordinates ⟨161, by decide⟩ = ("M0_plus", row161.u, row161.v) := by decide +kernel

theorem old162 : tableDenominators ⟨162, by decide⟩ = dz162.map (fun z : ℤ => (z : ℚ) / (dq162 : ℚ)) ∧
    tableScales ⟨162, by decide⟩ = (lam162 : ℤ) ∧
    outputCoordinates ⟨162, by decide⟩ = ("M0_plus", row162.u, row162.v) := by decide +kernel

theorem old163 : tableDenominators ⟨163, by decide⟩ = dz163.map (fun z : ℤ => (z : ℚ) / (dq163 : ℚ)) ∧
    tableScales ⟨163, by decide⟩ = (lam163 : ℤ) ∧
    outputCoordinates ⟨163, by decide⟩ = ("M0_plus", row163.u, row163.v) := by decide +kernel

theorem old164 : tableDenominators ⟨164, by decide⟩ = dz164.map (fun z : ℤ => (z : ℚ) / (dq164 : ℚ)) ∧
    tableScales ⟨164, by decide⟩ = (lam164 : ℤ) ∧
    outputCoordinates ⟨164, by decide⟩ = ("M0_plus", row164.u, row164.v) := by decide +kernel

theorem old165 : tableDenominators ⟨165, by decide⟩ = dz165.map (fun z : ℤ => (z : ℚ) / (dq165 : ℚ)) ∧
    tableScales ⟨165, by decide⟩ = (lam165 : ℤ) ∧
    outputCoordinates ⟨165, by decide⟩ = ("M0_plus", row165.u, row165.v) := by decide +kernel

theorem old166 : tableDenominators ⟨166, by decide⟩ = dz166.map (fun z : ℤ => (z : ℚ) / (dq166 : ℚ)) ∧
    tableScales ⟨166, by decide⟩ = (lam166 : ℤ) ∧
    outputCoordinates ⟨166, by decide⟩ = ("M0_plus", row166.u, row166.v) := by decide +kernel

theorem old167 : tableDenominators ⟨167, by decide⟩ = dz167.map (fun z : ℤ => (z : ℚ) / (dq167 : ℚ)) ∧
    tableScales ⟨167, by decide⟩ = (lam167 : ℤ) ∧
    outputCoordinates ⟨167, by decide⟩ = ("M0_plus", row167.u, row167.v) := by decide +kernel

theorem old168 : tableDenominators ⟨168, by decide⟩ = dz168.map (fun z : ℤ => (z : ℚ) / (dq168 : ℚ)) ∧
    tableScales ⟨168, by decide⟩ = (lam168 : ℤ) ∧
    outputCoordinates ⟨168, by decide⟩ = ("M0_plus", row168.u, row168.v) := by decide +kernel

theorem old169 : tableDenominators ⟨169, by decide⟩ = dz169.map (fun z : ℤ => (z : ℚ) / (dq169 : ℚ)) ∧
    tableScales ⟨169, by decide⟩ = (lam169 : ℤ) ∧
    outputCoordinates ⟨169, by decide⟩ = ("M0_plus", row169.u, row169.v) := by decide +kernel

theorem old170 : tableDenominators ⟨170, by decide⟩ = dz170.map (fun z : ℤ => (z : ℚ) / (dq170 : ℚ)) ∧
    tableScales ⟨170, by decide⟩ = (lam170 : ℤ) ∧
    outputCoordinates ⟨170, by decide⟩ = ("M0_plus", row170.u, row170.v) := by decide +kernel

theorem old171 : tableDenominators ⟨171, by decide⟩ = dz171.map (fun z : ℤ => (z : ℚ) / (dq171 : ℚ)) ∧
    tableScales ⟨171, by decide⟩ = (lam171 : ℤ) ∧
    outputCoordinates ⟨171, by decide⟩ = ("M0_plus", row171.u, row171.v) := by decide +kernel

theorem old172 : tableDenominators ⟨172, by decide⟩ = dz172.map (fun z : ℤ => (z : ℚ) / (dq172 : ℚ)) ∧
    tableScales ⟨172, by decide⟩ = (lam172 : ℤ) ∧
    outputCoordinates ⟨172, by decide⟩ = ("M0_plus", row172.u, row172.v) := by decide +kernel

theorem old173 : tableDenominators ⟨173, by decide⟩ = dz173.map (fun z : ℤ => (z : ℚ) / (dq173 : ℚ)) ∧
    tableScales ⟨173, by decide⟩ = (lam173 : ℤ) ∧
    outputCoordinates ⟨173, by decide⟩ = ("M0_plus", row173.u, row173.v) := by decide +kernel

theorem old174 : tableDenominators ⟨174, by decide⟩ = dz174.map (fun z : ℤ => (z : ℚ) / (dq174 : ℚ)) ∧
    tableScales ⟨174, by decide⟩ = (lam174 : ℤ) ∧
    outputCoordinates ⟨174, by decide⟩ = ("M0_plus", row174.u, row174.v) := by decide +kernel

theorem old175 : tableDenominators ⟨175, by decide⟩ = dz175.map (fun z : ℤ => (z : ℚ) / (dq175 : ℚ)) ∧
    tableScales ⟨175, by decide⟩ = (lam175 : ℤ) ∧
    outputCoordinates ⟨175, by decide⟩ = ("M0_plus", row175.u, row175.v) := by decide +kernel

theorem old176 : tableDenominators ⟨176, by decide⟩ = dz176.map (fun z : ℤ => (z : ℚ) / (dq176 : ℚ)) ∧
    tableScales ⟨176, by decide⟩ = (lam176 : ℤ) ∧
    outputCoordinates ⟨176, by decide⟩ = ("M0_plus", row176.u, row176.v) := by decide +kernel

theorem old177 : tableDenominators ⟨177, by decide⟩ = dz177.map (fun z : ℤ => (z : ℚ) / (dq177 : ℚ)) ∧
    tableScales ⟨177, by decide⟩ = (lam177 : ℤ) ∧
    outputCoordinates ⟨177, by decide⟩ = ("M0_plus", row177.u, row177.v) := by decide +kernel

theorem old178 : tableDenominators ⟨178, by decide⟩ = dz178.map (fun z : ℤ => (z : ℚ) / (dq178 : ℚ)) ∧
    tableScales ⟨178, by decide⟩ = (lam178 : ℤ) ∧
    outputCoordinates ⟨178, by decide⟩ = ("M0_plus", row178.u, row178.v) := by decide +kernel

theorem old179 : tableDenominators ⟨179, by decide⟩ = dz179.map (fun z : ℤ => (z : ℚ) / (dq179 : ℚ)) ∧
    tableScales ⟨179, by decide⟩ = (lam179 : ℤ) ∧
    outputCoordinates ⟨179, by decide⟩ = ("M0_plus", row179.u, row179.v) := by decide +kernel

theorem old180 : tableDenominators ⟨180, by decide⟩ = dz180.map (fun z : ℤ => (z : ℚ) / (dq180 : ℚ)) ∧
    tableScales ⟨180, by decide⟩ = (lam180 : ℤ) ∧
    outputCoordinates ⟨180, by decide⟩ = ("M0_plus", row180.u, row180.v) := by decide +kernel

theorem old181 : tableDenominators ⟨181, by decide⟩ = dz181.map (fun z : ℤ => (z : ℚ) / (dq181 : ℚ)) ∧
    tableScales ⟨181, by decide⟩ = (lam181 : ℤ) ∧
    outputCoordinates ⟨181, by decide⟩ = ("M0_plus", row181.u, row181.v) := by decide +kernel

theorem old182 : tableDenominators ⟨182, by decide⟩ = dz182.map (fun z : ℤ => (z : ℚ) / (dq182 : ℚ)) ∧
    tableScales ⟨182, by decide⟩ = (lam182 : ℤ) ∧
    outputCoordinates ⟨182, by decide⟩ = ("M0_plus", row182.u, row182.v) := by decide +kernel

theorem old183 : tableDenominators ⟨183, by decide⟩ = dz183.map (fun z : ℤ => (z : ℚ) / (dq183 : ℚ)) ∧
    tableScales ⟨183, by decide⟩ = (lam183 : ℤ) ∧
    outputCoordinates ⟨183, by decide⟩ = ("M0_plus", row183.u, row183.v) := by decide +kernel

theorem old184 : tableDenominators ⟨184, by decide⟩ = dz184.map (fun z : ℤ => (z : ℚ) / (dq184 : ℚ)) ∧
    tableScales ⟨184, by decide⟩ = (lam184 : ℤ) ∧
    outputCoordinates ⟨184, by decide⟩ = ("M0_plus", row184.u, row184.v) := by decide +kernel

theorem old185 : tableDenominators ⟨185, by decide⟩ = dz185.map (fun z : ℤ => (z : ℚ) / (dq185 : ℚ)) ∧
    tableScales ⟨185, by decide⟩ = (lam185 : ℤ) ∧
    outputCoordinates ⟨185, by decide⟩ = ("M0_plus", row185.u, row185.v) := by decide +kernel

theorem old186 : tableDenominators ⟨186, by decide⟩ = dz186.map (fun z : ℤ => (z : ℚ) / (dq186 : ℚ)) ∧
    tableScales ⟨186, by decide⟩ = (lam186 : ℤ) ∧
    outputCoordinates ⟨186, by decide⟩ = ("M0_plus", row186.u, row186.v) := by decide +kernel

theorem old187 : tableDenominators ⟨187, by decide⟩ = dz187.map (fun z : ℤ => (z : ℚ) / (dq187 : ℚ)) ∧
    tableScales ⟨187, by decide⟩ = (lam187 : ℤ) ∧
    outputCoordinates ⟨187, by decide⟩ = ("M0_plus", row187.u, row187.v) := by decide +kernel

theorem old188 : tableDenominators ⟨188, by decide⟩ = dz188.map (fun z : ℤ => (z : ℚ) / (dq188 : ℚ)) ∧
    tableScales ⟨188, by decide⟩ = (lam188 : ℤ) ∧
    outputCoordinates ⟨188, by decide⟩ = ("M0_plus", row188.u, row188.v) := by decide +kernel

theorem old189 : tableDenominators ⟨189, by decide⟩ = dz189.map (fun z : ℤ => (z : ℚ) / (dq189 : ℚ)) ∧
    tableScales ⟨189, by decide⟩ = (lam189 : ℤ) ∧
    outputCoordinates ⟨189, by decide⟩ = ("M0_plus", row189.u, row189.v) := by decide +kernel

theorem old190 : tableDenominators ⟨190, by decide⟩ = dz190.map (fun z : ℤ => (z : ℚ) / (dq190 : ℚ)) ∧
    tableScales ⟨190, by decide⟩ = (lam190 : ℤ) ∧
    outputCoordinates ⟨190, by decide⟩ = ("M0_plus", row190.u, row190.v) := by decide +kernel

theorem old191 : tableDenominators ⟨191, by decide⟩ = dz191.map (fun z : ℤ => (z : ℚ) / (dq191 : ℚ)) ∧
    tableScales ⟨191, by decide⟩ = (lam191 : ℤ) ∧
    outputCoordinates ⟨191, by decide⟩ = ("M0_plus", row191.u, row191.v) := by decide +kernel

theorem old192 : tableDenominators ⟨192, by decide⟩ = dz192.map (fun z : ℤ => (z : ℚ) / (dq192 : ℚ)) ∧
    tableScales ⟨192, by decide⟩ = (lam192 : ℤ) ∧
    outputCoordinates ⟨192, by decide⟩ = ("M0_plus", row192.u, row192.v) := by decide +kernel

theorem old193 : tableDenominators ⟨193, by decide⟩ = dz193.map (fun z : ℤ => (z : ℚ) / (dq193 : ℚ)) ∧
    tableScales ⟨193, by decide⟩ = (lam193 : ℤ) ∧
    outputCoordinates ⟨193, by decide⟩ = ("M0_plus", row193.u, row193.v) := by decide +kernel

theorem old194 : tableDenominators ⟨194, by decide⟩ = dz194.map (fun z : ℤ => (z : ℚ) / (dq194 : ℚ)) ∧
    tableScales ⟨194, by decide⟩ = (lam194 : ℤ) ∧
    outputCoordinates ⟨194, by decide⟩ = ("M0_plus", row194.u, row194.v) := by decide +kernel

theorem old195 : tableDenominators ⟨195, by decide⟩ = dz195.map (fun z : ℤ => (z : ℚ) / (dq195 : ℚ)) ∧
    tableScales ⟨195, by decide⟩ = (lam195 : ℤ) ∧
    outputCoordinates ⟨195, by decide⟩ = ("M0_plus", row195.u, row195.v) := by decide +kernel

theorem old196 : tableDenominators ⟨196, by decide⟩ = dz196.map (fun z : ℤ => (z : ℚ) / (dq196 : ℚ)) ∧
    tableScales ⟨196, by decide⟩ = (lam196 : ℤ) ∧
    outputCoordinates ⟨196, by decide⟩ = ("M0_plus", row196.u, row196.v) := by decide +kernel

theorem old197 : tableDenominators ⟨197, by decide⟩ = dz197.map (fun z : ℤ => (z : ℚ) / (dq197 : ℚ)) ∧
    tableScales ⟨197, by decide⟩ = (lam197 : ℤ) ∧
    outputCoordinates ⟨197, by decide⟩ = ("M0_plus", row197.u, row197.v) := by decide +kernel

theorem old198 : tableDenominators ⟨198, by decide⟩ = dz198.map (fun z : ℤ => (z : ℚ) / (dq198 : ℚ)) ∧
    tableScales ⟨198, by decide⟩ = (lam198 : ℤ) ∧
    outputCoordinates ⟨198, by decide⟩ = ("M0_plus", row198.u, row198.v) := by decide +kernel

theorem old199 : tableDenominators ⟨199, by decide⟩ = dz199.map (fun z : ℤ => (z : ℚ) / (dq199 : ℚ)) ∧
    tableScales ⟨199, by decide⟩ = (lam199 : ℤ) ∧
    outputCoordinates ⟨199, by decide⟩ = ("M0_plus", row199.u, row199.v) := by decide +kernel

theorem old200 : tableDenominators ⟨200, by decide⟩ = dz200.map (fun z : ℤ => (z : ℚ) / (dq200 : ℚ)) ∧
    tableScales ⟨200, by decide⟩ = (lam200 : ℤ) ∧
    outputCoordinates ⟨200, by decide⟩ = ("M0_plus", row200.u, row200.v) := by decide +kernel

theorem old201 : tableDenominators ⟨201, by decide⟩ = dz201.map (fun z : ℤ => (z : ℚ) / (dq201 : ℚ)) ∧
    tableScales ⟨201, by decide⟩ = (lam201 : ℤ) ∧
    outputCoordinates ⟨201, by decide⟩ = ("M0_plus", row201.u, row201.v) := by decide +kernel

theorem old202 : tableDenominators ⟨202, by decide⟩ = dz202.map (fun z : ℤ => (z : ℚ) / (dq202 : ℚ)) ∧
    tableScales ⟨202, by decide⟩ = (lam202 : ℤ) ∧
    outputCoordinates ⟨202, by decide⟩ = ("M0_plus", row202.u, row202.v) := by decide +kernel

theorem old203 : tableDenominators ⟨203, by decide⟩ = dz203.map (fun z : ℤ => (z : ℚ) / (dq203 : ℚ)) ∧
    tableScales ⟨203, by decide⟩ = (lam203 : ℤ) ∧
    outputCoordinates ⟨203, by decide⟩ = ("M0_plus", row203.u, row203.v) := by decide +kernel

theorem old204 : tableDenominators ⟨204, by decide⟩ = dz204.map (fun z : ℤ => (z : ℚ) / (dq204 : ℚ)) ∧
    tableScales ⟨204, by decide⟩ = (lam204 : ℤ) ∧
    outputCoordinates ⟨204, by decide⟩ = ("M0_plus", row204.u, row204.v) := by decide +kernel

theorem old205 : tableDenominators ⟨205, by decide⟩ = dz205.map (fun z : ℤ => (z : ℚ) / (dq205 : ℚ)) ∧
    tableScales ⟨205, by decide⟩ = (lam205 : ℤ) ∧
    outputCoordinates ⟨205, by decide⟩ = ("M0_plus", row205.u, row205.v) := by decide +kernel

theorem old206 : tableDenominators ⟨206, by decide⟩ = dz206.map (fun z : ℤ => (z : ℚ) / (dq206 : ℚ)) ∧
    tableScales ⟨206, by decide⟩ = (lam206 : ℤ) ∧
    outputCoordinates ⟨206, by decide⟩ = ("M0_plus", row206.u, row206.v) := by decide +kernel

theorem old207 : tableDenominators ⟨207, by decide⟩ = dz207.map (fun z : ℤ => (z : ℚ) / (dq207 : ℚ)) ∧
    tableScales ⟨207, by decide⟩ = (lam207 : ℤ) ∧
    outputCoordinates ⟨207, by decide⟩ = ("M0_plus", row207.u, row207.v) := by decide +kernel

theorem old208 : tableDenominators ⟨208, by decide⟩ = dz208.map (fun z : ℤ => (z : ℚ) / (dq208 : ℚ)) ∧
    tableScales ⟨208, by decide⟩ = (lam208 : ℤ) ∧
    outputCoordinates ⟨208, by decide⟩ = ("M0_plus", row208.u, row208.v) := by decide +kernel

theorem old209 : tableDenominators ⟨209, by decide⟩ = dz209.map (fun z : ℤ => (z : ℚ) / (dq209 : ℚ)) ∧
    tableScales ⟨209, by decide⟩ = (lam209 : ℤ) ∧
    outputCoordinates ⟨209, by decide⟩ = ("M0_plus", row209.u, row209.v) := by decide +kernel

theorem old210 : tableDenominators ⟨210, by decide⟩ = dz210.map (fun z : ℤ => (z : ℚ) / (dq210 : ℚ)) ∧
    tableScales ⟨210, by decide⟩ = (lam210 : ℤ) ∧
    outputCoordinates ⟨210, by decide⟩ = ("M0_plus", row210.u, row210.v) := by decide +kernel

theorem old211 : tableDenominators ⟨211, by decide⟩ = dz211.map (fun z : ℤ => (z : ℚ) / (dq211 : ℚ)) ∧
    tableScales ⟨211, by decide⟩ = (lam211 : ℤ) ∧
    outputCoordinates ⟨211, by decide⟩ = ("M0_plus", row211.u, row211.v) := by decide +kernel

theorem old212 : tableDenominators ⟨212, by decide⟩ = dz212.map (fun z : ℤ => (z : ℚ) / (dq212 : ℚ)) ∧
    tableScales ⟨212, by decide⟩ = (lam212 : ℤ) ∧
    outputCoordinates ⟨212, by decide⟩ = ("M0_plus", row212.u, row212.v) := by decide +kernel

theorem old213 : tableDenominators ⟨213, by decide⟩ = dz213.map (fun z : ℤ => (z : ℚ) / (dq213 : ℚ)) ∧
    tableScales ⟨213, by decide⟩ = (lam213 : ℤ) ∧
    outputCoordinates ⟨213, by decide⟩ = ("M0_plus", row213.u, row213.v) := by decide +kernel

theorem old214 : tableDenominators ⟨214, by decide⟩ = dz214.map (fun z : ℤ => (z : ℚ) / (dq214 : ℚ)) ∧
    tableScales ⟨214, by decide⟩ = (lam214 : ℤ) ∧
    outputCoordinates ⟨214, by decide⟩ = ("M0_plus", row214.u, row214.v) := by decide +kernel

theorem old215 : tableDenominators ⟨215, by decide⟩ = dz215.map (fun z : ℤ => (z : ℚ) / (dq215 : ℚ)) ∧
    tableScales ⟨215, by decide⟩ = (lam215 : ℤ) ∧
    outputCoordinates ⟨215, by decide⟩ = ("M0_plus", row215.u, row215.v) := by decide +kernel

theorem old216 : tableDenominators ⟨216, by decide⟩ = dz216.map (fun z : ℤ => (z : ℚ) / (dq216 : ℚ)) ∧
    tableScales ⟨216, by decide⟩ = (lam216 : ℤ) ∧
    outputCoordinates ⟨216, by decide⟩ = ("M0_plus", row216.u, row216.v) := by decide +kernel

theorem old217 : tableDenominators ⟨217, by decide⟩ = dz217.map (fun z : ℤ => (z : ℚ) / (dq217 : ℚ)) ∧
    tableScales ⟨217, by decide⟩ = (lam217 : ℤ) ∧
    outputCoordinates ⟨217, by decide⟩ = ("M0_plus", row217.u, row217.v) := by decide +kernel

theorem old218 : tableDenominators ⟨218, by decide⟩ = dz218.map (fun z : ℤ => (z : ℚ) / (dq218 : ℚ)) ∧
    tableScales ⟨218, by decide⟩ = (lam218 : ℤ) ∧
    outputCoordinates ⟨218, by decide⟩ = ("M0_plus", row218.u, row218.v) := by decide +kernel

theorem old219 : tableDenominators ⟨219, by decide⟩ = dz219.map (fun z : ℤ => (z : ℚ) / (dq219 : ℚ)) ∧
    tableScales ⟨219, by decide⟩ = (lam219 : ℤ) ∧
    outputCoordinates ⟨219, by decide⟩ = ("M0_plus", row219.u, row219.v) := by decide +kernel

theorem old220 : tableDenominators ⟨220, by decide⟩ = dz220.map (fun z : ℤ => (z : ℚ) / (dq220 : ℚ)) ∧
    tableScales ⟨220, by decide⟩ = (lam220 : ℤ) ∧
    outputCoordinates ⟨220, by decide⟩ = ("M0_plus", row220.u, row220.v) := by decide +kernel

theorem old221 : tableDenominators ⟨221, by decide⟩ = dz221.map (fun z : ℤ => (z : ℚ) / (dq221 : ℚ)) ∧
    tableScales ⟨221, by decide⟩ = (lam221 : ℤ) ∧
    outputCoordinates ⟨221, by decide⟩ = ("M0_plus", row221.u, row221.v) := by decide +kernel

theorem old222 : tableDenominators ⟨222, by decide⟩ = dz222.map (fun z : ℤ => (z : ℚ) / (dq222 : ℚ)) ∧
    tableScales ⟨222, by decide⟩ = (lam222 : ℤ) ∧
    outputCoordinates ⟨222, by decide⟩ = ("M0_plus", row222.u, row222.v) := by decide +kernel

theorem old223 : tableDenominators ⟨223, by decide⟩ = dz223.map (fun z : ℤ => (z : ℚ) / (dq223 : ℚ)) ∧
    tableScales ⟨223, by decide⟩ = (lam223 : ℤ) ∧
    outputCoordinates ⟨223, by decide⟩ = ("M0_plus", row223.u, row223.v) := by decide +kernel

theorem old224 : tableDenominators ⟨224, by decide⟩ = dz224.map (fun z : ℤ => (z : ℚ) / (dq224 : ℚ)) ∧
    tableScales ⟨224, by decide⟩ = (lam224 : ℤ) ∧
    outputCoordinates ⟨224, by decide⟩ = ("M0_plus", row224.u, row224.v) := by decide +kernel

theorem old225 : tableDenominators ⟨225, by decide⟩ = dz225.map (fun z : ℤ => (z : ℚ) / (dq225 : ℚ)) ∧
    tableScales ⟨225, by decide⟩ = (lam225 : ℤ) ∧
    outputCoordinates ⟨225, by decide⟩ = ("M0_plus", row225.u, row225.v) := by decide +kernel

theorem old226 : tableDenominators ⟨226, by decide⟩ = dz226.map (fun z : ℤ => (z : ℚ) / (dq226 : ℚ)) ∧
    tableScales ⟨226, by decide⟩ = (lam226 : ℤ) ∧
    outputCoordinates ⟨226, by decide⟩ = ("M0_plus", row226.u, row226.v) := by decide +kernel

theorem old227 : tableDenominators ⟨227, by decide⟩ = dz227.map (fun z : ℤ => (z : ℚ) / (dq227 : ℚ)) ∧
    tableScales ⟨227, by decide⟩ = (lam227 : ℤ) ∧
    outputCoordinates ⟨227, by decide⟩ = ("M0_plus", row227.u, row227.v) := by decide +kernel

theorem old228 : tableDenominators ⟨228, by decide⟩ = dz228.map (fun z : ℤ => (z : ℚ) / (dq228 : ℚ)) ∧
    tableScales ⟨228, by decide⟩ = (lam228 : ℤ) ∧
    outputCoordinates ⟨228, by decide⟩ = ("M0_plus", row228.u, row228.v) := by decide +kernel

theorem old229 : tableDenominators ⟨229, by decide⟩ = dz229.map (fun z : ℤ => (z : ℚ) / (dq229 : ℚ)) ∧
    tableScales ⟨229, by decide⟩ = (lam229 : ℤ) ∧
    outputCoordinates ⟨229, by decide⟩ = ("M0_plus", row229.u, row229.v) := by decide +kernel

theorem old230 : tableDenominators ⟨230, by decide⟩ = dz230.map (fun z : ℤ => (z : ℚ) / (dq230 : ℚ)) ∧
    tableScales ⟨230, by decide⟩ = (lam230 : ℤ) ∧
    outputCoordinates ⟨230, by decide⟩ = ("M0_plus", row230.u, row230.v) := by decide +kernel

theorem old231 : tableDenominators ⟨231, by decide⟩ = dz231.map (fun z : ℤ => (z : ℚ) / (dq231 : ℚ)) ∧
    tableScales ⟨231, by decide⟩ = (lam231 : ℤ) ∧
    outputCoordinates ⟨231, by decide⟩ = ("M0_plus", row231.u, row231.v) := by decide +kernel

theorem old232 : tableDenominators ⟨232, by decide⟩ = dz232.map (fun z : ℤ => (z : ℚ) / (dq232 : ℚ)) ∧
    tableScales ⟨232, by decide⟩ = (lam232 : ℤ) ∧
    outputCoordinates ⟨232, by decide⟩ = ("M0_plus", row232.u, row232.v) := by decide +kernel

theorem old233 : tableDenominators ⟨233, by decide⟩ = dz233.map (fun z : ℤ => (z : ℚ) / (dq233 : ℚ)) ∧
    tableScales ⟨233, by decide⟩ = (lam233 : ℤ) ∧
    outputCoordinates ⟨233, by decide⟩ = ("M0_plus", row233.u, row233.v) := by decide +kernel

theorem old234 : tableDenominators ⟨234, by decide⟩ = dz234.map (fun z : ℤ => (z : ℚ) / (dq234 : ℚ)) ∧
    tableScales ⟨234, by decide⟩ = (lam234 : ℤ) ∧
    outputCoordinates ⟨234, by decide⟩ = ("M0_plus", row234.u, row234.v) := by decide +kernel

theorem old235 : tableDenominators ⟨235, by decide⟩ = dz235.map (fun z : ℤ => (z : ℚ) / (dq235 : ℚ)) ∧
    tableScales ⟨235, by decide⟩ = (lam235 : ℤ) ∧
    outputCoordinates ⟨235, by decide⟩ = ("M0_plus", row235.u, row235.v) := by decide +kernel

theorem old236 : tableDenominators ⟨236, by decide⟩ = dz236.map (fun z : ℤ => (z : ℚ) / (dq236 : ℚ)) ∧
    tableScales ⟨236, by decide⟩ = (lam236 : ℤ) ∧
    outputCoordinates ⟨236, by decide⟩ = ("M0_plus", row236.u, row236.v) := by decide +kernel

theorem old237 : tableDenominators ⟨237, by decide⟩ = dz237.map (fun z : ℤ => (z : ℚ) / (dq237 : ℚ)) ∧
    tableScales ⟨237, by decide⟩ = (lam237 : ℤ) ∧
    outputCoordinates ⟨237, by decide⟩ = ("M0_plus", row237.u, row237.v) := by decide +kernel

theorem old238 : tableDenominators ⟨238, by decide⟩ = dz238.map (fun z : ℤ => (z : ℚ) / (dq238 : ℚ)) ∧
    tableScales ⟨238, by decide⟩ = (lam238 : ℤ) ∧
    outputCoordinates ⟨238, by decide⟩ = ("M0_plus", row238.u, row238.v) := by decide +kernel

theorem old239 : tableDenominators ⟨239, by decide⟩ = dz239.map (fun z : ℤ => (z : ℚ) / (dq239 : ℚ)) ∧
    tableScales ⟨239, by decide⟩ = (lam239 : ℤ) ∧
    outputCoordinates ⟨239, by decide⟩ = ("M0_plus", row239.u, row239.v) := by decide +kernel

theorem old240 : tableDenominators ⟨240, by decide⟩ = dz240.map (fun z : ℤ => (z : ℚ) / (dq240 : ℚ)) ∧
    tableScales ⟨240, by decide⟩ = (lam240 : ℤ) ∧
    outputCoordinates ⟨240, by decide⟩ = ("M0_plus", row240.u, row240.v) := by decide +kernel

theorem old241 : tableDenominators ⟨241, by decide⟩ = dz241.map (fun z : ℤ => (z : ℚ) / (dq241 : ℚ)) ∧
    tableScales ⟨241, by decide⟩ = (lam241 : ℤ) ∧
    outputCoordinates ⟨241, by decide⟩ = ("M0_plus", row241.u, row241.v) := by decide +kernel

theorem old242 : tableDenominators ⟨242, by decide⟩ = dz242.map (fun z : ℤ => (z : ℚ) / (dq242 : ℚ)) ∧
    tableScales ⟨242, by decide⟩ = (lam242 : ℤ) ∧
    outputCoordinates ⟨242, by decide⟩ = ("M0_plus", row242.u, row242.v) := by decide +kernel

theorem old243 : tableDenominators ⟨243, by decide⟩ = dz243.map (fun z : ℤ => (z : ℚ) / (dq243 : ℚ)) ∧
    tableScales ⟨243, by decide⟩ = (lam243 : ℤ) ∧
    outputCoordinates ⟨243, by decide⟩ = ("M0_plus", row243.u, row243.v) := by decide +kernel

theorem old244 : tableDenominators ⟨244, by decide⟩ = dz244.map (fun z : ℤ => (z : ℚ) / (dq244 : ℚ)) ∧
    tableScales ⟨244, by decide⟩ = (lam244 : ℤ) ∧
    outputCoordinates ⟨244, by decide⟩ = ("M0_plus", row244.u, row244.v) := by decide +kernel

theorem old245 : tableDenominators ⟨245, by decide⟩ = dz245.map (fun z : ℤ => (z : ℚ) / (dq245 : ℚ)) ∧
    tableScales ⟨245, by decide⟩ = (lam245 : ℤ) ∧
    outputCoordinates ⟨245, by decide⟩ = ("M0_plus", row245.u, row245.v) := by decide +kernel

theorem old246 : tableDenominators ⟨246, by decide⟩ = dz246.map (fun z : ℤ => (z : ℚ) / (dq246 : ℚ)) ∧
    tableScales ⟨246, by decide⟩ = (lam246 : ℤ) ∧
    outputCoordinates ⟨246, by decide⟩ = ("M0_plus", row246.u, row246.v) := by decide +kernel

theorem old247 : tableDenominators ⟨247, by decide⟩ = dz247.map (fun z : ℤ => (z : ℚ) / (dq247 : ℚ)) ∧
    tableScales ⟨247, by decide⟩ = (lam247 : ℤ) ∧
    outputCoordinates ⟨247, by decide⟩ = ("M0_plus", row247.u, row247.v) := by decide +kernel

theorem old248 : tableDenominators ⟨248, by decide⟩ = dz248.map (fun z : ℤ => (z : ℚ) / (dq248 : ℚ)) ∧
    tableScales ⟨248, by decide⟩ = (lam248 : ℤ) ∧
    outputCoordinates ⟨248, by decide⟩ = ("M0_plus", row248.u, row248.v) := by decide +kernel

theorem old249 : tableDenominators ⟨249, by decide⟩ = dz249.map (fun z : ℤ => (z : ℚ) / (dq249 : ℚ)) ∧
    tableScales ⟨249, by decide⟩ = (lam249 : ℤ) ∧
    outputCoordinates ⟨249, by decide⟩ = ("M0_plus", row249.u, row249.v) := by decide +kernel

theorem old250 : tableDenominators ⟨250, by decide⟩ = dz250.map (fun z : ℤ => (z : ℚ) / (dq250 : ℚ)) ∧
    tableScales ⟨250, by decide⟩ = (lam250 : ℤ) ∧
    outputCoordinates ⟨250, by decide⟩ = ("M0_plus", row250.u, row250.v) := by decide +kernel

theorem old251 : tableDenominators ⟨251, by decide⟩ = dz251.map (fun z : ℤ => (z : ℚ) / (dq251 : ℚ)) ∧
    tableScales ⟨251, by decide⟩ = (lam251 : ℤ) ∧
    outputCoordinates ⟨251, by decide⟩ = ("M0_plus", row251.u, row251.v) := by decide +kernel

theorem old252 : tableDenominators ⟨252, by decide⟩ = dz252.map (fun z : ℤ => (z : ℚ) / (dq252 : ℚ)) ∧
    tableScales ⟨252, by decide⟩ = (lam252 : ℤ) ∧
    outputCoordinates ⟨252, by decide⟩ = ("M0_plus", row252.u, row252.v) := by decide +kernel

theorem old253 : tableDenominators ⟨253, by decide⟩ = dz253.map (fun z : ℤ => (z : ℚ) / (dq253 : ℚ)) ∧
    tableScales ⟨253, by decide⟩ = (lam253 : ℤ) ∧
    outputCoordinates ⟨253, by decide⟩ = ("M0_plus", row253.u, row253.v) := by decide +kernel

theorem old254 : tableDenominators ⟨254, by decide⟩ = dz254.map (fun z : ℤ => (z : ℚ) / (dq254 : ℚ)) ∧
    tableScales ⟨254, by decide⟩ = (lam254 : ℤ) ∧
    outputCoordinates ⟨254, by decide⟩ = ("M0_plus", row254.u, row254.v) := by decide +kernel

theorem old255 : tableDenominators ⟨255, by decide⟩ = dz255.map (fun z : ℤ => (z : ℚ) / (dq255 : ℚ)) ∧
    tableScales ⟨255, by decide⟩ = (lam255 : ℤ) ∧
    outputCoordinates ⟨255, by decide⟩ = ("M0_plus", row255.u, row255.v) := by decide +kernel

theorem old256 : tableDenominators ⟨256, by decide⟩ = dz256.map (fun z : ℤ => (z : ℚ) / (dq256 : ℚ)) ∧
    tableScales ⟨256, by decide⟩ = (lam256 : ℤ) ∧
    outputCoordinates ⟨256, by decide⟩ = ("M0_plus", row256.u, row256.v) := by decide +kernel

theorem old257 : tableDenominators ⟨257, by decide⟩ = dz257.map (fun z : ℤ => (z : ℚ) / (dq257 : ℚ)) ∧
    tableScales ⟨257, by decide⟩ = (lam257 : ℤ) ∧
    outputCoordinates ⟨257, by decide⟩ = ("M0_plus", row257.u, row257.v) := by decide +kernel

theorem old258 : tableDenominators ⟨258, by decide⟩ = dz258.map (fun z : ℤ => (z : ℚ) / (dq258 : ℚ)) ∧
    tableScales ⟨258, by decide⟩ = (lam258 : ℤ) ∧
    outputCoordinates ⟨258, by decide⟩ = ("M0_plus", row258.u, row258.v) := by decide +kernel

theorem old259 : tableDenominators ⟨259, by decide⟩ = dz259.map (fun z : ℤ => (z : ℚ) / (dq259 : ℚ)) ∧
    tableScales ⟨259, by decide⟩ = (lam259 : ℤ) ∧
    outputCoordinates ⟨259, by decide⟩ = ("M0_plus", row259.u, row259.v) := by decide +kernel

theorem old260 : tableDenominators ⟨260, by decide⟩ = dz260.map (fun z : ℤ => (z : ℚ) / (dq260 : ℚ)) ∧
    tableScales ⟨260, by decide⟩ = (lam260 : ℤ) ∧
    outputCoordinates ⟨260, by decide⟩ = ("M0_plus", row260.u, row260.v) := by decide +kernel

theorem old261 : tableDenominators ⟨261, by decide⟩ = dz261.map (fun z : ℤ => (z : ℚ) / (dq261 : ℚ)) ∧
    tableScales ⟨261, by decide⟩ = (lam261 : ℤ) ∧
    outputCoordinates ⟨261, by decide⟩ = ("M0_plus", row261.u, row261.v) := by decide +kernel

theorem old262 : tableDenominators ⟨262, by decide⟩ = dz262.map (fun z : ℤ => (z : ℚ) / (dq262 : ℚ)) ∧
    tableScales ⟨262, by decide⟩ = (lam262 : ℤ) ∧
    outputCoordinates ⟨262, by decide⟩ = ("M0_plus", row262.u, row262.v) := by decide +kernel

theorem old263 : tableDenominators ⟨263, by decide⟩ = dz263.map (fun z : ℤ => (z : ℚ) / (dq263 : ℚ)) ∧
    tableScales ⟨263, by decide⟩ = (lam263 : ℤ) ∧
    outputCoordinates ⟨263, by decide⟩ = ("M0_plus", row263.u, row263.v) := by decide +kernel

theorem old264 : tableDenominators ⟨264, by decide⟩ = dz264.map (fun z : ℤ => (z : ℚ) / (dq264 : ℚ)) ∧
    tableScales ⟨264, by decide⟩ = (lam264 : ℤ) ∧
    outputCoordinates ⟨264, by decide⟩ = ("M0_plus", row264.u, row264.v) := by decide +kernel

theorem old265 : tableDenominators ⟨265, by decide⟩ = dz265.map (fun z : ℤ => (z : ℚ) / (dq265 : ℚ)) ∧
    tableScales ⟨265, by decide⟩ = (lam265 : ℤ) ∧
    outputCoordinates ⟨265, by decide⟩ = ("M0_standard", row265.u, row265.v) := by decide +kernel

theorem old266 : tableDenominators ⟨266, by decide⟩ = dz266.map (fun z : ℤ => (z : ℚ) / (dq266 : ℚ)) ∧
    tableScales ⟨266, by decide⟩ = (lam266 : ℤ) ∧
    outputCoordinates ⟨266, by decide⟩ = ("M0_standard", row266.u, row266.v) := by decide +kernel

theorem old267 : tableDenominators ⟨267, by decide⟩ = dz267.map (fun z : ℤ => (z : ℚ) / (dq267 : ℚ)) ∧
    tableScales ⟨267, by decide⟩ = (lam267 : ℤ) ∧
    outputCoordinates ⟨267, by decide⟩ = ("M0_standard", row267.u, row267.v) := by decide +kernel

theorem old268 : tableDenominators ⟨268, by decide⟩ = dz268.map (fun z : ℤ => (z : ℚ) / (dq268 : ℚ)) ∧
    tableScales ⟨268, by decide⟩ = (lam268 : ℤ) ∧
    outputCoordinates ⟨268, by decide⟩ = ("M0_standard", row268.u, row268.v) := by decide +kernel

theorem old269 : tableDenominators ⟨269, by decide⟩ = dz269.map (fun z : ℤ => (z : ℚ) / (dq269 : ℚ)) ∧
    tableScales ⟨269, by decide⟩ = (lam269 : ℤ) ∧
    outputCoordinates ⟨269, by decide⟩ = ("M0_standard", row269.u, row269.v) := by decide +kernel

theorem old270 : tableDenominators ⟨270, by decide⟩ = dz270.map (fun z : ℤ => (z : ℚ) / (dq270 : ℚ)) ∧
    tableScales ⟨270, by decide⟩ = (lam270 : ℤ) ∧
    outputCoordinates ⟨270, by decide⟩ = ("M0_standard", row270.u, row270.v) := by decide +kernel

theorem old271 : tableDenominators ⟨271, by decide⟩ = dz271.map (fun z : ℤ => (z : ℚ) / (dq271 : ℚ)) ∧
    tableScales ⟨271, by decide⟩ = (lam271 : ℤ) ∧
    outputCoordinates ⟨271, by decide⟩ = ("M0_standard", row271.u, row271.v) := by decide +kernel

theorem namesF0 : ∀ k : Fin 272, (outputCoordinates k).1 = "F0" ↔ (0 ≤ k.val ∧ k.val < 0 + 11) := by
  decide +kernel

theorem namesF1 : ∀ k : Fin 272, (outputCoordinates k).1 = "F1" ↔ (11 ≤ k.val ∧ k.val < 11 + 4) := by
  decide +kernel

theorem namesM0plus : ∀ k : Fin 272, (outputCoordinates k).1 = "M0_plus" ↔ (15 ≤ k.val ∧ k.val < 15 + 250) := by
  decide +kernel

theorem namesM0standard : ∀ k : Fin 272, (outputCoordinates k).1 = "M0_standard" ↔ (265 ≤ k.val ∧ k.val < 265 + 7) := by
  decide +kernel

end ThomsonCompact.Floor.Tables.D18b
