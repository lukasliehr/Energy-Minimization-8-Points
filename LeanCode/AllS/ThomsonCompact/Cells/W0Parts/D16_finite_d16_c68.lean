import ThomsonCompact.CoeffMap.Deg.Bridges.D16.Part
import ThomsonCompact.CoeffMap.Deg.GramNSound
import ThomsonCompact.CoeffMap.Deg.GramRSound
import ThomsonCompact.CoeffMap.Deg.Bridges.ShiftP
import ThomsonCompact.CoeffMap.Deg.OneTime.D16.ShiftFacts
import ThomsonCompact.CoeffMap.Deg.Bridges.StageP
import ThomsonCompact.Cells.finite_d16_c68.W0Z
import ThomsonCompact.Packed.BridgeIn
import ThomsonCompact.Cells.finite_d16_c68.W0Ctx
import ThomsonCompact.Cells.finite_d16_c68.W0Sum
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L00_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L01_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L02_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L03_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L04_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L05_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L06_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L07_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P08_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P08_0_1_1_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L09_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P10_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P10_0_1_1_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P10_0_1_2_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_0_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_0_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_1_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_1_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_2_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_2_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_3_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_3_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_4_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_4_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_5_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P11_0_1_5_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P12_0_1_0_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P12_0_1_0_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P12_0_1_1_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P12_0_1_1_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P12_0_1_2_0_101
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.P12_0_1_2_101_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L13_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L14_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.L15_0_1_0_0_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z08_0_4_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z08_4_256_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z10_0_2_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z10_2_5_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z10_32_256_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z10_5_32_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_0_2_0_29
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_0_2_29_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_11_13_0_29
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_11_13_29_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_13_256_0_29
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_13_256_29_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_2_5_0_29
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_2_5_29_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_5_7_0_29
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_5_7_29_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_7_11_0_29
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z11_7_11_29_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z12_0_4_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z12_4_7_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.Z12_7_256_0_256
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_0_22
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_22_44
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_44_67
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_67_89
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_89_112
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_112_134
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_134_157
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_157_179
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LSum_179_202
import ThomsonCompact.Cells.finite_d16_c68.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.finite_d16_c68_RootAccepted

/-! W0 part of cell finite_d16_c68 (index 27, D16, N = 30; generated by `CoeffMap/Deg/gen/assemble.py`): the packed
height enclosure (old accepted model), the leaves (single-stage piece leaves, sum leaves, denominator leaf),
`w0Part_of16` and `bsum_valid16`. Consumed by `Cells/finite_d16_c68/Cell.lean` (F3g). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.CoeffMap.Deg.Link
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

namespace ThomsonCompact.Cells.C_finite_d16_c68.W0
open Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.finite_d16_c68_RootAccepted (exponent sound)

theorem good : Good 30 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

/-- The packed height TM encloses the old accepted height `aS ∘ exponent`. -/
theorem hA : Encl ctx A (fun x => aS (exponent x)) := by
  have h := ofBoxes_sound good heightFinal.asTM sound.1
    (by decide +kernel : (ofOldTM ctx heightFinal.asTM).ok = true)
  rw [ofOldTM, (by decide +kernel : boxList heightFinal.asTM = hBoxes),
    (by decide +kernel : heightFinal.asTM.error = hErr)] at h
  exact h

theorem hord : ∀ b, (ThomsonCompact.CoeffMap.Deg.blkOf16 ThomsonCompact.Cells.C_finite_d16_c68.W0.data b).order = gramBlockDimension 8 b :=
  hord_of16 data (by decide +kernel)

/-- The `P` lookups of the piece leaves: stage P (stored z, `zData`) for the heavy blocks [8, 10, 11, 12], single-stage
otherwise (re-centred records, `CoeffMap.Deg.Shift`). -/
noncomputable def PT (b _h : ℕ) : ℕ → ℕ → TM :=
  cond (Nat.beq b 8 || Nat.beq b 10 || Nat.beq b 11 || Nat.beq b 12) (D16.L.PSC D16.LS 17 6 ctx A (WTt fdata ctx b) zData b) (D16.L.pLookC D16.LS 17 6 ctx A (WTn fdata ctx b) b)

/-- The stage-Z facts of block 8 (the `zStageOkC` leaves). -/
theorem hz08 : ∀ v, v < D16.L.rdim 8 → pivotOf (D16.L.blockRowC D16.LS 17 6 ctx A 8 v) = none → ∀ i, i < D16.L.gdim 8 →
    D16.L.zOk1 ctx zData 8 i v (zTMD ctx (D16.L.blockRowC D16.LS 17 6 ctx A 8) (wRowsD (WTn fdata ctx 8) (D16.L.gdim 8)) i v) = true :=
  ZFactsC.full (ZFactsC.join_v (zStageOkC_spec D16.L D16.LS Leaves.zleaf_08_0_4_0_256) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_08_4_256_0_256)) (by decide) (by decide)

/-- The stage-Z facts of block 10 (the `zStageOkC` leaves). -/
theorem hz10 : ∀ v, v < D16.L.rdim 10 → pivotOf (D16.L.blockRowC D16.LS 17 6 ctx A 10 v) = none → ∀ i, i < D16.L.gdim 10 →
    D16.L.zOk1 ctx zData 10 i v (zTMD ctx (D16.L.blockRowC D16.LS 17 6 ctx A 10) (wRowsD (WTn fdata ctx 10) (D16.L.gdim 10)) i v) = true :=
  ZFactsC.full (ZFactsC.join_v (zStageOkC_spec D16.L D16.LS Leaves.zleaf_10_0_2_0_256) (ZFactsC.join_v (zStageOkC_spec D16.L D16.LS Leaves.zleaf_10_2_5_0_256) (ZFactsC.join_v (zStageOkC_spec D16.L D16.LS Leaves.zleaf_10_5_32_0_256) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_10_32_256_0_256)))) (by decide) (by decide)

/-- The stage-Z facts of block 11 (the `zStageOkC` leaves). -/
theorem hz11 : ∀ v, v < D16.L.rdim 11 → pivotOf (D16.L.blockRowC D16.LS 17 6 ctx A 11 v) = none → ∀ i, i < D16.L.gdim 11 →
    D16.L.zOk1 ctx zData 11 i v (zTMD ctx (D16.L.blockRowC D16.LS 17 6 ctx A 11) (wRowsD (WTr fdata ctx 11) (D16.L.gdim 11)) i v) = true :=
  ZFactsC.full (ZFactsC.join_v (ZFactsC.join_i (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_0_2_0_29) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_0_2_29_256)) (ZFactsC.join_v (ZFactsC.join_i (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_2_5_0_29) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_2_5_29_256)) (ZFactsC.join_v (ZFactsC.join_i (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_5_7_0_29) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_5_7_29_256)) (ZFactsC.join_v (ZFactsC.join_i (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_7_11_0_29) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_7_11_29_256)) (ZFactsC.join_v (ZFactsC.join_i (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_11_13_0_29) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_11_13_29_256)) (ZFactsC.join_i (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_13_256_0_29) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_11_13_256_29_256))))))) (by decide) (by decide)

/-- The stage-Z facts of block 12 (the `zStageOkC` leaves). -/
theorem hz12 : ∀ v, v < D16.L.rdim 12 → pivotOf (D16.L.blockRowC D16.LS 17 6 ctx A 12 v) = none → ∀ i, i < D16.L.gdim 12 →
    D16.L.zOk1 ctx zData 12 i v (zTMD ctx (D16.L.blockRowC D16.LS 17 6 ctx A 12) (wRowsD (WTn fdata ctx 12) (D16.L.gdim 12)) i v) = true :=
  ZFactsC.full (ZFactsC.join_v (zStageOkC_spec D16.L D16.LS Leaves.zleaf_12_0_4_0_256) (ZFactsC.join_v (zStageOkC_spec D16.L D16.LS Leaves.zleaf_12_4_7_0_256) (zStageOkC_spec D16.L D16.LS Leaves.zleaf_12_7_256_0_256))) (by decide) (by decide)

theorem hP : ∀ b h, b < D16.L.dH + 8 → h < sumData.np b → ∀ u v,
    EnclOk ctx (PT b h u v) (fun t => PfL D16.L (fun x => aS (exponent x)) data b u v t) := by
  intro b _ hb _ u v
  have hb' : b < 16 := hb
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 0 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 1 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 2 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 3 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 4 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 5 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 6 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 7 u v
  · exact hP_stageC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data (fun b => WTn fdata ctx b) (fun b => WTt fdata ctx b)
      (fun b i j => WTn_sound_flat good data nchK nchF b i j) (fun b i j => WTt_sound_flat good data nchK nchF b i j)
      zData 8 hz08 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 9 u v
  · exact hP_stageC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data (fun b => WTn fdata ctx b) (fun b => WTt fdata ctx b)
      (fun b i j => WTn_sound_flat good data nchK nchF b i j) (fun b i j => WTt_sound_flat good data nchK nchF b i j)
      zData 10 hz10 u v
  · exact hP_stageC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data (fun b => WTr fdata ctx b) (fun b => WTt fdata ctx b)
      (fun b i j => WTr_sound_flat good data nchK nchF b i j) (fun b i j => WTt_sound_flat good data nchK nchF b i j)
      zData 11 hz11 u v
  · exact hP_stageC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data (fun b => WTn fdata ctx b) (fun b => WTt fdata ctx b)
      (fun b i j => WTn_sound_flat good data nchK nchF b i j) (fun b i j => WTt_sound_flat good data nchK nchF b i j)
      zData 12 hz12 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 13 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 14 u v
  · exact hP_singleC D16.L D16.LS 17 6 8 Bridges.D16.pivots Bridges.D16.facts OneTime.D16.shiftFacts good hA data
      (fun b => WTn fdata ctx b) (fun b i j => WTn_sound_flat good data nchK nchF b i j)
      (fun b i j => WTn_symm fdata ctx b i j) 15 u v

/-- Every piece is `ok` and matches its checkpoint (the piece leaves). -/
theorem hpc (b g h r : ℕ) (hb : b < D16.L.dH + 8) (hg : g < D16.L.nGrp b) (hh : h < sumData.np b) (hr : r < D16.L.nc) :
    (TP D16.L sumData ctx PT b g h r).ok = true ∧
      ckOk ctx sumData.F 30 (TP D16.L sumData ctx PT b g h r) (ckRecD sumData 30 b g h r) = true := by
  have hb' : b < 16 := hb
  have hr' : r < 202 := hr
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_00_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_01_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_02_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_03_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_04_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_05_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_06_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_07_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 2 := hh
    rcases (show (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 1 ∧ 0 ≤ r ∧ r < 202) by omega) with ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩
    · exact leafOk_spec D16.L Leaves.pleaf_08_0_1_0_0_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_08_0_1_1_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_09_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 3 := hh
    rcases (show (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 1 ∧ 0 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 2 ∧ 0 ≤ r ∧ r < 202) by omega) with ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩
    · exact leafOk_spec D16.L Leaves.pleaf_10_0_1_0_0_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_10_0_1_1_0_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_10_0_1_2_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 6 := hh
    rcases (show (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 1 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 1 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 2 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 2 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 3 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 3 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 4 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 4 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 5 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 5 ∧ 101 ≤ r ∧ r < 202) by omega) with ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_0_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_0_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_1_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_1_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_2_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_2_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_3_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_3_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_4_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_4_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_5_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_11_0_1_5_101_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 3 := hh
    rcases (show (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 1 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 1 ∧ 101 ≤ r ∧ r < 202) ∨ (0 ≤ g ∧ g < 1 ∧ h = 2 ∧ 0 ≤ r ∧ r < 101) ∨ (0 ≤ g ∧ g < 1 ∧ h = 2 ∧ 101 ≤ r ∧ r < 202) by omega) with ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩ | ⟨h0, h1, rfl, h2, h3⟩
    · exact leafOk_spec D16.L Leaves.pleaf_12_0_1_0_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_12_0_1_0_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_12_0_1_1_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_12_0_1_1_101_202 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_12_0_1_2_0_101 g h0 h1 r h2 h3 hr
    · exact leafOk_spec D16.L Leaves.pleaf_12_0_1_2_101_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_13_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_14_0_1_0_0_202 g h0 h1 r h2 h3 hr
  · have hg' : g < 1 := hg
    have hh' : h < 1 := hh
    obtain ⟨h0, h1, rfl, h2, h3⟩ : (0 ≤ g ∧ g < 1 ∧ h = 0 ∧ 0 ≤ r ∧ r < 202) := by omega
    exact leafOk_spec D16.L Leaves.leaf_15_0_1_0_0_202 g h0 h1 r h2 h3 hr

/-- The final sum records (the sum leaves). -/
theorem sum_ok (r : ℕ) (hr : r < 202) : D16.L.sumOkRD sumData 30 r = true := by
  rcases (show (0 ≤ r ∧ r < 22) ∨ (22 ≤ r ∧ r < 44) ∨ (44 ≤ r ∧ r < 67) ∨ (67 ≤ r ∧ r < 89) ∨ (89 ≤ r ∧ r < 112) ∨ (112 ≤ r ∧ r < 134) ∨ (134 ≤ r ∧ r < 157) ∨ (157 ≤ r ∧ r < 179) ∨ (179 ≤ r ∧ r < 202) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_0_22 r h0.1 h0.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_22_44 r h1.1 h1.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_44_67 r h2.1 h2.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_67_89 r h3.1 h3.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_89_112 r h4.1 h4.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_112_134 r h5.1 h5.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_134_157 r h6.1 h6.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_157_179 r h7.1 h7.2
  · exact D16.L.sumOkD_spec sumData Leaves.lsum_179_202 r h8.1 h8.2

/-- The W0 pieces of cell finite_d16_c68 (`B` at the internal order 30; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part16 exponent data.cell (blkOf16 data) hord 30 (16 * 32 * 32) :=
  w0Part_of16 good data exponent hA hord sumData Leaves.leaf_den (by decide) PT hP 30 hpc

/-- **The W0 sum per retained coordinate (order 30) encloses `Σ_ι g ι r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 202) :
    (BsumD 30 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid16 good data exponent hA hord sumData Leaves.leaf_den (by decide) PT hP 30 (by decide) hpc sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_finite_d16_c68.W0
