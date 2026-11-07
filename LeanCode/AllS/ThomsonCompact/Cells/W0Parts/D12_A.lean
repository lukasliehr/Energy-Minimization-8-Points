import ThomsonCompact.CoeffMap.W0Part
import ThomsonCompact.CoeffMap.BSumSound
import ThomsonCompact.CoeffMap.EGCheck.Empty
import ThomsonCompact.Packed.BridgeIn
import ThomsonCompact.Cells.base_A_01.W0Ctx
import ThomsonCompact.Cells.base_A_01.W0Sum
import ThomsonCompact.Cells.base_A_01.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L08_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L08_1_2_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L08_2_3_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_1_2_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_2_3_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_3_4_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_4_5_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_5_6_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_6_7_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L09_7_8_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_A_01.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_A_01.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_A_01.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_A_01.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_A_01_RootAccepted
import ThomsonCompact.Cells.base_A_05.W0Ctx
import ThomsonCompact.Cells.base_A_05.W0Sum
import ThomsonCompact.Cells.base_A_05.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L08_0_1_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L08_0_1_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L08_1_2_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L08_1_2_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L08_2_3_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L08_2_3_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_0_1_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_0_1_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_1_2_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_1_2_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_2_3_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_2_3_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_3_4_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_3_4_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_4_5_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_4_5_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_5_6_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_5_6_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_6_7_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_6_7_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_7_8_0_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.L09_7_8_50_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.LSum_0_16
import ThomsonCompact.Cells.base_A_05.W0Leaves.LSum_16_33
import ThomsonCompact.Cells.base_A_05.W0Leaves.LSum_33_50
import ThomsonCompact.Cells.base_A_05.W0Leaves.LSum_50_66
import ThomsonCompact.Cells.base_A_05.W0Leaves.LSum_66_83
import ThomsonCompact.Cells.base_A_05.W0Leaves.LSum_83_100
import ThomsonCompact.Cells.base_A_05.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_A_05_RootAccepted
import ThomsonCompact.Cells.base_A_08.W0Ctx
import ThomsonCompact.Cells.base_A_08.W0Sum
import ThomsonCompact.Cells.base_A_08.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L08_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L08_1_2_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L08_2_3_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_1_2_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_2_3_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_3_4_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_4_5_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_5_6_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_6_7_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L09_7_8_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_A_08.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_A_08.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_A_08.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_A_08.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_A_08_RootAccepted
import ThomsonCompact.Cells.base_B_00.W0Ctx
import ThomsonCompact.Cells.base_B_00.W0Sum
import ThomsonCompact.Cells.base_B_00.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L08_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L08_1_2_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L08_2_3_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_1_2_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_2_3_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_3_4_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_4_5_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_5_6_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_6_7_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L09_7_8_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_B_00.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_B_00.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_B_00.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_B_00.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_B_00_RootAccepted
import ThomsonCompact.Cells.base_B_02.W0Ctx
import ThomsonCompact.Cells.base_B_02.W0Sum
import ThomsonCompact.Cells.base_B_02.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L08_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L08_1_2_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L08_2_3_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_1_2_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_2_3_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_3_4_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_4_5_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_5_6_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_6_7_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L09_7_8_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_B_02.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_B_02.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_B_02.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_B_02.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_B_02_RootAccepted

/-! W0 parts of the D12 cells base_A_01, base_A_05, base_A_08, base_B_00, base_B_02 (generated by `CoeffMap/gen/w0_cells.py`): per cell the packed height
enclosure (old accepted model), the leaves and `CoeffMap.w0Part_of` / `CoeffMap.bsum_valid_of`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open ThomsonCompact.Packed ThomsonCompact.CoeffMap Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

/-! ### cell base_A_01 (index 0, N = 12) -/
namespace ThomsonCompact.Cells.C_base_A_01.W0
open Blueprint.CAP.ArithmeticPilot.base_A_01_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_A_01_RootAccepted (exponent sound)

theorem good : Good 14 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

/-- The packed height TM encloses the old accepted height `aS ∘ exponent`. -/
theorem hA : Encl ctx A (fun x => aS (exponent x)) := by
  have h := ofBoxes_sound good heightFinal.asTM sound.1
    (by decide +kernel : (ofOldTM ctx heightFinal.asTM).ok = true)
  rw [ofOldTM, (by decide +kernel : boxList heightFinal.asTM = hBoxes),
    (by decide +kernel : heightFinal.asTM.error = hErr)] at h
  exact h

theorem hord : ∀ b, (blkOf data b).order = gramBlockDimension 6 b := hord_of_data data (by decide +kernel)

theorem piece_ok (bi : Fin 14) (g : Fin 8) (r : Fin 100) (hng : (g : ℕ) < ngD12 bi) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true ∧
      ckOk ctx sumData.F 12 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 12 bi g r) = true := by
  have hr := r.isLt
  fin_cases bi
  · exact blockOkS_spec Leaves.leaf_00_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_01_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_02_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_03_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_04_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_05_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 2 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_06_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · exact blockOkS_spec Leaves.leaf_06_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_07_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_08_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_08_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_08_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 8 := hng
    rcases Nat.lt_or_ge (g : ℕ) 4 with h0 | h0
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 1 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 3 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_3_4_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 6 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 5 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_4_5_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_5_6_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 7 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_6_7_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_7_8_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_10_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_10_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_10_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_11_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_12_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_13_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr

theorem piece_ok_all (bi : Fin 14) (g : Fin 8) (r : Fin 100) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true := by
  by_cases hng : (g : ℕ) < ngD12 bi
  · exact (piece_ok bi g r hng).1
  · rw [empty_piece emptyGroupsOk_d12 _ _ _ _ _ _ bi.isLt g.isLt (by omega) r.isLt]; rfl

theorem sum_ok (r : Fin 100) : sumOkR sumData 12 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3
  · exact sumOk_spec Leaves.lsum_0_25 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_25_50 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_50_75 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_75_100 r h3.1 h3.2

/-- The 112 W0 pieces of cell base_A_01 (`B` at the internal order 14; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 14 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 12) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 12 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 12 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_A_01.W0

/-! ### cell base_A_05 (index 1, N = 17) -/
namespace ThomsonCompact.Cells.C_base_A_05.W0
open Blueprint.CAP.ArithmeticPilot.base_A_05_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_A_05_RootAccepted (exponent sound)

theorem good : Good 19 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

/-- The packed height TM encloses the old accepted height `aS ∘ exponent`. -/
theorem hA : Encl ctx A (fun x => aS (exponent x)) := by
  have h := ofBoxes_sound good heightFinal.asTM sound.1
    (by decide +kernel : (ofOldTM ctx heightFinal.asTM).ok = true)
  rw [ofOldTM, (by decide +kernel : boxList heightFinal.asTM = hBoxes),
    (by decide +kernel : heightFinal.asTM.error = hErr)] at h
  exact h

theorem hord : ∀ b, (blkOf data b).order = gramBlockDimension 6 b := hord_of_data data (by decide +kernel)

theorem piece_ok (bi : Fin 14) (g : Fin 8) (r : Fin 100) (hng : (g : ℕ) < ngD12 bi) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true ∧
      ckOk ctx sumData.F 17 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 17 bi g r) = true := by
  have hr := r.isLt
  fin_cases bi
  · exact blockOkS_spec Leaves.leaf_00_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_01_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_02_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_03_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_04_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_05_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 2 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_06_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · exact blockOkS_spec Leaves.leaf_06_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_07_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · rcases Nat.lt_or_ge (r : ℕ) 50 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_08_0_1_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_08_0_1_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (r : ℕ) 50 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_08_1_2_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_08_1_2_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (r : ℕ) 50 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_08_2_3_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_08_2_3_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 8 := hng
    rcases Nat.lt_or_ge (g : ℕ) 4 with h0 | h0
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 1 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_0_1_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_0_1_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_1_2_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_1_2_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 3 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_2_3_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_2_3_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_3_4_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_3_4_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 6 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 5 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_4_5_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_4_5_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_5_6_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_5_6_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 7 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_6_7_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_6_7_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 50 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_7_8_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_09_7_8_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_10_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_10_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_10_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_11_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_12_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_13_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr

theorem piece_ok_all (bi : Fin 14) (g : Fin 8) (r : Fin 100) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true := by
  by_cases hng : (g : ℕ) < ngD12 bi
  · exact (piece_ok bi g r hng).1
  · rw [empty_piece emptyGroupsOk_d12 _ _ _ _ _ _ bi.isLt g.isLt (by omega) r.isLt]; rfl

theorem sum_ok (r : Fin 100) : sumOkR sumData 17 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 16) ∨ (16 ≤ (r : ℕ) ∧ (r : ℕ) < 33) ∨ (33 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 66) ∨ (66 ≤ (r : ℕ) ∧ (r : ℕ) < 83) ∨ (83 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3 | h4 | h5
  · exact sumOk_spec Leaves.lsum_0_16 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_16_33 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_33_50 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_50_66 r h3.1 h3.2
  · exact sumOk_spec Leaves.lsum_66_83 r h4.1 h4.2
  · exact sumOk_spec Leaves.lsum_83_100 r h5.1 h5.2

/-- The 112 W0 pieces of cell base_A_05 (`B` at the internal order 19; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 19 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 17) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 17 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 17 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_A_05.W0

/-! ### cell base_A_08 (index 2, N = 14) -/
namespace ThomsonCompact.Cells.C_base_A_08.W0
open Blueprint.CAP.ArithmeticPilot.base_A_08_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_A_08_RootAccepted (exponent sound)

theorem good : Good 16 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

/-- The packed height TM encloses the old accepted height `aS ∘ exponent`. -/
theorem hA : Encl ctx A (fun x => aS (exponent x)) := by
  have h := ofBoxes_sound good heightFinal.asTM sound.1
    (by decide +kernel : (ofOldTM ctx heightFinal.asTM).ok = true)
  rw [ofOldTM, (by decide +kernel : boxList heightFinal.asTM = hBoxes),
    (by decide +kernel : heightFinal.asTM.error = hErr)] at h
  exact h

theorem hord : ∀ b, (blkOf data b).order = gramBlockDimension 6 b := hord_of_data data (by decide +kernel)

theorem piece_ok (bi : Fin 14) (g : Fin 8) (r : Fin 100) (hng : (g : ℕ) < ngD12 bi) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true ∧
      ckOk ctx sumData.F 14 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 14 bi g r) = true := by
  have hr := r.isLt
  fin_cases bi
  · exact blockOkS_spec Leaves.leaf_00_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_01_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_02_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_03_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_04_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_05_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 2 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_06_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · exact blockOkS_spec Leaves.leaf_06_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_07_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_08_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_08_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_08_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 8 := hng
    rcases Nat.lt_or_ge (g : ℕ) 4 with h0 | h0
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 1 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 3 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_3_4_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 6 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 5 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_4_5_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_5_6_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 7 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_6_7_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_7_8_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_10_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_10_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_10_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_11_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_12_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_13_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr

theorem piece_ok_all (bi : Fin 14) (g : Fin 8) (r : Fin 100) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true := by
  by_cases hng : (g : ℕ) < ngD12 bi
  · exact (piece_ok bi g r hng).1
  · rw [empty_piece emptyGroupsOk_d12 _ _ _ _ _ _ bi.isLt g.isLt (by omega) r.isLt]; rfl

theorem sum_ok (r : Fin 100) : sumOkR sumData 14 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3
  · exact sumOk_spec Leaves.lsum_0_25 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_25_50 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_50_75 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_75_100 r h3.1 h3.2

/-- The 112 W0 pieces of cell base_A_08 (`B` at the internal order 16; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 16 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 14) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 14 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 14 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_A_08.W0

/-! ### cell base_B_00 (index 3, N = 14) -/
namespace ThomsonCompact.Cells.C_base_B_00.W0
open Blueprint.CAP.ArithmeticPilot.base_B_00_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_B_00_RootAccepted (exponent sound)

theorem good : Good 16 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

/-- The packed height TM encloses the old accepted height `aS ∘ exponent`. -/
theorem hA : Encl ctx A (fun x => aS (exponent x)) := by
  have h := ofBoxes_sound good heightFinal.asTM sound.1
    (by decide +kernel : (ofOldTM ctx heightFinal.asTM).ok = true)
  rw [ofOldTM, (by decide +kernel : boxList heightFinal.asTM = hBoxes),
    (by decide +kernel : heightFinal.asTM.error = hErr)] at h
  exact h

theorem hord : ∀ b, (blkOf data b).order = gramBlockDimension 6 b := hord_of_data data (by decide +kernel)

theorem piece_ok (bi : Fin 14) (g : Fin 8) (r : Fin 100) (hng : (g : ℕ) < ngD12 bi) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true ∧
      ckOk ctx sumData.F 14 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 14 bi g r) = true := by
  have hr := r.isLt
  fin_cases bi
  · exact blockOkS_spec Leaves.leaf_00_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_01_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_02_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_03_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_04_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_05_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 2 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_06_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · exact blockOkS_spec Leaves.leaf_06_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_07_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_08_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_08_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_08_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 8 := hng
    rcases Nat.lt_or_ge (g : ℕ) 4 with h0 | h0
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 1 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 3 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_3_4_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 6 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 5 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_4_5_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_5_6_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 7 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_6_7_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_7_8_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_10_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_10_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_10_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_11_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_12_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_13_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr

theorem piece_ok_all (bi : Fin 14) (g : Fin 8) (r : Fin 100) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true := by
  by_cases hng : (g : ℕ) < ngD12 bi
  · exact (piece_ok bi g r hng).1
  · rw [empty_piece emptyGroupsOk_d12 _ _ _ _ _ _ bi.isLt g.isLt (by omega) r.isLt]; rfl

theorem sum_ok (r : Fin 100) : sumOkR sumData 14 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3
  · exact sumOk_spec Leaves.lsum_0_25 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_25_50 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_50_75 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_75_100 r h3.1 h3.2

/-- The 112 W0 pieces of cell base_B_00 (`B` at the internal order 16; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 16 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 14) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 14 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 14 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_B_00.W0

/-! ### cell base_B_02 (index 4, N = 13) -/
namespace ThomsonCompact.Cells.C_base_B_02.W0
open Blueprint.CAP.ArithmeticPilot.base_B_02_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_B_02_RootAccepted (exponent sound)

theorem good : Good 13 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

/-- The packed height TM encloses the old accepted height `aS ∘ exponent`. -/
theorem hA : Encl ctx A (fun x => aS (exponent x)) := by
  have h := ofBoxes_sound good heightFinal.asTM sound.1
    (by decide +kernel : (ofOldTM ctx heightFinal.asTM).ok = true)
  rw [ofOldTM, (by decide +kernel : boxList heightFinal.asTM = hBoxes),
    (by decide +kernel : heightFinal.asTM.error = hErr)] at h
  exact h

theorem hord : ∀ b, (blkOf data b).order = gramBlockDimension 6 b := hord_of_data data (by decide +kernel)

theorem piece_ok (bi : Fin 14) (g : Fin 8) (r : Fin 100) (hng : (g : ℕ) < ngD12 bi) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true ∧
      ckOk ctx sumData.F 13 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 13 bi g r) = true := by
  have hr := r.isLt
  fin_cases bi
  · exact blockOkS_spec Leaves.leaf_00_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_01_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_02_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_03_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_04_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_05_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 2 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_06_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · exact blockOkS_spec Leaves.leaf_06_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_07_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_08_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_08_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_08_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 8 := hng
    rcases Nat.lt_or_ge (g : ℕ) 4 with h0 | h0
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 1 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 3 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_3_4_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 6 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 5 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_4_5_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_5_6_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 7 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_09_6_7_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_09_7_8_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · exact blockOkS_spec Leaves.leaf_10_0_1_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_10_1_2_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_10_2_3_0_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_11_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_12_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_13_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr

theorem piece_ok_all (bi : Fin 14) (g : Fin 8) (r : Fin 100) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true := by
  by_cases hng : (g : ℕ) < ngD12 bi
  · exact (piece_ok bi g r hng).1
  · rw [empty_piece emptyGroupsOk_d12 _ _ _ _ _ _ bi.isLt g.isLt (by omega) r.isLt]; rfl

theorem sum_ok (r : Fin 100) : sumOkR sumData 13 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3
  · exact sumOk_spec Leaves.lsum_0_25 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_25_50 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_50_75 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_75_100 r h3.1 h3.2

/-- The 112 W0 pieces of cell base_B_02 (`B` at the internal order 13; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 13 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 13) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 13 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 13 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_B_02.W0

