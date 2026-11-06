import ThomsonCompact.CoeffMap.W0Part
import ThomsonCompact.CoeffMap.BSumSound
import ThomsonCompact.CoeffMap.EGCheck.Empty
import ThomsonCompact.Packed.BridgeIn
import ThomsonCompact.Cells.base_B_38.W0Ctx
import ThomsonCompact.Cells.base_B_38.W0Sum
import ThomsonCompact.Cells.base_B_38.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L08_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L08_1_2_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L08_2_3_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_1_2_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_2_3_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_3_4_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_4_5_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_5_6_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_6_7_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L09_7_8_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_B_38.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_B_38.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_B_38.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_B_38.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_B_38_RootAccepted
import ThomsonCompact.Cells.base_B_41.W0Ctx
import ThomsonCompact.Cells.base_B_41.W0Sum
import ThomsonCompact.Cells.base_B_41.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L08_0_1_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L08_0_1_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L08_1_2_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L08_1_2_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L08_2_3_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L08_2_3_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_0_1_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_0_1_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_1_2_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_1_2_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_2_3_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_2_3_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_3_4_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_3_4_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_4_5_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_4_5_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_5_6_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_5_6_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_6_7_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_6_7_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_7_8_0_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.L09_7_8_50_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_B_41.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_B_41.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_B_41.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_B_41.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_B_41_RootAccepted
import ThomsonCompact.Cells.base_C_00.W0Ctx
import ThomsonCompact.Cells.base_C_00.W0Sum
import ThomsonCompact.Cells.base_C_00.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L06_0_1_0_50
import ThomsonCompact.Cells.base_C_00.W0Leaves.L06_0_1_50_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L06_1_2_0_50
import ThomsonCompact.Cells.base_C_00.W0Leaves.L06_1_2_50_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_0_1_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_0_1_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_0_1_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_1_2_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_1_2_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_1_2_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_2_3_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_2_3_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L08_2_3_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_0_1_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_0_1_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_0_1_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_1_2_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_1_2_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_1_2_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_2_3_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_2_3_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_2_3_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_3_4_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_3_4_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_3_4_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_4_5_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_4_5_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_4_5_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_5_6_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_5_6_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_5_6_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_6_7_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_6_7_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_6_7_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_7_8_0_34
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_7_8_34_67
import ThomsonCompact.Cells.base_C_00.W0Leaves.L09_7_8_67_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L10_0_1_0_50
import ThomsonCompact.Cells.base_C_00.W0Leaves.L10_0_1_50_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L10_1_2_0_50
import ThomsonCompact.Cells.base_C_00.W0Leaves.L10_1_2_50_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L10_2_3_0_50
import ThomsonCompact.Cells.base_C_00.W0Leaves.L10_2_3_50_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_0_12
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_12_25
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_25_37
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_37_50
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_50_62
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_62_75
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_75_87
import ThomsonCompact.Cells.base_C_00.W0Leaves.LSum_87_100
import ThomsonCompact.Cells.base_C_00.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_C_00_RootAccepted
import ThomsonCompact.Cells.base_C_07.W0Ctx
import ThomsonCompact.Cells.base_C_07.W0Sum
import ThomsonCompact.Cells.base_C_07.W0Leaves.L00_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L01_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L02_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L03_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L04_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L05_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L06_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L06_1_2_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L07_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L08_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L08_1_2_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L08_2_3_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_1_2_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_2_3_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_3_4_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_4_5_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_5_6_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_6_7_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L09_7_8_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L10_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L10_1_2_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L10_2_3_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L11_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L12_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.L13_0_1_0_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.LSum_0_25
import ThomsonCompact.Cells.base_C_07.W0Leaves.LSum_25_50
import ThomsonCompact.Cells.base_C_07.W0Leaves.LSum_50_75
import ThomsonCompact.Cells.base_C_07.W0Leaves.LSum_75_100
import ThomsonCompact.Cells.base_C_07.W0Leaves.LDen
import AllS.Units.N_AI.N_root_models.base_C_07_RootAccepted

/-! W0 parts of the D12 cells base_B_38, base_B_41, base_C_00, base_C_07 (generated by `CoeffMap/gen/w0_cells.py`): per cell the packed height
enclosure (old accepted model), the leaves and `CoeffMap.w0Part_of` / `CoeffMap.bsum_valid_of`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open ThomsonCompact.Packed ThomsonCompact.CoeffMap Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

/-! ### cell base_B_38 (index 15, N = 14) -/
namespace ThomsonCompact.Cells.C_base_B_38.W0
open Blueprint.CAP.ArithmeticPilot.base_B_38_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_B_38_RootAccepted (exponent sound)

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

/-- The 112 W0 pieces of cell base_B_38 (`B` at the internal order 14; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 14 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 14) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 14 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 14 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_B_38.W0

/-! ### cell base_B_41 (index 16, N = 16) -/
namespace ThomsonCompact.Cells.C_base_B_41.W0
open Blueprint.CAP.ArithmeticPilot.base_B_41_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_B_41_RootAccepted (exponent sound)

theorem good : Good 18 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

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
      ckOk ctx sumData.F 16 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 16 bi g r) = true := by
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

theorem sum_ok (r : Fin 100) : sumOkR sumData 16 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3
  · exact sumOk_spec Leaves.lsum_0_25 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_25_50 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_50_75 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_75_100 r h3.1 h3.2

/-- The 112 W0 pieces of cell base_B_41 (`B` at the internal order 18; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 18 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 16) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 16 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 16 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_B_41.W0

/-! ### cell base_C_00 (index 17, N = 27) -/
namespace ThomsonCompact.Cells.C_base_C_00.W0
open Blueprint.CAP.ArithmeticPilot.base_C_00_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_C_00_RootAccepted (exponent sound)

theorem good : Good 31 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

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
      ckOk ctx sumData.F 27 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 27 bi g r) = true := by
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
    · rcases Nat.lt_or_ge (r : ℕ) 50 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_06_0_1_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_06_0_1_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (r : ℕ) 50 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_06_1_2_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_06_1_2_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_07_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · rcases Nat.lt_or_ge (r : ℕ) 34 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_08_0_1_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (r : ℕ) 67 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_08_0_1_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_08_0_1_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (r : ℕ) 34 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_08_1_2_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 67 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_08_1_2_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_08_1_2_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (r : ℕ) 34 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_08_2_3_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 67 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_08_2_3_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
          · exact blockOkS_spec Leaves.leaf_08_2_3_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 8 := hng
    rcases Nat.lt_or_ge (g : ℕ) 4 with h0 | h0
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 1 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_0_1_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_0_1_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_0_1_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_1_2_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_1_2_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_1_2_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 3 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_2_3_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_2_3_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_2_3_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_3_4_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_3_4_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_3_4_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 6 with h1 | h1
      · rcases Nat.lt_or_ge (g : ℕ) 5 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_4_5_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_4_5_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_4_5_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_5_6_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_5_6_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_5_6_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (g : ℕ) 7 with h2 | h2
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_6_7_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_6_7_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_6_7_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
        · rcases Nat.lt_or_ge (r : ℕ) 34 with h3 | h3
          · exact blockOkS_spec Leaves.leaf_09_7_8_0_34 g (by omega) (by omega) r (by omega) (by omega) hr
          · rcases Nat.lt_or_ge (r : ℕ) 67 with h4 | h4
            · exact blockOkS_spec Leaves.leaf_09_7_8_34_67 g (by omega) (by omega) r (by omega) (by omega) hr
            · exact blockOkS_spec Leaves.leaf_09_7_8_67_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · have hng' : (g : ℕ) < 3 := hng
    rcases Nat.lt_or_ge (g : ℕ) 1 with h0 | h0
    · rcases Nat.lt_or_ge (r : ℕ) 50 with h1 | h1
      · exact blockOkS_spec Leaves.leaf_10_0_1_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
      · exact blockOkS_spec Leaves.leaf_10_0_1_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
    · rcases Nat.lt_or_ge (g : ℕ) 2 with h1 | h1
      · rcases Nat.lt_or_ge (r : ℕ) 50 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_10_1_2_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_10_1_2_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
      · rcases Nat.lt_or_ge (r : ℕ) 50 with h2 | h2
        · exact blockOkS_spec Leaves.leaf_10_2_3_0_50 g (by omega) (by omega) r (by omega) (by omega) hr
        · exact blockOkS_spec Leaves.leaf_10_2_3_50_100 g (by omega) (by omega) r (by omega) (by omega) hr
  · exact blockOkS_spec Leaves.leaf_11_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_12_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr
  · exact blockOkS_spec Leaves.leaf_13_0_1_0_100 g (Nat.zero_le _) hng r (Nat.zero_le _) hr hr

theorem piece_ok_all (bi : Fin 14) (g : Fin 8) (r : Fin 100) :
    (blockTMgr ctx A (WTp data ctx bi) bi g r).ok = true := by
  by_cases hng : (g : ℕ) < ngD12 bi
  · exact (piece_ok bi g r hng).1
  · rw [empty_piece emptyGroupsOk_d12 _ _ _ _ _ _ bi.isLt g.isLt (by omega) r.isLt]; rfl

theorem sum_ok (r : Fin 100) : sumOkR sumData 27 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 12) ∨ (12 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 37) ∨ (37 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 62) ∨ (62 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 87) ∨ (87 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact sumOk_spec Leaves.lsum_0_12 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_12_25 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_25_37 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_37_50 r h3.1 h3.2
  · exact sumOk_spec Leaves.lsum_50_62 r h4.1 h4.2
  · exact sumOk_spec Leaves.lsum_62_75 r h5.1 h5.2
  · exact sumOk_spec Leaves.lsum_75_87 r h6.1 h6.2
  · exact sumOk_spec Leaves.lsum_87_100 r h7.1 h7.2

/-- The 112 W0 pieces of cell base_C_00 (`B` at the internal order 31; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 31 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 27) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 27 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 27 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_C_00.W0

/-! ### cell base_C_07 (index 18, N = 15) -/
namespace ThomsonCompact.Cells.C_base_C_07.W0
open Blueprint.CAP.ArithmeticPilot.base_C_07_RootCompositionGates (heightFinal)
open Blueprint.CAP.Instances.base_C_07_RootAccepted (exponent sound)

theorem good : Good 15 160 200 402 := ⟨by decide, by decide, by decide, by decide +kernel⟩

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
      ckOk ctx sumData.F 15 (blockTMgr ctx A (WTp data ctx bi) bi g r) (ckRec sumData 15 bi g r) = true := by
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

theorem sum_ok (r : Fin 100) : sumOkR sumData 15 r = true := by
  have hr := r.isLt
  rcases (show (0 ≤ (r : ℕ) ∧ (r : ℕ) < 25) ∨ (25 ≤ (r : ℕ) ∧ (r : ℕ) < 50) ∨ (50 ≤ (r : ℕ) ∧ (r : ℕ) < 75) ∨ (75 ≤ (r : ℕ) ∧ (r : ℕ) < 100) by omega) with h0 | h1 | h2 | h3
  · exact sumOk_spec Leaves.lsum_0_25 r h0.1 h0.2
  · exact sumOk_spec Leaves.lsum_25_50 r h1.1 h1.2
  · exact sumOk_spec Leaves.lsum_50_75 r h2.1 h2.2
  · exact sumOk_spec Leaves.lsum_75_100 r h3.1 h3.2

/-- The 112 W0 pieces of cell base_C_07 (`B` at the internal order 15; `g`, `W0_link`). -/
noncomputable def w0Part : W0Part exponent data.cell (blkOf data) hord 15 112 :=
  w0Part_of good data exponent hA hord piece_ok_all Leaves.leaf_den

/-- **The W0 sum per retained coordinate (order 15) encloses `Σ_b g b r`** (one combined W0 model). -/
theorem Bsum_valid (r : Fin 100) :
    (BsumQ 15 160 sumData r).asTM.Valid (fun x => ∑ ι, w0Part.g ι r x) :=
  bsum_valid_of good data exponent hA hord sumData emptyGroupsOk_d12 15 (by decide) piece_ok sum_ok r

#print axioms w0Part
#print axioms Bsum_valid

end ThomsonCompact.Cells.C_base_C_07.W0

