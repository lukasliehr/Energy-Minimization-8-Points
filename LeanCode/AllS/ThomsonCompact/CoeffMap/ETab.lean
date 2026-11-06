import Mathlib.Tactic.IntervalCases
import ThomsonCompact.CoeffMap.ETabCheck.B00_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B01_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B02_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B03_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B04_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B05_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B06_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B07_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B08_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B09_0_25
import ThomsonCompact.CoeffMap.ETabCheck.B09_25_50
import ThomsonCompact.CoeffMap.ETabCheck.B09_50_75
import ThomsonCompact.CoeffMap.ETabCheck.B09_75_100
import ThomsonCompact.CoeffMap.ETabCheck.B10_0_50
import ThomsonCompact.CoeffMap.ETabCheck.B10_50_100
import ThomsonCompact.CoeffMap.ETabCheck.B11_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B12_0_100
import ThomsonCompact.CoeffMap.ETabCheck.B13_0_100
import ThomsonCompact.CoeffMap.EGCheck.B00_0_8
import ThomsonCompact.CoeffMap.EGCheck.B01_0_8
import ThomsonCompact.CoeffMap.EGCheck.B02_0_8
import ThomsonCompact.CoeffMap.EGCheck.B03_0_8
import ThomsonCompact.CoeffMap.EGCheck.B04_0_8
import ThomsonCompact.CoeffMap.EGCheck.B05_0_8
import ThomsonCompact.CoeffMap.EGCheck.B06_0_8
import ThomsonCompact.CoeffMap.EGCheck.B07_0_8
import ThomsonCompact.CoeffMap.EGCheck.B08_0_1
import ThomsonCompact.CoeffMap.EGCheck.B08_1_2
import ThomsonCompact.CoeffMap.EGCheck.B08_2_3
import ThomsonCompact.CoeffMap.EGCheck.B08_3_4
import ThomsonCompact.CoeffMap.EGCheck.B08_4_5
import ThomsonCompact.CoeffMap.EGCheck.B08_5_6
import ThomsonCompact.CoeffMap.EGCheck.B08_6_7
import ThomsonCompact.CoeffMap.EGCheck.B08_7_8
import ThomsonCompact.CoeffMap.EGCheck.B09_0_1
import ThomsonCompact.CoeffMap.EGCheck.B09_1_2
import ThomsonCompact.CoeffMap.EGCheck.B09_2_3
import ThomsonCompact.CoeffMap.EGCheck.B09_3_4
import ThomsonCompact.CoeffMap.EGCheck.B09_4_5
import ThomsonCompact.CoeffMap.EGCheck.B09_5_6
import ThomsonCompact.CoeffMap.EGCheck.B09_6_7
import ThomsonCompact.CoeffMap.EGCheck.B09_7_8
import ThomsonCompact.CoeffMap.EGCheck.B10_0_1
import ThomsonCompact.CoeffMap.EGCheck.B10_1_2
import ThomsonCompact.CoeffMap.EGCheck.B10_2_3
import ThomsonCompact.CoeffMap.EGCheck.B10_3_4
import ThomsonCompact.CoeffMap.EGCheck.B10_4_5
import ThomsonCompact.CoeffMap.EGCheck.B10_5_6
import ThomsonCompact.CoeffMap.EGCheck.B10_6_7
import ThomsonCompact.CoeffMap.EGCheck.B10_7_8
import ThomsonCompact.CoeffMap.EGCheck.B11_0_8
import ThomsonCompact.CoeffMap.EGCheck.B12_0_8
import ThomsonCompact.CoeffMap.EGCheck.B13_0_8

/-!
# The sequential and grouped coefficient tables are the proven sparse lists (F2c)

`eTab_eq`: `listAt [] (eTab b) r = D12E.eList b r`; `eTabG_eq`: the grouped lists of `EDataG` are the filtered
tables. Assembled from the one-time check leaves `ETabCheck.*`, `EGCheck.*` (generated ranges).
-/

namespace ThomsonCompact.CoeffMap

theorem eTabOk_spec {b r0 r1 : ℕ} (h : eTabOk b r0 r1 = true) {r : ℕ} (h0 : r0 ≤ r) (h1 : r < r1) :
    listAt [] (eTab b) r = D12E.eList b r := by
  unfold eTabOk at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr h1)
  rw [show Nat.ble r0 r = true from Nat.ble_eq.mpr h0] at this
  simpa using this

theorem eGOk_spec {b g0 g1 : ℕ} (h : eGOk b g0 g1 = true) {g : ℕ} (h0 : g0 ≤ g) (h1 : g < g1) {r : ℕ} (hr : r < 100) :
    listAt [] (eTabG (Nat.add (Nat.mul 8 b) g)) r =
      (listAt [] (eTab b) r).filter fun e => Nat.beq (grpOf (D12G.gmap b) 8 e) g := by
  unfold eGOk at h
  rw [List.all_eq_true] at h
  have := h g (List.mem_range.mpr h1)
  rw [show Nat.ble g0 g = true from Nat.ble_eq.mpr h0] at this
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at this
  simpa using this r hr

theorem eTab_eq (b : ℕ) (hb : b < 14) (r : ℕ) (hr : r < 100) : listAt [] (eTab b) r = D12E.eList b r := by
  interval_cases b
  · exact eTabOk_spec eTabOk_00_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_01_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_02_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_03_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_04_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_05_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_06_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_07_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_08_0_100 (Nat.zero_le _) hr
  · rcases (show (0 ≤ r ∧ r < 25) ∨ (25 ≤ r ∧ r < 50) ∨ (50 ≤ r ∧ r < 75) ∨ (75 ≤ r ∧ r < 100) by omega) with h0 | h1 | h2 | h3
    · exact eTabOk_spec eTabOk_09_0_25 h0.1 h0.2
    · exact eTabOk_spec eTabOk_09_25_50 h1.1 h1.2
    · exact eTabOk_spec eTabOk_09_50_75 h2.1 h2.2
    · exact eTabOk_spec eTabOk_09_75_100 h3.1 h3.2
  · rcases (show (0 ≤ r ∧ r < 50) ∨ (50 ≤ r ∧ r < 100) by omega) with h0 | h1
    · exact eTabOk_spec eTabOk_10_0_50 h0.1 h0.2
    · exact eTabOk_spec eTabOk_10_50_100 h1.1 h1.2
  · exact eTabOk_spec eTabOk_11_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_12_0_100 (Nat.zero_le _) hr
  · exact eTabOk_spec eTabOk_13_0_100 (Nat.zero_le _) hr

theorem eTabG_eq (b : ℕ) (hb : b < 14) (g : ℕ) (hg : g < 8) (r : ℕ) (hr : r < 100) :
    listAt [] (eTabG (Nat.add (Nat.mul 8 b) g)) r = (listAt [] (eTab b) r).filter fun e => Nat.beq (grpOf (D12G.gmap b) 8 e) g := by
  interval_cases b
  · exact eGOk_spec eGOk_00_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_01_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_02_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_03_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_04_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_05_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_06_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_07_0_8 (Nat.zero_le _) hg hr
  · rcases (show (0 ≤ g ∧ g < 1) ∨ (1 ≤ g ∧ g < 2) ∨ (2 ≤ g ∧ g < 3) ∨ (3 ≤ g ∧ g < 4) ∨ (4 ≤ g ∧ g < 5) ∨ (5 ≤ g ∧ g < 6) ∨ (6 ≤ g ∧ g < 7) ∨ (7 ≤ g ∧ g < 8) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact eGOk_spec eGOk_08_0_1 h0.1 h0.2 hr
    · exact eGOk_spec eGOk_08_1_2 h1.1 h1.2 hr
    · exact eGOk_spec eGOk_08_2_3 h2.1 h2.2 hr
    · exact eGOk_spec eGOk_08_3_4 h3.1 h3.2 hr
    · exact eGOk_spec eGOk_08_4_5 h4.1 h4.2 hr
    · exact eGOk_spec eGOk_08_5_6 h5.1 h5.2 hr
    · exact eGOk_spec eGOk_08_6_7 h6.1 h6.2 hr
    · exact eGOk_spec eGOk_08_7_8 h7.1 h7.2 hr
  · rcases (show (0 ≤ g ∧ g < 1) ∨ (1 ≤ g ∧ g < 2) ∨ (2 ≤ g ∧ g < 3) ∨ (3 ≤ g ∧ g < 4) ∨ (4 ≤ g ∧ g < 5) ∨ (5 ≤ g ∧ g < 6) ∨ (6 ≤ g ∧ g < 7) ∨ (7 ≤ g ∧ g < 8) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact eGOk_spec eGOk_09_0_1 h0.1 h0.2 hr
    · exact eGOk_spec eGOk_09_1_2 h1.1 h1.2 hr
    · exact eGOk_spec eGOk_09_2_3 h2.1 h2.2 hr
    · exact eGOk_spec eGOk_09_3_4 h3.1 h3.2 hr
    · exact eGOk_spec eGOk_09_4_5 h4.1 h4.2 hr
    · exact eGOk_spec eGOk_09_5_6 h5.1 h5.2 hr
    · exact eGOk_spec eGOk_09_6_7 h6.1 h6.2 hr
    · exact eGOk_spec eGOk_09_7_8 h7.1 h7.2 hr
  · rcases (show (0 ≤ g ∧ g < 1) ∨ (1 ≤ g ∧ g < 2) ∨ (2 ≤ g ∧ g < 3) ∨ (3 ≤ g ∧ g < 4) ∨ (4 ≤ g ∧ g < 5) ∨ (5 ≤ g ∧ g < 6) ∨ (6 ≤ g ∧ g < 7) ∨ (7 ≤ g ∧ g < 8) by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact eGOk_spec eGOk_10_0_1 h0.1 h0.2 hr
    · exact eGOk_spec eGOk_10_1_2 h1.1 h1.2 hr
    · exact eGOk_spec eGOk_10_2_3 h2.1 h2.2 hr
    · exact eGOk_spec eGOk_10_3_4 h3.1 h3.2 hr
    · exact eGOk_spec eGOk_10_4_5 h4.1 h4.2 hr
    · exact eGOk_spec eGOk_10_5_6 h5.1 h5.2 hr
    · exact eGOk_spec eGOk_10_6_7 h6.1 h6.2 hr
    · exact eGOk_spec eGOk_10_7_8 h7.1 h7.2 hr
  · exact eGOk_spec eGOk_11_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_12_0_8 (Nat.zero_le _) hg hr
  · exact eGOk_spec eGOk_13_0_8 (Nat.zero_le _) hg hr

#print axioms eTab_eq
#print axioms eTabG_eq

end ThomsonCompact.CoeffMap
