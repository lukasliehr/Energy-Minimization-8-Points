import ThomsonCompact.Floor.SoundMetric
import ThomsonCompact.Floor.B.SoundBlockQ

/-!
# The congruence matrix of F3b is the short-metric matrix of F3a

`zMat_eq_zReal`: the block leaves' `Z = Zi 2^-32` (`zMat`, sign-magnitude slots `zsm`) is F3a's `zReal`
(rows decoded by `decodeSM`), so `short_metric_sound` (F3a) and `blockOk_sound` (F3b) speak about the same `Z`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Floor (mask slot decodeSM zMatrix zent zReal)
open scoped BigOperators

theorem decodeSM_getD {w : ℕ} (hw : 1 ≤ w) : ∀ (n x u : ℕ), u < n →
    (decodeSM w n x).getD u 0 = sv (smDec (slot w x u))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => by
    show Int.subNatNat (Nat.shiftRight (Nat.land x (mask w)) 1)
        (Nat.mul (Nat.land x 1) (Nat.mul 2 (Nat.shiftRight (Nat.land x (mask w)) 1))) = _
    have hs : slot w x 0 = Nat.land x (mask w) := by
      show (x >>> (w * 0)) &&& mask w = x &&& mask w; simp
    rw [hs]
    have hb : Nat.land (Nat.land x (mask w)) 1 = Nat.land x 1 := by
      show (x &&& mask w) &&& 1 = x &&& 1
      rw [Nat.and_assoc]
      congr 1
      rw [mask_eq, Nat.and_comm, Nat.one_and_eq_mod_two, Nat.two_pow_sub_one_mod_two]
      simp; omega
    unfold smDec sv
    rw [hb]
    have h2 : Nat.land x 1 = 0 ∨ Nat.land x 1 = 1 := by
      show x &&& 1 = 0 ∨ x &&& 1 = 1
      rw [Nat.and_one_is_mod]; omega
    rcases h2 with h | h
    · rw [h]; simp [Int.subNatNat_eq_coe]
    · rw [h]; simp [Int.subNatNat_eq_coe]; ring
  | n + 1, x, u + 1, h => by
    show (decodeSM w n (Nat.shiftRight x w)).getD u 0 = _
    rw [decodeSM_getD hw n _ u (by omega)]
    congr 2
    show ((x >>> w) >>> (w * u)) &&& mask w = (x >>> (w * (u + 1))) &&& mask w
    rw [← Nat.shiftRight_add, show w + w * u = w * (u + 1) by ring]

/-- **`zMat = zReal`**: the F3b congruence matrix is the F3a short-metric matrix. -/
theorem zMat_eq_zReal (n wz : ℕ) (hw : 1 ≤ wz) (zrows : List ℕ) : zMat n wz zrows = zReal n wz zrows n := by
  ext p a
  simp only [zMat, zReal, Matrix.of_apply, zent, zMatrix]
  congr 1
  by_cases hp : p.val < zrows.length
  · rw [getD_of_lt (List.map (decodeSM wz n) zrows) [] (by simpa using hp), List.getElem_map,
      decodeSM_getD hw n _ a.val a.isLt, getD_of_lt zrows 0 hp]
    rfl
  · rw [getD_of_ge (List.map (decodeSM wz n) zrows) [] (by simp; omega), getD_of_ge zrows 0 (by omega)]
    simp [zv, zsm, smDec, sv, slot_eq]

end ThomsonCompact.Floor.B
