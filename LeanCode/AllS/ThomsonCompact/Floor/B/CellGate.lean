import ThomsonCompact.Floor.B.CellAsm
import ThomsonCompact.Floor.B.SoundBridge
import ThomsonCompact.Packed.Export

/-!
# The centre gate leaf (F3c)

`centreGateOk … = true` (Init-only kernel `KernelC`) gives, per retained coordinate `i`, the integer inequality of
`centre_gate_of_int` for the decoded target TM coefficients (`decode`), the sign-magnitude sum records of F2's
checkpointed W0 sums and the centre slots (`centreGate_hint`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (slot mask)
open scoped BigOperators

theorem svK_eq (x : Bool × ℕ) : svK x = sv x := by
  rcases x with ⟨_ | _, n⟩ <;> rfl

theorem mod_div_mod_pow (x a b w : ℕ) (h : b + w ≤ a) : x % 2 ^ a / 2 ^ b % 2 ^ w = x / 2 ^ b % 2 ^ w := by
  have e : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))]

/-- the signed slots of `pvGet` are the decoded TM coefficients -/
theorem pvGet_decode {N S B W : ℕ} (v k : ℕ) (hk : k < N + 1) :
    sv (pvGet W (N + 1) v k) = (decode (mkCtx N S B W) v).getD k 0 := by
  show sv (Nat.blt (slot W (Nat.land (Nat.add v (pvBias W (N + 1))) (mask (Nat.mul W (N + 1)))) k)
      (Nat.pow 2 (Nat.sub W 1)), ndist (slot W (Nat.land (Nat.add v (pvBias W (N + 1)))
        (mask (Nat.mul W (N + 1)))) k) (Nat.pow 2 (Nat.sub W 1))) = _
  rw [Bridge.sv_slot, slot_eq, Bridge.land_mask, pvBias_eq]
  unfold decode
  simp only [mk_W, mk_m, mk_hb, mk_K, Nat.mul_eq]
  rw [List.getD_eq_getElem _ _ (by simp [digitsN]; omega), List.getElem_map]
  simp only [digitsN, List.getElem_map, List.getElem_range]
  rw [mod_div_mod_pow _ _ _ _ (by nlinarith), mod_div_mod_pow _ _ _ _ (by nlinarith)]
  push_cast
  rfl

theorem lsum_cast (l : List ℕ) : ((lsum l : ℕ) : ℤ) = (l.map (fun x : ℕ => (x : ℤ))).sum := by
  rw [lsum_eq_sum]
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- **Centre gate leaf soundness**: per coordinate the direction is a target index and the integer inequality holds. -/
theorem centreGate_hint {N B W : ℕ} {Ht : ℕ → TM} {dirT : ℕ → ℕ} {dirQ : ℕ → Bool × ℕ} {D : ℕ → List ℕ}
    {F Sc wc : ℕ} {cm Er : ℕ → ℕ}
    (h : centreGateOk (mkCtx N 256 B W) Ht dirT dirQ D F Sc wc cm Er 100 = true) (i : ℕ) (hi : i < 100) :
    dirT i < 12 ∧
      ∑ k : Fin (N + 1), |sv (dirQ i) * (decode (mkCtx N 256 B W) (Ht (dirT i)).v).getD k 0 -
        3 * (ThomsonCompact.CoeffMap.sdec ((D i).getD k 0) * 2 ^ F) -
          3 * sv (smDec (slot wc (cm i) k)) * 2 ^ (256 - Sc)| +
        3 * (((D i).getD (N + 1) 0 * 2 ^ F : ℕ) : ℤ) ≤ 3 * (Er i : ℤ) := by
  unfold centreGateOk at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.mpr hi)
  rw [Bool.and_eq_true] at h1
  refine ⟨Nat.le_of_ble_eq_true h1.1, ?_⟩
  have h2 := Nat.le_of_ble_eq_true h1.2
  have h3 : ((lsum ((List.range (N + 1)).map (cgateK (mkCtx N 256 B W) (Ht (dirT i)) (dirQ i) (D i) F Sc wc (cm i))) +
      3 * ((D i).getD (N + 1) 0 * 2 ^ F) : ℕ) : ℤ) ≤ ((3 * Er i : ℕ) : ℤ) := by exact_mod_cast h2
  push_cast at h3
  rw [lsum_cast, List.map_map, list_sum_range] at h3
  rw [← Fin.sum_univ_eq_sum_range] at h3
  refine le_trans (le_of_eq ?_) h3
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp, cgateK, Int.natCast_natAbs, svK_eq, mk_W, mk_m, mk_S]
  rw [pvGet_decode _ _ k.isLt]
  simp only [Int.ofNat_eq_natCast, Nat.pow_eq, Nat.sub_eq, Nat.cast_pow, Nat.cast_ofNat]
  ring_nf

end ThomsonCompact.Floor.B
