import ThomsonCompact.Floor.B.Active
import ThomsonCompact.Floor.B.KernelC
import ThomsonCompact.Floor.B.SoundGateR
import ThomsonCompact.Packed.BridgeIn

/-!
# Cell assembly helpers (F3c)

* `rowOk_of_group`: one row of a row leaf (`rowsOk` over a group of rows);
* `errLe_spec`, `toQModel_error_le`: the error leaf bounds the target-model errors by the claims `herr`;
* `centre_gate_of_int`: the centre gate of `gateR` for point models from one exact integer inequality per
  coordinate (scale `2^-256`, centres at `2^-Sc`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open Blueprint.CAP
open scoped BigOperators

theorem rowOk_of_group {cb : CellB} {row : ℕ → RowT} {L : ℕ} {κC κD : ℤ} {Kc wv we : ℕ} {ckd : ℕ → CkRow}
    {j1 n : ℕ} (h : rowsOk cb row L κC κD Kc wv we ckd j1 n = true) (j0 i : ℕ) (h1 : j1 ≤ j0 + i)
    (h2 : j0 + i < j1 + n) :
    rowOk cb (upow cb.cT cb.U L) (chanAll cb.KC cb.M cb.WC (Nat.succ cb.N) cb.dirT cb.dirQ cb.cvc 0)
      (row (j0 + i)) κC κD Kc wv we (ckd (j0 + i)) = true := by
  have := rowsOk_row h (j0 + i - j1) (by omega)
  rwa [show j1 + (j0 + i - j1) = j0 + i by omega] at this

theorem errLe_spec (f : ℕ → ℕ) : ∀ (L : List TM) (i : ℕ), errLe f L i = true →
    ∀ t, (L.getD t zeroTM).e ≤ f (i + t)
  | [], i, _, t => by simp [zeroTM]
  | T :: L, i, h, t => by
    have h' : (Nat.ble T.e (f i) && errLe f L (Nat.succ i)) = true := h
    rw [Bool.and_eq_true] at h'
    cases t with
    | zero => simpa using Nat.le_of_ble_eq_true h'.1
    | succ t =>
      have := errLe_spec f L (i + 1) h'.2 t
      rw [List.getD_cons_succ]
      rwa [show i + 1 + t = i + (t + 1) by omega] at this

theorem getD_drop_one (L : List TM) (j : ℕ) : (L.drop 1).getD j zeroTM = L.getD (j + 1) zeroTM := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem toQModel_error_le {N B W : ℕ} (L : List TM) (f : ℕ → ℕ) (h : errLe f (L.drop 1) 0 = true) (j : ℕ) :
    (toQModel (mkCtx N 256 B W) (L.getD (j + 1) zeroTM)).error ≤ (f j : ℚ) / 2 ^ 256 := by
  have h1 := errLe_spec f (L.drop 1) 0 h j
  rw [getD_drop_one, Nat.zero_add] at h1
  show ((L.getD (j + 1) zeroTM).e : ℚ) / 2 ^ 256 ≤ _
  have : ((L.getD (j + 1) zeroTM).e : ℚ) ≤ f j := by exact_mod_cast h1
  exact div_le_div_of_nonneg_right this (by positivity)

/-- **Centre gate from integers.** Point target models `H j` (coefficients `hz j k 2^-256`), point contributions
summing to `bs i k 2^-256` with errors summing to `be i 2^-256`, directions `q i j = [j = dt i] qn i / 3`,
centres `C i k 2^-Sc` and radii `Er i 2^-256`: the gate is one integer inequality per coordinate. -/
theorem centre_gate_of_int {nI n t b : ℕ} (H : Fin t → QModel n) (B : Fin b → Fin nI → QModel n)
    (q : Fin nI → Fin t → ℚ) (center : Fin nI → Fin (n + 1) → ℚ) (err : Fin nI → ℚ)
    (hz : Fin t → Fin (n + 1) → ℤ) (bs : Fin nI → Fin (n + 1) → ℤ) (be : Fin nI → ℕ)
    (dt : Fin nI → Fin t) (qn : Fin nI → ℤ) (C : Fin nI → Fin (n + 1) → ℤ) (Er : Fin nI → ℕ) (Sc : ℕ)
    (hSc : Sc ≤ 256)
    (hH : ∀ j k, (H j).coeff k = ⟨(hz j k : ℚ) / 2 ^ 256, (hz j k : ℚ) / 2 ^ 256⟩)
    (hpt : ∀ j i k, ((B j i).coeff k).hi = ((B j i).coeff k).lo)
    (hbs : ∀ i k, ∑ j, ((B j i).coeff k).lo = (bs i k : ℚ) / 2 ^ 256)
    (hbe : ∀ i, ∑ j, (B j i).error = (be i : ℚ) / 2 ^ 256)
    (hq : ∀ i j, q i j = (if dt i = j then (qn i : ℚ) else 0) / 3)
    (hcen : ∀ i k, center i k = (C i k : ℚ) / 2 ^ Sc)
    (herr : ∀ i, err i = (Er i : ℚ) / 2 ^ 256)
    (hint : ∀ i, ∑ k, |qn i * hz (dt i) k - 3 * bs i k - 3 * C i k * 2 ^ (256 - Sc)| + 3 * (be i : ℤ) ≤
      3 * (Er i : ℤ)) :
    StructuredCenterGate (gateR H B q) center err := by
  apply centre_of_points H B q (fun j k => (hz j k : ℚ) / 2 ^ 256) (fun j i k => ((B j i).coeff k).lo) hH
    (fun j i k => by
      rcases hB : (B j i).coeff k with ⟨lo, hi⟩
      have := hpt j i k
      rw [hB] at this
      simp only at this
      rw [this])
  intro i
  have hs : ∀ k, ∑ j, q i j * ((hz j k : ℚ) / 2 ^ 256) = (qn i : ℚ) * hz (dt i) k / 2 ^ 256 / 3 := by
    intro k
    simp only [hq]
    rw [Finset.sum_eq_single (dt i)]
    · rw [if_pos rfl]; ring
    · intro j _ hj; rw [if_neg (Ne.symm hj)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : (2 : ℚ) ^ 256 = 2 ^ Sc * 2 ^ (256 - Sc) := by rw [← pow_add]; congr 1; omega
  set X : Fin (n + 1) → ℚ := fun k => (qn i : ℚ) * hz (dt i) k - 3 * bs i k - 3 * C i k * 2 ^ (256 - Sc) with hX
  have hk : ∀ k, |∑ j, q i j * ((hz j k : ℚ) / 2 ^ 256) - ∑ j, ((B j i).coeff k).lo - center i k| =
      |X k| / (3 * 2 ^ 256) := by
    intro k
    rw [hs k, hbs i k, hcen i k]
    rw [show (qn i : ℚ) * hz (dt i) k / 2 ^ 256 / 3 - bs i k / 2 ^ 256 - C i k / 2 ^ Sc =
      X k / (3 * 2 ^ 256) by
        simp only [hX]; rw [h2]; field_simp]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 3 * 2 ^ 256)]
  simp only [hk, hbe i, herr i]
  have hq3 : ((∑ k, |qn i * hz (dt i) k - 3 * bs i k - 3 * C i k * 2 ^ (256 - Sc)| + 3 * (be i : ℤ) : ℤ) : ℚ) ≤
      ((3 * (Er i : ℤ) : ℤ) : ℚ) := by exact_mod_cast hint i
  push_cast at hq3
  have h3 : (0 : ℚ) < 3 * 2 ^ 256 := by positivity
  rw [← Finset.sum_div]
  calc (∑ k, |X k|) / (3 * 2 ^ 256) + (be i : ℚ) / 2 ^ 256
      = ((∑ k, |X k|) + 3 * (be i : ℚ)) / (3 * 2 ^ 256) := by field_simp
    _ ≤ ((3 : ℚ) * (Er i : ℚ)) / (3 * 2 ^ 256) := div_le_div_of_nonneg_right hq3 h3.le
    _ = (Er i : ℚ) / 2 ^ 256 := by field_simp

end ThomsonCompact.Floor.B
