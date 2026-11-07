import ThomsonCompact.CoeffMap.Deg.ProgSound
import ThomsonCompact.CoeffMap.BSumSound

/-!
# Soundness of the checkpointed W0 sums of any degree (F2f)

The pieces are `(b, g, h)` (block, group, owner part); every piece TM is checkpointed at the scale `2^-(S-F)`
(`ckRecD`), the sum leaves check the final records against the checkpoints of all pieces (`sumOkRD`). Here:

* `sumOkRD_spec`: the final record holds the exact coefficient sums and at least the error sum of the checkpoints;
* `bsum_validD`: if every piece TM encloses its function and matches its checkpoint, the final record (`BsumD`, a
  point QModel of the target order) encloses the sum of the piece functions.

Reuses `ck_valid`, `valid_sum`, `accRecs_spec`, `smAll_spec` of the D12 `CoeffMap.BSumSound` (generic).
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

/-- The final sum QModel at coordinate `r` (point coefficients `sdec Dₖ 2^F / 2^S`, error `D_e 2^F / 2^S`). -/
noncomputable def BsumD (n S : ℕ) (sd : SumD) (r : ℕ) : QModel n := ckQ n S sd.F (dRecD sd n r)

namespace DegD

variable (L : DegD)

theorem recsAtD_sum {M : Type*} [AddCommMonoid M] (sd : SumD) (n r : ℕ) (φ : List ℕ → M) :
    ((L.recsAtD sd n r).map φ).sum = ∑ b ∈ Finset.range (Nat.add L.dH 8), ∑ g ∈ Finset.range (L.nGrp b),
      ∑ h ∈ Finset.range (sd.np b), φ (ckRecD sd n b g h r) := by
  unfold DegD.recsAtD
  rw [sum_map_flatMap, lsum_range]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [sum_map_flatMap, lsum_range]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [List.map_map]
  exact lsum_range _ _

/-- **The sum leaf**: exact coefficient sums and at least the error sum of the checkpoints at `r`. -/
theorem sumOkRD_spec (sd : SumD) (n r : ℕ) (h : L.sumOkRD sd n r = true) :
    (∀ k, k < n + 1 → sdec ((dRecD sd n r).getD k 0) = ∑ b ∈ Finset.range (Nat.add L.dH 8),
      ∑ g ∈ Finset.range (L.nGrp b), ∑ hh ∈ Finset.range (sd.np b), sdec ((ckRecD sd n b g hh r).getD k 0)) ∧
    ∑ b ∈ Finset.range (Nat.add L.dH 8), ∑ g ∈ Finset.range (L.nGrp b), ∑ hh ∈ Finset.range (sd.np b),
      (ckRecD sd n b g hh r).getD (n + 1) 0 ≤ (dRecD sd n r).getD (n + 1) 0 := by
  unfold DegD.sumOkRD at h
  obtain ⟨hl, hv, he⟩ := accRecs_spec (Nat.add n 1) (L.recsAtD sd n r) (List.replicate (Nat.add n 1) (0, 0)) 0
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hs, hle⟩ := h
  obtain ⟨hlen, hk⟩ := smAll_spec _ _ hs
  have hdl : (dRecD sd n r).length = n + 2 := decRec_length _ _ _ _
  refine ⟨fun k hk' => ?_, ?_⟩
  · have h1 := hk k (by rw [List.length_take, hdl]; show k < min (n + 1) (n + 2); omega)
    rw [getD_take_of_lt _ (show k < Nat.add n 1 from hk')] at h1
    rw [h1, hv k (by rw [List.length_replicate]; exact hk')]
    have h0 : pval ((List.replicate (Nat.add n 1) ((0 : ℕ), (0 : ℕ))).getD k (0, 0)) = 0 := by
      have : (List.replicate (Nat.add n 1) ((0 : ℕ), (0 : ℕ))).getD k (0, 0) = (0, 0) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [this]
      simp [pval]
    rw [h0, zero_add, L.recsAtD_sum sd n r (fun rec => sdec ((rec.take (Nat.add n 1)).getD k 0))]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun hh _ => ?_)))
    rw [getD_take_of_lt _ (show k < Nat.add n 1 from hk')]
  · rw [he, zero_add, L.recsAtD_sum sd n r (fun rec => rec.getD (Nat.add n 1) 0)] at hle
    exact hle

theorem sumOkD_spec (sd : SumD) {n r0 r1 : ℕ} (h : L.sumOkD sd n r0 r1 = true) :
    ∀ r, r0 ≤ r → r < r1 → L.sumOkRD sd n r = true := by
  intro r h0 h1
  unfold DegD.sumOkD at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr h1)
  rw [show Nat.ble r0 r = true from Nat.ble_eq.mpr h0] at this
  simpa using this

end DegD

/-- A point QModel summing the coefficients `p i` and errors `e i` over `s`. -/
noncomputable def pointSum {n : ℕ} {ι : Type*} (s : Finset ι) (p : ι → Fin (n + 1) → ℚ) (e : ι → ℚ) : QModel n :=
  ⟨fun k => ⟨∑ i ∈ s, p i k, ∑ i ∈ s, p i k⟩, ∑ i ∈ s, e i⟩

theorem pointSum_valid {n : ℕ} {ι : Type*} (s : Finset ι) (M : ι → QModel n) (f : ι → ℝ → ℝ)
    (p : ι → Fin (n + 1) → ℚ) (hp : ∀ i k, (M i).coeff k = ⟨p i k, p i k⟩) (hv : ∀ i ∈ s, (M i).asTM.Valid (f i)) :
    (pointSum s p (fun i => (M i).error)).asTM.Valid (fun x => ∑ i ∈ s, f i x) :=
  valid_sum s M f p hp hv _ (fun _ => rfl) le_rfl

/-- The coefficients of a checkpoint QModel at the scale. -/
noncomputable def ckP (S F : ℕ) (rec : List ℕ) (n : ℕ) (k : Fin (n + 1)) : ℚ :=
  (sdec (rec.getD k.val 0) : ℚ) * 2 ^ F / 2 ^ S

/-- **The final records enclose the sum of the piece functions** (any degree). -/
theorem bsum_validD {N S B W : ℕ} (hg : Good N S B W) (L : DegD) (sd : SumD) (n : ℕ) (hn : n ≤ N)
    (f : ℕ → ℕ → ℕ → ℝ → ℝ) (T : ℕ → ℕ → ℕ → TM) (r : ℕ)
    (hpc : ∀ b, b < Nat.add L.dH 8 → ∀ g, g < L.nGrp b → ∀ h, h < sd.np b →
      Encl (mkCtx N S B W) (T b g h) (f b g h) ∧ ckOk (mkCtx N S B W) sd.F n (T b g h) (ckRecD sd n b g h r) = true)
    (hsum : L.sumOkRD sd n r = true) :
    (BsumD n S sd r).asTM.Valid (fun x => ∑ b ∈ Finset.range (Nat.add L.dH 8), ∑ g ∈ Finset.range (L.nGrp b),
      ∑ h ∈ Finset.range (sd.np b), f b g h x) := by
  obtain ⟨hD, hEr⟩ := L.sumOkRD_spec sd n r hsum
  have hlen : ∀ b g h, n + 1 ≤ (ckRecD sd n b g h r).length := by
    intro b g h; unfold ckRecD; rw [decRec_length]; show n + 1 ≤ n + 2; omega
  -- parts
  have h3 : ∀ b ∈ Finset.range (Nat.add L.dH 8), ∀ g ∈ Finset.range (L.nGrp b),
      (pointSum (Finset.range (sd.np b)) (fun h => ckP S sd.F (ckRecD sd n b g h r) n)
        (fun h => (ckQ n S sd.F (ckRecD sd n b g h r)).error)).asTM.Valid
        (fun x => ∑ h ∈ Finset.range (sd.np b), f b g h x) := by
    intro b hb g hgr
    refine pointSum_valid _ (fun h => ckQ n S sd.F (ckRecD sd n b g h r)) (f b g)
      (fun h => ckP S sd.F (ckRecD sd n b g h r) n) (fun _ _ => rfl) (fun h hh => ?_)
    obtain ⟨hE, hck⟩ := hpc b (Finset.mem_range.mp hb) g (Finset.mem_range.mp hgr) h (Finset.mem_range.mp hh)
    exact ck_valid hg hE sd.F n hn _ (hlen b g h) hck
  -- groups
  have h2 : ∀ b ∈ Finset.range (Nat.add L.dH 8),
      (pointSum (Finset.range (L.nGrp b)) (fun g k => ∑ h ∈ Finset.range (sd.np b), ckP S sd.F (ckRecD sd n b g h r) n k)
        (fun g => ∑ h ∈ Finset.range (sd.np b), (ckQ n S sd.F (ckRecD sd n b g h r)).error)).asTM.Valid
        (fun x => ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b), f b g h x) := by
    intro b hb
    exact valid_sum _ (fun g => pointSum (Finset.range (sd.np b)) (fun h => ckP S sd.F (ckRecD sd n b g h r) n)
        (fun h => (ckQ n S sd.F (ckRecD sd n b g h r)).error)) (fun g x => ∑ h ∈ Finset.range (sd.np b), f b g h x)
      (fun g k => ∑ h ∈ Finset.range (sd.np b), ckP S sd.F (ckRecD sd n b g h r) n k) (fun _ _ => rfl)
      (h3 b hb) _ (fun _ => rfl) le_rfl
  -- blocks and the final record
  refine valid_sum _ (fun b => pointSum (Finset.range (L.nGrp b))
      (fun g k => ∑ h ∈ Finset.range (sd.np b), ckP S sd.F (ckRecD sd n b g h r) n k)
      (fun g => ∑ h ∈ Finset.range (sd.np b), (ckQ n S sd.F (ckRecD sd n b g h r)).error)) _
    (fun b k => ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b), ckP S sd.F (ckRecD sd n b g h r) n k)
    (fun _ _ => rfl) h2 (BsumD n S sd r) (fun k => ?_) ?_
  · show (⟨_, _⟩ : QInterval) = _
    unfold ckP
    rw [hD k.val k.isLt]
    push_cast
    simp only [Finset.sum_mul, Finset.sum_div]
  · show ∑ b ∈ Finset.range (Nat.add L.dH 8), ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
        ((ckRecD sd n b g h r).getD (n + 1) 0 : ℚ) * 2 ^ sd.F / 2 ^ S ≤ ((dRecD sd n r).getD (n + 1) 0 : ℚ) * 2 ^ sd.F / 2 ^ S
    simp only [← Finset.sum_div, ← Finset.sum_mul]
    have : (∑ b ∈ Finset.range (Nat.add L.dH 8), ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
        ((ckRecD sd n b g h r).getD (n + 1) 0 : ℚ)) ≤ ((dRecD sd n r).getD (n + 1) 0 : ℚ) := by exact_mod_cast hEr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)) (by positivity)

#print axioms bsum_validD

end ThomsonCompact.CoeffMap.Deg
