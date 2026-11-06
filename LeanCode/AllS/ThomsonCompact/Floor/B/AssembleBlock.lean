import ThomsonCompact.Floor.B.Assemble

/-!
# One corrected block from its row and block leaves (F3b)

`block_centre`: at every point of the height box, the congruence of the block insertion of the row values
`y_j = Σ_ch bw_ch rowS_j(ch)/λd_j / (D 2^Sc)` (Bernstein weights `bw ≥ 0`, `Σ bw = 1`) has the quadratic bound
`Gc 2^-256`. `block_error`: every vector bounded by the row error claims has the bound `Geta 2^-256`.
`heightOk_sound`, `box_param`: the height of the cell lies in the box of the row leaves.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open Blueprint.CAP
open scoped BigOperators

theorem rowsOk_row {cb : CellB} {row : ℕ → RowT} {Lmax : ℕ} {κC κD : ℤ} {Kc wv we : ℕ} {ckd : ℕ → CkRow}
    {j0 n : ℕ} (h : rowsOk cb row Lmax κC κD Kc wv we ckd j0 n = true) (i : ℕ) (hi : i < n) :
    rowOk cb (upow cb.cT cb.U Lmax) (chanAll cb.KC cb.M cb.WC (Nat.succ cb.N) cb.dirT cb.dirQ cb.cvc 0)
      (row (j0 + i)) κC κD Kc wv we (ckd (j0 + i)) = true := by
  unfold rowsOk at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem blockOk_chans {cb : CellB} {row : ℕ → RowT} {Kc wv we : ℕ} {ckd : ℕ → CkRow} {j0 nr n wz : ℕ}
    {zrows : List ℕ} {FG : ℕ} {κC : ℤ} {Sc Gc LB LE LS ch0 nch : ℕ} {ws : ℕ → List ℕ} {Γs : ℕ → ℕ}
    {wE : List ℕ} {Geta : ℕ}
    (h : blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true) :
    ch0 + nch ≤ cb.N + 1 := by
  rw [blockOk_eq] at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  exact h.1.1.2

/-- **Whole-centre bound of one block at one point of the height box.** -/
theorem block_centre (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hcs : ChanSem nI cb cvA zl)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hWC : 1 ≤ cb.WC)
    (hU : cb.U.ok = true) (hu0 : cb.ucN < 2 ^ (2 * cb.BT + 2)) (hu1 : cb.rN < 2 ^ (2 * cb.BT + 2))
    (hu2 : 2 * (cb.ucN + cb.rN) ≤ 2 ^ 256) (hKt : 1 ≤ cb.Kt)
    (row : ℕ → RowT) (a0 σ : ℝ) (H : ℕ → ℕ → ℝ → ℝ) (dl : ℕ → ℝ → ℝ) (j0 nr : ℕ)
    (hrs : ∀ i < nr, RowSem nI (row (j0 + i)) a0 σ (1 / 2) (H (j0 + i)) (dl (j0 + i)))
    (Lm : ℕ → ℕ) (κC κD : ℤ) (Kc wv we : ℕ) (ckd : ℕ → CkRow)
    (hrow : ∀ i < nr, rowOk cb (upow cb.cT cb.U (Lm i)) cvA (row (j0 + i)) κC κD Kc wv we (ckd (j0 + i)) = true)
    (n wz : ℕ) (zrows : List ℕ) (FG Sc Gc LB LE LS : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ) (wE : List ℕ) (Geta : ℕ)
    (hLB : 0 < LB) (hLE : 0 < LE) (hLS : 0 < LS)
    (huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n)
    (hblk : ∀ ch ≤ cb.N, ∃ ch0 nch, ch0 ≤ ch ∧ ch < ch0 + nch ∧
      blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true)
    (hD : 0 < cb.D)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (bw : ℕ → ℝ) (hbw0 : ∀ ch ≤ cb.N, 0 ≤ bw ch)
    (hbw1 : ∑ ch ∈ Finset.range (cb.N + 1), bw ch = 1) :
    QuadraticBound (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v)
      (fun i => ∑ ch ∈ Finset.range (cb.N + 1), bw ch *
        (rowS (row (j0 + i)) (H (j0 + i)) zl ch (a0 + σ * cb.uf t) / dl (j0 + i) (a0 + σ * cb.uf t)) /
          ((cb.D : ℝ) * 2 ^ Sc)) * (zMat n wz zrows).transpose) ((Gc : ℝ) / 2 ^ 256) := by
  set F : ℕ → ℕ → ℝ := fun i ch => (2 : ℝ) ^ κC *
    rowS (row (j0 + i)) (H (j0 + i)) zl ch (a0 + σ * cb.uf t) / dl (j0 + i) (a0 + σ * cb.uf t) with hF
  have hDr : (0 : ℝ) < (cb.D : ℝ) := by exact_mod_cast hD
  have hK : (0 : ℝ) < 2 ^ κC * ((cb.D : ℝ) * 2 ^ Sc) := by positivity
  -- per channel: the covering block leaf
  have hleaf : ∀ ch ≤ cb.N, QuadraticBound (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u)
      (fun i => (row (j0 + i)).v) (fun i => F i ch) * (zMat n wz zrows).transpose)
        (2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (Γs ch : ℝ)) ∧
      (Γs ch : ℝ) * 2 ^ ((FG : ℤ) - κC - 64) ≤ (Gc : ℝ) * cb.D * 2 ^ Sc := by
    intro ch hch
    obtain ⟨ch0, nch, h0, h1, hb⟩ := hblk ch hch
    have hcn := blockOk_chans hb
    have hT : ∀ i < nr, ∀ c < nch, Encl cb.cT ((ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c))
        (fun t => (2 : ℝ) ^ κC * rowS (row (j0 + i)) (H (j0 + i)) zl (ch0 + c) (a0 + σ * cb.uf t) /
          dl (j0 + i) (a0 + σ * cb.uf t)) := by
      intro i hi c hc
      exact (rowOk_sound cb cvA zl hcs hg hWC hU hu0 hu1 hu2 hKt (row (j0 + i)) a0 σ (H (j0 + i)) (dl (j0 + i))
        (hrs i hi) (Lm i) κC κD Kc wv we (ckd (j0 + i)) (hrow i hi)).1 (ch0 + c) (by omega)
    obtain ⟨_, hB1, hB2, _⟩ := blockOk_sound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs
      wE Geta hg hLB hLE hLS huv _ hT hb
    have e : ch0 + (ch - ch0) = ch := by omega
    have q1 := hB1 (ch - ch0) (by omega) t ht
    have q2 := hB2 (ch - ch0) (by omega)
    rw [e] at q1 q2
    exact ⟨q1, q2⟩
  apply centre_assembly n nr _ _ _ cb.N bw hbw0 hbw1 _ F (2 ^ κC * ((cb.D : ℝ) * 2 ^ Sc)) hK
    (fun i _ => by
      apply Finset.sum_congr rfl; intro ch _
      simp only [hF]
      have : (2 : ℝ) ^ κC ≠ 0 := zpow_ne_zero _ (by norm_num)
      field_simp)
    (fun ch => 2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (Γs ch : ℝ)) (fun ch hch => (hleaf ch hch).1) _ (by positivity)
  intro ch hch
  have h2 := (hleaf ch hch).2
  have e1 : (2 : ℝ) ^ ((FG : ℤ) - κC - 64) = 2 ^ ((FG : ℤ) - 64) / 2 ^ κC := by
    rw [← zpow_sub₀ (by norm_num)]; congr 1; ring
  rw [e1] at h2
  have hk : (0 : ℝ) < 2 ^ κC := zpow_pos (by norm_num) _
  rw [div_le_div_iff₀ hK (by positivity)]
  calc 2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (Γs ch : ℝ) * 2 ^ 256
      = (Γs ch : ℝ) * (2 ^ ((FG : ℤ) - 64) / 2 ^ κC) * 2 ^ κC := by field_simp
    _ ≤ (Gc : ℝ) * cb.D * 2 ^ Sc * 2 ^ κC := mul_le_mul_of_nonneg_right h2 hk.le
    _ = (Gc : ℝ) * (2 ^ κC * ((cb.D : ℝ) * 2 ^ Sc)) := by ring

/-- **Error bound of one block at one point of the height box**: every vector bounded by the row error
functions has the congruence bound `Geta 2^-256`. -/
theorem block_error (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hcs : ChanSem nI cb cvA zl)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hWC : 1 ≤ cb.WC)
    (hU : cb.U.ok = true) (hu0 : cb.ucN < 2 ^ (2 * cb.BT + 2)) (hu1 : cb.rN < 2 ^ (2 * cb.BT + 2))
    (hu2 : 2 * (cb.ucN + cb.rN) ≤ 2 ^ 256) (hKt : 1 ≤ cb.Kt)
    (row : ℕ → RowT) (a0 σ : ℝ) (H : ℕ → ℕ → ℝ → ℝ) (dl : ℕ → ℝ → ℝ) (j0 nr : ℕ)
    (hrs : ∀ i < nr, RowSem nI (row (j0 + i)) a0 σ (1 / 2) (H (j0 + i)) (dl (j0 + i)))
    (Lm : ℕ → ℕ) (κC κD : ℤ) (Kc wv we : ℕ) (ckd : ℕ → CkRow)
    (hrow : ∀ i < nr, rowOk cb (upow cb.cT cb.U (Lm i)) cvA (row (j0 + i)) κC κD Kc wv we (ckd (j0 + i)) = true)
    (n wz : ℕ) (zrows : List ℕ) (FG Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ) (wE : List ℕ)
    (Geta : ℕ) (hLB : 0 < LB) (hLE : 0 < LE) (hLS : 0 < LS)
    (huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n)
    (hb : blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (y : ℕ → ℝ)
    (hy : ∀ i < nr, |y i| ≤ rowErr cb (row (j0 + i)) (H (j0 + i)) (dl (j0 + i)) zl (a0 + σ * cb.uf t)) :
    QuadraticBound (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) y *
      (zMat n wz zrows).transpose) (1 / 2 ^ 256 * (Geta : ℝ)) := by
  have hcn := blockOk_chans hb
  have hT : ∀ i < nr, ∀ c < nch, Encl cb.cT ((ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c))
      (fun t => (2 : ℝ) ^ κC * rowS (row (j0 + i)) (H (j0 + i)) zl (ch0 + c) (a0 + σ * cb.uf t) /
        dl (j0 + i) (a0 + σ * cb.uf t)) := by
    intro i hi c hc
    exact (rowOk_sound cb cvA zl hcs hg hWC hU hu0 hu1 hu2 hKt (row (j0 + i)) a0 σ (H (j0 + i)) (dl (j0 + i))
      (hrs i hi) (Lm i) κC κD Kc wv we (ckd (j0 + i)) (hrow i hi)).1 (ch0 + c) (by omega)
  obtain ⟨_, _, _, hB3⟩ := blockOk_sound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs
    wE Geta hg hLB hLE hLS huv _ hT hb
  apply hB3 y
  intro i hi
  exact le_trans (hy i hi) ((rowOk_sound cb cvA zl hcs hg hWC hU hu0 hu1 hu2 hKt (row (j0 + i)) a0 σ (H (j0 + i))
    (dl (j0 + i)) (hrs i hi) (Lm i) κC κD Kc wv we (ckd (j0 + i)) (hrow i hi)).2 t ht)

/-! ## The height box -/

theorem heightOk_sound {N S B W : ℕ} (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f)
    (ac rg : ℕ) (h : heightOk (mkCtx N S B W) A ac rg = true) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - (ac : ℝ) / 2 ^ S| ≤ (rg : ℝ) / 2 ^ S := by
  unfold heightOk at h
  rw [Bool.and_eq_true, Nat.ble_eq] at h
  have h1 := addC_sound hA true ac 0 (-(ac : ℝ) / 2 ^ S) (by simp) h.1 hg
  intro t ht
  have h2 := rangeX_sound hg h1 t ht
  have h3 : (rangeX (mkCtx N S B W) (addC (mkCtx N S B W) true ac 0 A) : ℝ) ≤ rg := by exact_mod_cast h.2
  calc |f t - (ac : ℝ) / 2 ^ S| = |f t + -(ac : ℝ) / 2 ^ S| := by ring_nf
    _ ≤ (rangeX (mkCtx N S B W) (addC (mkCtx N S B W) true ac 0 A) : ℝ) / 2 ^ S := h2
    _ ≤ (rg : ℝ) / 2 ^ S := div_le_div_of_nonneg_right h3 (by positivity)

/-- a height in the box `a0 + σ (uc ± ρ)` is `a0 + σ uf(t)` for some `t ∈ [-1, 1]` -/
theorem box_param (cb : CellB) (a0 σ a : ℝ) (hσ : 0 < σ) (hr : 0 < cb.rN)
    (ha : |a - (a0 + σ * ((if cb.ucNeg then -(cb.ucN : ℝ) else cb.ucN) / 2 ^ 256))| ≤ σ * ((cb.rN : ℝ) / 2 ^ 256)) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1, a = a0 + σ * cb.uf t := by
  set uc := (if cb.ucNeg then -(cb.ucN : ℝ) else cb.ucN) with huc
  have hρ : (0 : ℝ) < cb.rN := by exact_mod_cast hr
  refine ⟨((a - a0) / σ * 2 ^ 256 - uc) / cb.rN, ?_, ?_⟩
  · have h1 : |(a - a0) / σ - uc / 2 ^ 256| ≤ (cb.rN : ℝ) / 2 ^ 256 := by
      have : (a - a0) / σ - uc / 2 ^ 256 = (a - (a0 + σ * (uc / 2 ^ 256))) / σ := by field_simp; ring
      rw [this, abs_div, abs_of_pos hσ, div_le_iff₀ hσ]; linarith
    have h2 : |((a - a0) / σ * 2 ^ 256 - uc) / cb.rN| ≤ 1 := by
      rw [abs_div, abs_of_pos hρ, div_le_one hρ]
      have : (a - a0) / σ * 2 ^ 256 - uc = ((a - a0) / σ - uc / 2 ^ 256) * 2 ^ 256 := by field_simp
      rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 256)]
      calc |(a - a0) / σ - uc / 2 ^ 256| * 2 ^ 256 ≤ (cb.rN : ℝ) / 2 ^ 256 * 2 ^ 256 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = cb.rN := by field_simp
    exact ⟨by linarith [(abs_le.mp h2).1], (abs_le.mp h2).2⟩
  · unfold CellB.uf
    rw [← huc]
    field_simp
    ring

end ThomsonCompact.Floor.B
