import ThomsonCompact.Floor.B.ActiveG
import ThomsonCompact.Floor.B.SoundBlockSplit

/-!
# Corrected blocks with column-split block leaves (F3f)

`BlockLeavesQ` is `BlockLeaves` whose block leaves may be column-split (`blockSplitOk`: column leaves `blockOkQ` +
aggregation leaf `blockAggOk`, `Floor/B/SoundBlockSplit.lean`) per channel group; `BlockLeavesQ.activeT` is
`BlockLeaves.activeT` for it (`block_centreS`/`block_errorS` take the per-channel-group conclusions `BlockSound`).
`BlockLeaves.toQ` embeds the plain version. The D12 builders (`BlockLeaves.active`) are unchanged.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- the block leaves of one channel group: one plain leaf or the column-split leaves -/
def BlockLeafOk (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ)
    (wE : List ℕ) (Geta : ℕ) : Prop :=
  blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true ∨
    blockSplitOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta

theorem BlockLeafOk.sound {cb : CellB} {row : ℕ → RowT} {Kc wv we : ℕ} {ckd : ℕ → CkRow} {j0 nr n wz : ℕ}
    {zrows : List ℕ} {FG : ℕ} {κC : ℤ} {Sc Gc LB LE LS ch0 nch : ℕ} {ws : ℕ → List ℕ} {Γs : ℕ → ℕ}
    {wE : List ℕ} {Geta : ℕ}
    (h : BlockLeafOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hLB : 0 < LB) (hLE : 0 < LE) (hLS : 0 < LS)
    (huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n) :
    BlockSound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc ch0 nch Γs Geta := by
  rcases h with h | h
  · exact blockOk_blockSound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta hg hLB
      hLE hLS huv h
  · exact blockSplit_sound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta hg hLB
      hLE hLS huv h

/-- **Whole-centre bound of one block at one point of the height box.** -/
theorem block_centreS (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hcs : ChanSem nI cb cvA zl)
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
      BlockSound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc ch0 nch Γs Geta)
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
    obtain ⟨ch0, nch, h0, h1, hcn, hb⟩ := hblk ch hch
    have hT : ∀ i < nr, ∀ c < nch, Encl cb.cT ((ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c))
        (fun t => (2 : ℝ) ^ κC * rowS (row (j0 + i)) (H (j0 + i)) zl (ch0 + c) (a0 + σ * cb.uf t) /
          dl (j0 + i) (a0 + σ * cb.uf t)) := by
      intro i hi c hc
      exact (rowOk_sound cb cvA zl hcs hg hWC hU hu0 hu1 hu2 hKt (row (j0 + i)) a0 σ (H (j0 + i)) (dl (j0 + i))
        (hrs i hi) (Lm i) κC κD Kc wv we (ckd (j0 + i)) (hrow i hi)).1 (ch0 + c) (by omega)
    obtain ⟨hB1, hB2, _⟩ := hb _ hT
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
theorem block_errorS (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hcs : ChanSem nI cb cvA zl)
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
    (hb : BlockSound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc ch0 nch Γs Geta)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (y : ℕ → ℝ)
    (hy : ∀ i < nr, |y i| ≤ rowErr cb (row (j0 + i)) (H (j0 + i)) (dl (j0 + i)) zl (a0 + σ * cb.uf t)) :
    QuadraticBound (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) y *
      (zMat n wz zrows).transpose) (1 / 2 ^ 256 * (Geta : ℝ)) := by
  obtain ⟨hcn, hb⟩ := hb
  have hT : ∀ i < nr, ∀ c < nch, Encl cb.cT ((ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c))
      (fun t => (2 : ℝ) ^ κC * rowS (row (j0 + i)) (H (j0 + i)) zl (ch0 + c) (a0 + σ * cb.uf t) /
        dl (j0 + i) (a0 + σ * cb.uf t)) := by
    intro i hi c hc
    exact (rowOk_sound cb cvA zl hcs hg hWC hU hu0 hu1 hu2 hKt (row (j0 + i)) a0 σ (H (j0 + i)) (dl (j0 + i))
      (hrs i hi) (Lm i) κC κD Kc wv we (ckd (j0 + i)) (hrow i hi)).1 (ch0 + c) (by omega)
  obtain ⟨_, _, hB3⟩ := hb _ hT
  apply hB3 y
  intro i hi
  exact le_trans (hy i hi) ((rowOk_sound cb cvA zl hcs hg hWC hU hu0 hu1 hu2 hKt (row (j0 + i)) a0 σ (H (j0 + i))
    (dl (j0 + i)) (hrs i hi) (Lm i) κC κD Kc wv we (ckd (j0 + i)) (hrow i hi)).2 t ht)

/-- the F3b data and the leaf facts of one corrected block, plain or column-split block leaves (rows `j0 … j0+nr-1` of `row`, block order `n`) -/
structure BlockLeavesQ (cb : CellB) (row : ℕ → RowT) (j0 nr n : ℕ) where
  κC : ℤ
  κD : ℤ
  Kc : ℕ
  wv : ℕ
  we : ℕ
  ckd : ℕ → CkRow
  Lm : ℕ → ℕ
  wz : ℕ
  zrows : List ℕ
  FG : ℕ
  Sc : ℕ
  Gc : ℕ
  LB : ℕ
  LE : ℕ
  LS : ℕ
  ws : ℕ → List ℕ
  Γs : ℕ → ℕ
  wE : List ℕ
  Geta : ℕ
  hLB : 0 < LB
  hLE : 0 < LE
  hLS : 0 < LS
  hwz : 1 ≤ wz
  huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n
  rows : ∀ i < nr, rowOk cb (upow cb.cT cb.U (Lm i))
    (chanAll cb.KC cb.M cb.WC (Nat.succ cb.N) cb.dirT cb.dirQ cb.cvc 0) (row (j0 + i)) κC κD Kc wv we
    (ckd (j0 + i)) = true
  blocks : ∀ ch ≤ cb.N, ∃ ch0 nch, ch0 ≤ ch ∧ ch < ch0 + nch ∧
    BlockLeafOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta


/-- the plain block leaves as (unsplit) `BlockLeavesQ` -/
def BlockLeaves.toQ {cb : CellB} {row : ℕ → RowT} {j0 nr n : ℕ} (BL : BlockLeaves cb row j0 nr n) :
    BlockLeavesQ cb row j0 nr n where
  κC := BL.κC
  κD := BL.κD
  Kc := BL.Kc
  wv := BL.wv
  we := BL.we
  ckd := BL.ckd
  Lm := BL.Lm
  wz := BL.wz
  zrows := BL.zrows
  FG := BL.FG
  Sc := BL.Sc
  Gc := BL.Gc
  LB := BL.LB
  LE := BL.LE
  LS := BL.LS
  ws := BL.ws
  Γs := BL.Γs
  wE := BL.wE
  Geta := BL.Geta
  hLB := BL.hLB
  hLE := BL.hLE
  hLS := BL.hLS
  hwz := BL.hwz
  huv := BL.huv
  rows := BL.rows
  blocks := fun ch hch => by
    obtain ⟨ch0, nch, h0, h1, hb⟩ := BL.blocks ch hch
    exact ⟨ch0, nch, h0, h1, Or.inl hb⟩

/-- the per-channel-group conclusions of the block leaves -/
theorem BlockLeavesQ.sound {cb : CellB} {row : ℕ → RowT} {j0 nr n : ℕ} (BL : BlockLeavesQ cb row j0 nr n)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) :
    ∀ ch ≤ cb.N, ∃ ch0 nch, ch0 ≤ ch ∧ ch < ch0 + nch ∧
      BlockSound cb row BL.Kc BL.wv BL.we BL.ckd j0 nr n BL.wz BL.zrows BL.FG BL.κC BL.Sc BL.Gc ch0 nch BL.Γs BL.Geta := by
  intro ch hch
  obtain ⟨ch0, nch, h0, h1, hb⟩ := BL.blocks ch hch
  exact ⟨ch0, nch, h0, h1, hb.sound hg BL.hLB BL.hLE BL.hLS BL.huv⟩

/-- **The fields of a corrected block** from its leaves (plain or column-split block leaves) and the cell facts
(any degree). -/
noncomputable def BlockLeavesQ.activeT {nI : ℕ} {T : TabSpec nI} {s : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT}
    {j0 nr n : ℕ} (BL : BlockLeavesQ cb row j0 nr n) (hC : CellFactsT T s cb row)
    (hdl : ∀ a, physical a → ∀ j < nI, T.dl j a ≠ 0)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {H : Fin cb.nT → QModel cb.N} {q : Fin nI → Fin cb.nT → ℚ}
    {center : Fin nI → Fin (cb.N + 1) → ℚ} {err : Fin nI → ℚ}
    (hcen : ∀ r : Fin nI, ∀ k : Fin (cb.N + 1),
      center r k = (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ BL.Sc)
    (hq : ∀ r : Fin nI, ∀ j : Fin cb.nT, q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hH : ∀ j : Fin cb.nT, (H j).error ≤ (cb.herr j : ℚ) / 2 ^ 256)
    (herr : ∀ r : Fin nI, err r ≤ (cb.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ nI)
    (hname : ∀ k : Fin nI, (T.coords k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => BL.Gc) BL.Geta (BL.Gc + BL.Geta) claim (32 + mb) E = true) :
    ActiveT T s cell X name H q center err where
  Z := zMat X.order BL.wz BL.zrows
  θ := (claim : ℝ) / 2 ^ (32 + mb)
  γ := ((BL.Gc + BL.Geta : ℕ) : ℝ) / 2 ^ 256
  short_metric := by
    subst hX
    rw [zMat_eq_zReal X.order BL.wz BL.hwz BL.zrows]
    exact ThomsonCompact.Floor.short_metric_sound X X.order BL.wz cell.metricBits mb BL.zrows ex kl claim rfl hex hkl hθ
  gap := by
    have h := ThomsonCompact.Floor.gap_sound hgap
    rw [hE]
    exact h
  γc := (BL.Gc : ℚ) / 2 ^ 256
  η := (BL.Geta : ℝ) / 2 ^ 256
  total := by
    push_cast
    rw [add_div]
  centerBound := by
    subst hX
    intro x hx
    obtain ⟨tt, htt, ha⟩ := hC.box x hx
    have hlen := chanOk_len cb nI hC.chan
    obtain ⟨hU, hu0, hu1, hu2, hKt, -⟩ := chanOk_facts cb nI hC.chan
    rw [outputInsertion_eq_insMT T.coords name X.order j0 nr hnr row
      (fun i hi => (hC.rows (j0 + i) (by omega)).coord _) hname]
    rw [insM_congr_vec X.order nr _ _ _ (fun i => ∑ ch ∈ Finset.range (cb.N + 1), bernsteinWeight cb.N ch x *
        (rowS (row (j0 + i)) (T.Hd (j0 + i)) (chanZc cb) ch (T.a0 + T.σ * cb.uf tt) /
          T.dl (j0 + i) (T.a0 + T.σ * cb.uf tt)) / ((cb.D : ℝ) * 2 ^ BL.Sc)) (fun i hi => by
        have hj : j0 + i < nI := by omega
        rw [dif_pos hj, centre_vecT T cb hlen BL.Sc center hcen (row (j0 + i)) (j0 + i) hj
          (hC.rows (j0 + i) hj).sem.sorted (hC.rows (j0 + i) hj).sem.ltn (hC.rows (j0 + i) hj).zero, ha])]
    have hbw1 : ∑ ch ∈ Finset.range (cb.N + 1), bernsteinWeight cb.N ch x = 1 := by
      rw [← Fin.sum_univ_eq_sum_range (fun ch => bernsteinWeight cb.N ch x) (cb.N + 1)]
      exact bernsteinWeight_sum cb.N x
    have hbc := block_centreS cb _ (chanZc cb) (chanOk_sound cb nI hC.chan) hC.good hC.wc1 hU hu0 hu1 hu2
      hKt row T.a0 T.σ T.Hd T.dl j0 nr (fun i hi => (hC.rows (j0 + i) (by omega)).sem) BL.Lm BL.κC BL.κD BL.Kc
      BL.wv BL.we BL.ckd BL.rows X.order BL.wz BL.zrows BL.FG BL.Sc BL.Gc BL.LB BL.LE BL.LS BL.ws BL.Γs BL.wE
      BL.Geta BL.hLB BL.hLE BL.hLS BL.huv (BL.sound hC.good) (bernDen_pos cb.N) tt htt (fun ch => bernsteinWeight cb.N ch x)
      (fun ch _ => bernsteinWeight_nonneg cb.N ch x hx) hbw1
    push_cast
    exact hbc
  error := by
    subst hX
    intro x hx e ε he hε
    obtain ⟨tt, htt, ha⟩ := hC.box x hx
    have hs := hC.s_nonneg x hx
    have hphys := aS_physical (s x) hs
    have hlen := chanOk_len cb nI hC.chan
    obtain ⟨hU, hu0, hu1, hu2, hKt, -⟩ := chanOk_facts cb nI hC.chan
    obtain ⟨ch0, nch, -, -, hb⟩ := BL.sound hC.good 0 (Nat.zero_le _)
    rw [outputInsertion_eq_insMT T.coords name X.order j0 nr hnr row
      (fun i hi => (hC.rows (j0 + i) (by omega)).coord _) hname]
    have he' : ∀ tt < cb.nT, |extN e tt| ≤ (cb.herr tt : ℝ) / 2 ^ 256 := by
      intro tt htt
      simp only [extN, dif_pos htt]
      refine (he ⟨tt, htt⟩).trans ?_
      have h2 := (Rat.cast_le (K := ℝ)).mpr (hH ⟨tt, htt⟩)
      push_cast at h2
      exact h2
    have hq' : ∀ m < nI, ∀ tt < cb.nT, extQ q m tt = (((chanZc cb m).getD (cb.N + 1 + tt) 0 : ℤ) : ℝ) / 3 := by
      intro m hm tt htt
      simp only [extQ, dif_pos (And.intro hm htt), hq]
      rw [chanZc_of_lt cb (by rw [hlen]; exact hm), chanZ_getD_dir cb m tt htt]
      split_ifs <;> simp
    have hε' : ∀ m < nI, |extN ε m| ≤ (cb.Er m : ℝ) / 2 ^ 256 := by
      intro m hm
      simp only [extN, dif_pos hm]
      refine (hε ⟨m, hm⟩).trans ?_
      have h2 := (Rat.cast_le (K := ℝ)).mpr (herr ⟨m, hm⟩)
      push_cast at h2
      exact h2
    have hbe := block_errorS cb _ (chanZc cb) (chanOk_sound cb nI hC.chan) hC.good hC.wc1 hU hu0 hu1 hu2
      hKt row T.a0 T.σ T.Hd T.dl j0 nr (fun i hi => (hC.rows (j0 + i) (by omega)).sem) BL.Lm BL.κC BL.κD BL.Kc
      BL.wv BL.we BL.ckd BL.rows X.order BL.wz BL.zrows BL.FG BL.Sc BL.Gc BL.LB BL.LE BL.LS ch0 nch BL.ws BL.Γs
      BL.wE BL.Geta BL.hLB BL.hLE BL.hLS BL.huv hb tt htt
      (fun i => if h : j0 + i < nI then (T.inv (aS (s x))).mulVec
        ((∑ jj, e jj • fun r => (q r jj : ℝ)) + ε) ⟨j0 + i, h⟩ else 0) (fun i hi => by
        have hj : j0 + i < nI := by omega
        rw [dif_pos hj, error_vecT T q (j0 + i) hj, ← ha]
        exact rowvec_err cb (row (j0 + i)) (T.Hd (j0 + i)) (T.dl (j0 + i)) (chanZc cb) (aS (s x))
          (hC.rows (j0 + i) hj).sem.sorted (hC.rows (j0 + i) hj).sem.ltn (hdl _ hphys _ hj)
          (fun m hm hn => (hC.rows (j0 + i) hj).zero m hm hn _) (extN e) he' (extQ q) hq' (extN ε) hε')
    convert hbe using 1
    ring

end ThomsonCompact.Floor.B
