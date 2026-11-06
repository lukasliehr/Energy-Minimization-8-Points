import ThomsonCompact.Floor.B.TabSpec
import ThomsonCompact.Floor.B.AssembleBlock
import ThomsonCompact.Floor.B.AssembleMetric
import ThomsonCompact.Floor.B.SoundChanOld
import AllS.Units.N_FI.N_certificate.N_corrected_gram
import AllS.Units.N_FI.N_cell_soundness.N_affine_cell
import AllS.Units.N_AI.N_gram_replay.LiteralGramSupport
import AllS.Units.N_AI.N_gram_replay.CorrectedShortMetricSupport
import AllS.Units.N_AI.N_correction_bounds.OutputInsertionSupport
import AllS.Units.N_AI.N_residual_replay.StructuredCenterSupport
import AllS.Units.N_F.N_height_upper

/-!
# One corrected block of a cell, for any degree: the `Active'` fields from the F3b leaves (F3d)

Degree-generic version of the F3c D12 builder: the table enters as a `TabSpec nI` (`inv a j m = H_jm(a)/dl_j(a)`,
output coordinates, anchor), the row denominators are nonzero on physical heights (`hdl`).

* `centre_vecT`, `error_vecT`: rows of `inv a · (centre polynomials)` and of `inv a · (Σ e_j q_j + ε)`;
* `outputInsertion_eq_insMT`: the output insertion of a block is `insM` on its rows;
* `box_of_heightG`: the height leaf puts `aS (s x)` into the box `a0 + σ uf(t)` of the row leaves (anchor `p/2^q`,
  `σ = 2^-g`);
* `CellFactsT` (facts shared by the blocks of a cell), `ActiveT` (the fields of `Active12'`/`Active14'`/
  `Active16'`/`Active18'` for the table `T`) and `BlockLeaves.activeT`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-! ## Channel vectors: direction slots -/

theorem chanZ_getD_dir (cb : CellB) (m tt : ℕ) (htt : tt < cb.nT) :
    (chanZ cb m).getD (cb.N + 1 + tt) 0 = if cb.dirT m = tt then sv (cb.dirQ m) else 0 := by
  unfold chanZ
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp)]
  simp

/-! ## Rows of the correction -/

theorem rowS_eq_sumT {nI : ℕ} (r : RowT) (H : ℕ → ℝ → ℝ) (hsrt : r.msL.Pairwise (· < ·))
    (hn : ∀ m ∈ r.msL, m < nI) (hz : ∀ m < nI, m ∉ r.msL → ∀ a, H m a = 0) (zl : ℕ → List ℤ) (ch : ℕ) (a : ℝ) :
    rowS r H zl ch a = ∑ m : Fin nI, H m a * ((zl m).getD ch 0 : ℝ) := by
  unfold rowS
  rw [Fin.sum_univ_eq_sum_range (fun m => H m a * ((zl m).getD ch 0 : ℝ)) nI,
    sum_msL r hsrt hn _ (fun m hm hnm => by rw [hz m hm hnm a, zero_mul])]

/-- **Centre row**: row `j` of the correction of the centre polynomials. -/
theorem centre_vecT {nI : ℕ} (T : TabSpec nI) (cb : CellB) (hlen : cb.cvc.length = nI) (Sc : ℕ)
    (center : Fin nI → Fin (cb.N + 1) → ℚ)
    (hcen : ∀ r : Fin nI, ∀ k : Fin (cb.N + 1),
      center r k = (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ Sc)
    (r : RowT) (j : ℕ) (hj : j < nI) (hsrt : r.msL.Pairwise (· < ·)) (hn : ∀ m ∈ r.msL, m < nI)
    (hz : ∀ m < nI, m ∉ r.msL → ∀ a, T.Hd j m a = 0) (a x : ℝ) :
    (T.inv a).mulVec (fun r => scalarEval (fun k => (center r k : ℝ)) x) ⟨j, hj⟩ =
      ∑ ch ∈ Finset.range (cb.N + 1), bernsteinWeight cb.N ch x *
        (rowS r (T.Hd j) (chanZc cb) ch a / T.dl j a) / ((cb.D : ℝ) * 2 ^ Sc) := by
  have hc : ∀ m : Fin nI, scalarEval (fun k => (center m k : ℝ)) x =
      (∑ i : Fin (cb.N + 1), (((chanZc cb m).getD i.val 0 : ℤ) : ℝ) / (cb.D : ℝ) *
        bernsteinWeight cb.N i.val x) / 2 ^ Sc := by
    intro m
    rw [← chanZc_bernstein cb m (by rw [hlen]; exact m.isLt) x]
    unfold scalarEval
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hcen m k]
    push_cast
    ring
  simp only [Matrix.mulVec, dotProduct, T.inv_eq, hc]
  simp only [rowS_eq_sumT r (T.Hd j) hsrt hn hz]
  rw [Finset.sum_range (fun ch => bernsteinWeight cb.N ch x *
    ((∑ m : Fin nI, T.Hd j m a * (((chanZc cb m).getD ch 0 : ℤ) : ℝ)) / T.dl j a) / ((cb.D : ℝ) * 2 ^ Sc))]
  simp only [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- extension by zero of a `Fin`-indexed vector -/
noncomputable def extN {t : ℕ} (e : Fin t → ℝ) (tt : ℕ) : ℝ := if h : tt < t then e ⟨tt, h⟩ else 0

/-- extension by zero of the target directions -/
noncomputable def extQ {nI t : ℕ} (q : Fin nI → Fin t → ℚ) (m tt : ℕ) : ℝ :=
  if h : m < nI ∧ tt < t then (q ⟨m, h.1⟩ ⟨tt, h.2⟩ : ℝ) else 0

/-- **Error row**: row `j` of the correction of a structured error vector. -/
theorem error_vecT {nI t : ℕ} (T : TabSpec nI) (q : Fin nI → Fin t → ℚ) (j : ℕ) (hj : j < nI) (a : ℝ)
    (e : Fin t → ℝ) (ε : Fin nI → ℝ) :
    (T.inv a).mulVec ((∑ jj, e jj • fun r => (q r jj : ℝ)) + ε) ⟨j, hj⟩ =
      ∑ m ∈ Finset.range nI, T.Hd j m a / T.dl j a *
        (∑ tt ∈ Finset.range t, extN e tt * extQ q m tt + extN ε m) := by
  simp only [Matrix.mulVec, dotProduct, T.inv_eq, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun m => T.Hd j m a / T.dl j a *
    (∑ tt ∈ Finset.range t, extN e tt * extQ q m tt + extN ε m)) nI]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun tt => extN e tt * extQ q m tt) t]
  simp [extN, extQ]

/-! ## The block insertion -/

theorem outputInsertion_eq_insMT {nI : ℕ} (coords : Fin nI → String × ℕ × ℕ) (name : String) (n j0 nr : ℕ)
    (hnr : j0 + nr ≤ nI) (row : ℕ → RowT)
    (hcoord : ∀ i (h : i < nr), (coords ⟨j0 + i, by omega⟩).2 = ((row (j0 + i)).u, (row (j0 + i)).v))
    (hname : ∀ k : Fin nI, (coords k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (w : Fin nI → ℝ) :
    outputInsertion (n := n) coords name w =
      insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v)
        (fun i => if h : j0 + i < nI then w ⟨j0 + i, h⟩ else 0) := by
  have h := outIns_eq_insM coords name n nr j0 hnr (fun i => (row (j0 + i)).u)
    (fun i => (row (j0 + i)).v) (fun i hi => by
      have h1 := (hname ⟨j0 + i, by omega⟩).2 ⟨by simp, by simp; omega⟩
      have h2 := hcoord i hi
      exact Prod.ext h1 h2) (fun k hk => (hname k).1 hk) w
  exact h

/-! ## The height box -/

/-- the height leaf and the height enclosure put `aS (s x)` into the box of the row leaves, for the anchor
`a0 = p/2^q`, `σ = 2^-g`: `2^g acN = p 2^(256-q+g) ± ucN`, `rN = 2^g rg` -/
theorem box_of_heightG {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (cb : CellB) (acN rg : ℕ)
    (hok : heightOk (mkCtx N 256 B W) A acN rg = true) (p q g : ℕ) (hq : q ≤ 256)
    (hac : (2 : ℤ) ^ g * acN = (p : ℤ) * 2 ^ (256 - q + g) + (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ g * rg) (hr : 0 < cb.rN) :
    ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = (p : ℝ) / 2 ^ q + 1 / 2 ^ g * cb.uf t := by
  intro x hx
  have h1 := heightOk_sound hg hA acN rg hok x hx
  apply box_param cb ((p : ℝ) / 2 ^ q) (1 / 2 ^ g) (aS (s x)) (by positivity) hr
  have hac' : (if cb.ucNeg then -(cb.ucN : ℝ) else cb.ucN) = 2 ^ g * acN - p * 2 ^ (256 - q + g) := by
    have := congrArg (Int.cast (R := ℝ)) hac
    push_cast at this
    split_ifs at this ⊢ <;> linarith
  have hrg' : (cb.rN : ℝ) = 2 ^ g * rg := by exact_mod_cast hrg
  rw [hac', hrg']
  have e2 : (2 : ℝ) ^ (256 - q + g) = 2 ^ 256 * 2 ^ g / 2 ^ q := by
    rw [pow_add, show (256 : ℕ) = (256 - q) + q by omega, pow_add]
    field_simp
    rw [show 256 - q + q - q = 256 - q by omega]
  rw [e2]
  have e1 : (p : ℝ) / 2 ^ q + 1 / 2 ^ g * ((2 ^ g * (acN : ℝ) - p * (2 ^ 256 * 2 ^ g / 2 ^ q)) / 2 ^ 256) =
      (acN : ℝ) / 2 ^ 256 := by
    field_simp
    ring
  have e3 : (1 : ℝ) / 2 ^ g * (2 ^ g * (rg : ℝ) / 2 ^ 256) = (rg : ℝ) / 2 ^ 256 := by field_simp
  rw [e1, e3]
  exact h1

/-! ## The fields of a corrected block -/

/-- the F3b data and the leaf facts of one corrected block (rows `j0 … j0+nr-1` of `row`, block order `n`) -/
structure BlockLeaves (cb : CellB) (row : ℕ → RowT) (j0 nr n : ℕ) where
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
    blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true

/-- the per-cell facts shared by the corrected blocks (table `T`) -/
structure CellFactsT {nI : ℕ} (T : TabSpec nI) (s : ℝ → ℝ) (cb : CellB) (row : ℕ → RowT) : Prop where
  chan : chanOk cb nI = true
  good : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)
  wc1 : 1 ≤ cb.WC
  rows : ∀ j < nI, RowFactsT T j (row j)
  s_nonneg : ∀ x ∈ cellDomain, 0 ≤ s x
  box : ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = T.a0 + T.σ * cb.uf t

/-- the fields of `Active12'` (`Active14'`, `Active16'`, `Active18'`) for the table `T` -/
structure ActiveT {nI : ℕ} (T : TabSpec nI) (s : ℝ → ℝ) (cell : Literals.Cell) (X : Literals.Block) (name : String)
    {N t : ℕ} (H : Fin t → QModel N) (q : Fin nI → Fin t → ℚ)
    (center : Fin nI → Fin (N + 1) → ℚ) (err : Fin nI → ℚ) where
  Z : Matrix (Fin X.order) (Fin X.order) ℝ
  θ : ℝ
  γ : ℝ
  short_metric : QuadraticBound ((Z * literalMetric X cell.metricBits - 1) +
    (Z * literalMetric X cell.metricBits - 1).transpose) θ
  gap : γ < (2 : ℝ) ^ cell.floorExponent * (1 - θ)
  γc : ℚ
  η : ℝ
  total : (γc : ℝ) + η ≤ γ
  centerBound : ∀ x ∈ cellDomain, QuadraticBound
    (Z * outputInsertion T.coords name
      ((T.inv (aS (s x))).mulVec
        (fun r => scalarEval (fun k => (center r k : ℝ)) x)) * Z.transpose) (γc : ℝ)
  error : ∀ x ∈ cellDomain, ∀ (e : Fin t → ℝ) (ε : Fin nI → ℝ),
    (∀ j, |e j| ≤ ((H j).error : ℝ)) → (∀ r, |ε r| ≤ (err r : ℝ)) → QuadraticBound
      (Z * outputInsertion T.coords name
        ((T.inv (aS (s x))).mulVec
          ((∑ j, e j • fun r => (q r j : ℝ)) + ε)) * Z.transpose) η

/-- **The fields of a corrected block** from its leaves and the cell facts (any degree). -/
noncomputable def BlockLeaves.activeT {nI : ℕ} {T : TabSpec nI} {s : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT}
    {j0 nr n : ℕ} (BL : BlockLeaves cb row j0 nr n) (hC : CellFactsT T s cb row)
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
    have hbc := block_centre cb _ (chanZc cb) (chanOk_sound cb nI hC.chan) hC.good hC.wc1 hU hu0 hu1 hu2
      hKt row T.a0 T.σ T.Hd T.dl j0 nr (fun i hi => (hC.rows (j0 + i) (by omega)).sem) BL.Lm BL.κC BL.κD BL.Kc
      BL.wv BL.we BL.ckd BL.rows X.order BL.wz BL.zrows BL.FG BL.Sc BL.Gc BL.LB BL.LE BL.LS BL.ws BL.Γs BL.wE
      BL.Geta BL.hLB BL.hLE BL.hLS BL.huv BL.blocks (bernDen_pos cb.N) tt htt (fun ch => bernsteinWeight cb.N ch x)
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
    obtain ⟨ch0, nch, -, -, hb⟩ := BL.blocks 0 (Nat.zero_le _)
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
    have hbe := block_error cb _ (chanZc cb) (chanOk_sound cb nI hC.chan) hC.good hC.wc1 hU hu0 hu1 hu2
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
