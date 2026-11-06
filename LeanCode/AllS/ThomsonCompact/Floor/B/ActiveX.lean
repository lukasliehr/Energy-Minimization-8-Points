import ThomsonCompact.Floor.B.ActiveQ
import ThomsonCompact.Floor.B.SoundX

/-!
# Two-piece corrected blocks (x-split of a cell, F3f)

A cell `x ∈ [-1,1]` whose single height box is too wide is corrected on its halves `x = (y - 1)/2` and
`x = (y + 1)/2` (`y ∈ [-1,1]`), each with its own F3b data (`CellB`: centre polynomials re-expanded on the half,
`reexpOk`; height box of the half, `pieceHeight`) and its own leaves (`BlockLeavesQ`), the same short inverse `Z`.

* `BlockLeavesQ.centre_at`, `BlockLeavesQ.error_at`: the two quadratic bounds of one piece at one point of the
  piece (the bodies of `BlockLeavesQ.activeT`);
* `BlockLeavesQ.activeTX`: the fields `ActiveT` of the block on the whole cell from its two pieces (`γc`, `η` the
  maxima of the pieces; the gap leaf checks the maxima).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

theorem quadraticBound_mono' {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {γ γ' : ℝ}
    (h : QuadraticBound M γ) (hle : γ ≤ γ') : QuadraticBound M γ' := by
  refine ⟨h.1.trans hle, fun v => (h.2 v).trans ?_⟩
  have hv : 0 ≤ squaredEuclidean v := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  exact mul_le_mul_of_nonneg_right hle hv

/-- **Centre bound of one piece at one point** (the centre polynomials `centerP` of the piece). -/
theorem BlockLeavesQ.centre_at {nI : ℕ} {T : TabSpec nI} {sP : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT}
    {j0 nr n : ℕ} (BL : BlockLeavesQ cb row j0 nr n) (hC : CellFactsT T sP cb row) (name : String)
    (hnr : j0 + nr ≤ nI) (hname : ∀ k : Fin nI, (T.coords k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (centerP : Fin nI → Fin (cb.N + 1) → ℚ)
    (hcen : ∀ r : Fin nI, ∀ k : Fin (cb.N + 1),
      centerP r k = (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ BL.Sc)
    (y : ℝ) (hy : y ∈ cellDomain) :
    QuadraticBound (zMat n BL.wz BL.zrows * outputInsertion (n := n) T.coords name
      ((T.inv (aS (sP y))).mulVec (fun r => scalarEval (fun k => (centerP r k : ℝ)) y)) *
        (zMat n BL.wz BL.zrows).transpose) ((BL.Gc : ℝ) / 2 ^ 256) := by
  obtain ⟨tt, htt, ha⟩ := hC.box y hy
  have hlen := chanOk_len cb nI hC.chan
  obtain ⟨hU, hu0, hu1, hu2, hKt, -⟩ := chanOk_facts cb nI hC.chan
  rw [outputInsertion_eq_insMT T.coords name n j0 nr hnr row
    (fun i hi => (hC.rows (j0 + i) (by omega)).coord _) hname]
  rw [insM_congr_vec n nr _ _ _ (fun i => ∑ ch ∈ Finset.range (cb.N + 1), bernsteinWeight cb.N ch y *
      (rowS (row (j0 + i)) (T.Hd (j0 + i)) (chanZc cb) ch (T.a0 + T.σ * cb.uf tt) /
        T.dl (j0 + i) (T.a0 + T.σ * cb.uf tt)) / ((cb.D : ℝ) * 2 ^ BL.Sc)) (fun i hi => by
      have hj : j0 + i < nI := by omega
      rw [dif_pos hj, centre_vecT T cb hlen BL.Sc centerP hcen (row (j0 + i)) (j0 + i) hj
        (hC.rows (j0 + i) hj).sem.sorted (hC.rows (j0 + i) hj).sem.ltn (hC.rows (j0 + i) hj).zero, ha])]
  have hbw1 : ∑ ch ∈ Finset.range (cb.N + 1), bernsteinWeight cb.N ch y = 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun ch => bernsteinWeight cb.N ch y) (cb.N + 1)]
    exact bernsteinWeight_sum cb.N y
  exact block_centreS cb _ (chanZc cb) (chanOk_sound cb nI hC.chan) hC.good hC.wc1 hU hu0 hu1 hu2
    hKt row T.a0 T.σ T.Hd T.dl j0 nr (fun i hi => (hC.rows (j0 + i) (by omega)).sem) BL.Lm BL.κC BL.κD BL.Kc
    BL.wv BL.we BL.ckd BL.rows n BL.wz BL.zrows BL.FG BL.Sc BL.Gc BL.LB BL.LE BL.LS BL.ws BL.Γs BL.wE
    BL.Geta BL.hLB BL.hLE BL.hLS BL.huv (BL.sound hC.good) (bernDen_pos cb.N) tt htt
    (fun ch => bernsteinWeight cb.N ch y) (fun ch _ => bernsteinWeight_nonneg cb.N ch y hy) hbw1

/-- **Error bound of one piece at one point** (directions `q` with `t = cb.nT` columns). -/
theorem BlockLeavesQ.error_at {nI : ℕ} {T : TabSpec nI} {sP : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT}
    {j0 nr n : ℕ} (BL : BlockLeavesQ cb row j0 nr n) (hC : CellFactsT T sP cb row)
    (hdl : ∀ a, physical a → ∀ j < nI, T.dl j a ≠ 0) (name : String)
    (hnr : j0 + nr ≤ nI) (hname : ∀ k : Fin nI, (T.coords k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    {t : ℕ} (q : Fin nI → Fin t → ℚ) (htq : cb.nT = t)
    (hq : ∀ r : Fin nI, ∀ j : Fin t, q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (y : ℝ) (hy : y ∈ cellDomain) (e : Fin t → ℝ) (ε : Fin nI → ℝ)
    (he : ∀ j : Fin t, |e j| ≤ (cb.herr j : ℝ) / 2 ^ 256) (hε : ∀ r : Fin nI, |ε r| ≤ (cb.Er r : ℝ) / 2 ^ 256) :
    QuadraticBound (zMat n BL.wz BL.zrows * outputInsertion (n := n) T.coords name
      ((T.inv (aS (sP y))).mulVec ((∑ jj, e jj • fun r => (q r jj : ℝ)) + ε)) *
        (zMat n BL.wz BL.zrows).transpose) ((BL.Geta : ℝ) / 2 ^ 256) := by
  obtain ⟨tt, htt, ha⟩ := hC.box y hy
  have hs := hC.s_nonneg y hy
  have hphys := aS_physical (sP y) hs
  have hlen := chanOk_len cb nI hC.chan
  obtain ⟨hU, hu0, hu1, hu2, hKt, -⟩ := chanOk_facts cb nI hC.chan
  obtain ⟨ch0, nch, -, -, hb⟩ := BL.sound hC.good 0 (Nat.zero_le _)
  rw [outputInsertion_eq_insMT T.coords name n j0 nr hnr row
    (fun i hi => (hC.rows (j0 + i) (by omega)).coord _) hname]
  have he' : ∀ tt < cb.nT, |extN e tt| ≤ (cb.herr tt : ℝ) / 2 ^ 256 := by
    intro tt htt
    have htt' : tt < t := htq ▸ htt
    simp only [extN, dif_pos htt']
    exact he ⟨tt, htt'⟩
  have hq' : ∀ m < nI, ∀ tt < cb.nT, extQ q m tt = (((chanZc cb m).getD (cb.N + 1 + tt) 0 : ℤ) : ℝ) / 3 := by
    intro m hm tt htt
    have htt' : tt < t := htq ▸ htt
    simp only [extQ, dif_pos (And.intro hm htt'), hq]
    rw [chanZc_of_lt cb (by rw [hlen]; exact hm), chanZ_getD_dir cb m tt htt]
    split_ifs <;> simp
  have hε' : ∀ m < nI, |extN ε m| ≤ (cb.Er m : ℝ) / 2 ^ 256 := by
    intro m hm
    simp only [extN, dif_pos hm]
    exact hε ⟨m, hm⟩
  have hbe := block_errorS cb _ (chanZc cb) (chanOk_sound cb nI hC.chan) hC.good hC.wc1 hU hu0 hu1 hu2
    hKt row T.a0 T.σ T.Hd T.dl j0 nr (fun i hi => (hC.rows (j0 + i) (by omega)).sem) BL.Lm BL.κC BL.κD BL.Kc
    BL.wv BL.we BL.ckd BL.rows n BL.wz BL.zrows BL.FG BL.Sc BL.Gc BL.LB BL.LE BL.LS ch0 nch BL.ws BL.Γs
    BL.wE BL.Geta BL.hLB BL.hLE BL.hLS BL.huv hb tt htt
    (fun i => if h : j0 + i < nI then (T.inv (aS (sP y))).mulVec
      ((∑ jj, e jj • fun r => (q r jj : ℝ)) + ε) ⟨j0 + i, h⟩ else 0) (fun i hi => by
      have hj : j0 + i < nI := by omega
      rw [dif_pos hj, error_vecT T q (j0 + i) hj, ← ha]
      have h1 := rowvec_err cb (row (j0 + i)) (T.Hd (j0 + i)) (T.dl (j0 + i)) (chanZc cb) (aS (sP y))
        (hC.rows (j0 + i) hj).sem.sorted (hC.rows (j0 + i) hj).sem.ltn (hdl _ hphys _ hj)
        (fun m hm hn => (hC.rows (j0 + i) hj).zero m hm hn _) (extN e) he' (extQ q) hq' (extN ε) hε'
      rw [htq] at h1
      exact h1)
  convert hbe using 1
  ring

/-- the centres of a piece as rationals (scale `2^-Sc` of its block leaves) -/
noncomputable def pieceCenter {nI : ℕ} (cb : CellB) (Sc : ℕ) (r : Fin nI) (k : Fin (cb.N + 1)) : ℚ :=
  (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ Sc

/-- **The fields of a corrected block from its two x-halves** (left `x = (y-1)/2`, right `x = (y+1)/2`; the same
short inverse; `γc`, `η` the maxima of the two pieces). -/
noncomputable def BlockLeavesQ.activeTX {nI : ℕ} {T : TabSpec nI} {s : ℝ → ℝ} {cbL cbR : CellB}
    {row : ℕ → RowT} {j0 nr n : ℕ} (BL : BlockLeavesQ cbL row j0 nr n) (BR : BlockLeavesQ cbR row j0 nr n)
    (hCL : CellFactsT T (fun y => s ((y + sgnH true) / 2)) cbL row)
    (hCR : CellFactsT T (fun y => s ((y + sgnH false) / 2)) cbR row)
    (hdl : ∀ a, physical a → ∀ j < nI, T.dl j a ≠ 0)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin nI → Fin t → ℚ}
    {center : Fin nI → Fin (N + 1) → ℚ} {err : Fin nI → ℚ}
    (hcenL : ∀ r : Fin nI, ∀ y : ℝ, scalarEval (fun k => (center r k : ℝ)) ((y + sgnH true) / 2) =
      scalarEval (fun k => (pieceCenter cbL BL.Sc r k : ℝ)) y)
    (hcenR : ∀ r : Fin nI, ∀ y : ℝ, scalarEval (fun k => (center r k : ℝ)) ((y + sgnH false) / 2) =
      scalarEval (fun k => (pieceCenter cbR BR.Sc r k : ℝ)) y)
    (htL : cbL.nT = t) (htR : cbR.nT = t)
    (hqL : ∀ r : Fin nI, ∀ j : Fin t, q r j = ((if cbL.dirT r = j then sv (cbL.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hqR : ∀ r : Fin nI, ∀ j : Fin t, q r j = ((if cbR.dirT r = j then sv (cbR.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hHL : ∀ j : Fin t, (H j).error ≤ (cbL.herr j : ℚ) / 2 ^ 256)
    (hHR : ∀ j : Fin t, (H j).error ≤ (cbR.herr j : ℚ) / 2 ^ 256)
    (herrL : ∀ r : Fin nI, err r ≤ (cbL.Er r : ℚ) / 2 ^ 256)
    (herrR : ∀ r : Fin nI, err r ≤ (cbR.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ nI)
    (hname : ∀ k : Fin nI, (T.coords k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (hwz : BR.wz = BL.wz) (hzr : BR.zrows = BL.zrows)
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => Nat.max BL.Gc BR.Gc) (Nat.max BL.Geta BR.Geta)
      (Nat.max BL.Gc BR.Gc + Nat.max BL.Geta BR.Geta) claim (32 + mb) E = true) :
    ActiveT T s cell X name H q center err where
  Z := zMat X.order BL.wz BL.zrows
  θ := (claim : ℝ) / 2 ^ (32 + mb)
  γ := ((Nat.max BL.Gc BR.Gc + Nat.max BL.Geta BR.Geta : ℕ) : ℝ) / 2 ^ 256
  short_metric := by
    subst hX
    rw [zMat_eq_zReal X.order BL.wz BL.hwz BL.zrows]
    exact ThomsonCompact.Floor.short_metric_sound X X.order BL.wz cell.metricBits mb BL.zrows ex kl claim rfl hex hkl hθ
  gap := by
    have h := ThomsonCompact.Floor.gap_sound hgap
    rw [hE]
    exact h
  γc := (Nat.max BL.Gc BR.Gc : ℚ) / 2 ^ 256
  η := (Nat.max BL.Geta BR.Geta : ℝ) / 2 ^ 256
  total := by
    push_cast
    rw [add_div]
  centerBound := by
    subst hX
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    rcases le_or_gt x 0 with hxn | hxp
    · -- left half: `y = 2x + 1`
      have hy : 2 * x + 1 ∈ cellDomain := ⟨by linarith, by linarith⟩
      have e1 : (2 * x + 1 + sgnH true) / 2 = x := by simp [sgnH]
      have h := BL.centre_at hCL name hnr hname (pieceCenter cbL BL.Sc) (fun _ _ => rfl) (2 * x + 1) hy
      simp only [e1] at h
      have hc : (fun r => scalarEval (fun k => (center r k : ℝ)) x) =
          fun r => scalarEval (fun k => (pieceCenter cbL BL.Sc r k : ℝ)) (2 * x + 1) := by
        funext r; rw [← hcenL r (2 * x + 1), e1]
      rw [hc]
      refine quadraticBound_mono' h ?_
      push_cast
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_max_left _ _) (by positivity)
    · -- right half: `y = 2x - 1`
      have hy : 2 * x - 1 ∈ cellDomain := ⟨by linarith, by linarith⟩
      have e1 : (2 * x - 1 + sgnH false) / 2 = x := by simp [sgnH]
      have h := BR.centre_at hCR name hnr hname (pieceCenter cbR BR.Sc) (fun _ _ => rfl) (2 * x - 1) hy
      simp only [e1] at h
      rw [hwz, hzr] at h
      have hc : (fun r => scalarEval (fun k => (center r k : ℝ)) x) =
          fun r => scalarEval (fun k => (pieceCenter cbR BR.Sc r k : ℝ)) (2 * x - 1) := by
        funext r; rw [← hcenR r (2 * x - 1), e1]
      rw [hc]
      refine quadraticBound_mono' h ?_
      push_cast
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_max_right _ _) (by positivity)
  error := by
    subst hX
    intro x hx e ε he hε
    obtain ⟨hx0, hx1⟩ := hx
    rcases le_or_gt x 0 with hxn | hxp
    · have hy : 2 * x + 1 ∈ cellDomain := ⟨by linarith, by linarith⟩
      have e1 : (2 * x + 1 + sgnH true) / 2 = x := by simp [sgnH]
      have h := BL.error_at hCL hdl name hnr hname q htL hqL (2 * x + 1) hy e ε
        (fun j => (he j).trans (by have h2 := (Rat.cast_le (K := ℝ)).mpr (hHL j); push_cast at h2; exact h2))
        (fun r => (hε r).trans (by have h2 := (Rat.cast_le (K := ℝ)).mpr (herrL r); push_cast at h2; exact h2))
      simp only [e1] at h
      refine quadraticBound_mono' h ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_max_left _ _) (by positivity)
    · have hy : 2 * x - 1 ∈ cellDomain := ⟨by linarith, by linarith⟩
      have e1 : (2 * x - 1 + sgnH false) / 2 = x := by simp [sgnH]
      have h := BR.error_at hCR hdl name hnr hname q htR hqR (2 * x - 1) hy e ε
        (fun j => (he j).trans (by have h2 := (Rat.cast_le (K := ℝ)).mpr (hHR j); push_cast at h2; exact h2))
        (fun r => (hε r).trans (by have h2 := (Rat.cast_le (K := ℝ)).mpr (herrR r); push_cast at h2; exact h2))
      simp only [e1] at h
      rw [hwz, hzr] at h
      refine quadraticBound_mono' h ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_max_right _ _) (by positivity)

end ThomsonCompact.Floor.B
