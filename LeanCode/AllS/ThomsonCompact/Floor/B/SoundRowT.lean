import ThomsonCompact.Floor.B.SoundRowC

/-!
# Row leaf: the Taylor-model computation (F3b)

`rowTMs_sound`: under `RowSem` (table) and `ChanSem` (channels), the row computation encloses
* the denominator `2^(Fd - FDP) λd(a(t))` (`D`) and its reciprocal (`R`),
* every channel value `2^(F + FDP - Fd - Fp) Σ_m H_m(a(t)) z_m,ch / λd(a(t))` (`V_ch`),
where `a(t) = a0 + σ u(t)` and `u(t)` is the height-box variable of the cell.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open scoped BigOperators

/-! ## Kernel pieces -/

theorem zaccB_spec (W ch : ℕ) : ∀ (Pbs : List ℕ) (Ws : List TM) (P Q : ℕ),
    ((zaccB W ch Pbs Ws P Q).1 : ℤ) - (zaccB W ch Pbs Ws P Q).2 =
      (P : ℤ) - Q + (List.zipWith (fun (Pb : ℕ) (Wk : TM) => sv (pbGet W Pb ch) * (Wk.v : ℤ)) Pbs Ws).sum
  | [], Ws, P, Q => by simp [zaccB]
  | Pb :: Pbs, [], P, Q => by simp [zaccB]
  | Pb :: Pbs, Wk :: Ws, P, Q => by
    have ih := zaccB_spec W ch Pbs Ws (cond (pbGet W Pb ch).1 P (Nat.add P (Nat.mul (pbGet W Pb ch).2 Wk.v)))
      (cond (pbGet W Pb ch).1 (Nat.add Q (Nat.mul (pbGet W Pb ch).2 Wk.v)) Q)
    show ((zaccB W ch Pbs Ws (cond (pbGet W Pb ch).1 P (Nat.add P (Nat.mul (pbGet W Pb ch).2 Wk.v)))
      (cond (pbGet W Pb ch).1 (Nat.add Q (Nat.mul (pbGet W Pb ch).2 Wk.v)) Q)).1 : ℤ) -
      (zaccB W ch Pbs Ws (cond (pbGet W Pb ch).1 P (Nat.add P (Nat.mul (pbGet W Pb ch).2 Wk.v)))
      (cond (pbGet W Pb ch).1 (Nat.add Q (Nat.mul (pbGet W Pb ch).2 Wk.v)) Q)).2 = _
    rw [ih, List.zipWith_cons_cons, List.sum_cons]
    generalize pbGet W Pb ch = g
    rcases g with ⟨b, n⟩
    cases b <;> simp [sv] <;> ring

theorem zacc_ok : ∀ (terms : List (Bool × ℕ × TM)) (P Q ns ne : ℕ) (ok : Bool),
    (zacc terms P Q ns ne ok).2.2.2.2 = true → ok = true ∧ ∀ x ∈ terms, x.2.2.ok = true
  | [], _, _, _, _, _, h => ⟨h, by simp⟩
  | x :: terms, P, Q, ns, ne, ok, h => by
    have := zacc_ok terms _ _ _ _ (and ok x.2.2.ok) h
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact this.1.2
    · exact this.2 y hy

theorem zfin_ok {c : Ctx} {F : ℕ} {r : ℕ × ℕ × ℕ × ℕ × Bool} (h : (zfin c F r).ok = true) : r.2.2.2.2 = true := by
  have h' : (r.2.2.2.2 && Nat.blt r.2.2.1 (Nat.pow 2 (Nat.mul 2 c.B)) && Nat.blt (zfin c F r).s c.twoB) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1.1

theorem zcomb_ok_terms {c : Ctx} {F : ℕ} {terms : List (Bool × ℕ × TM)} (h : (zcomb c F terms).ok = true) :
    ∀ x ∈ terms, x.2.2.ok = true :=
  (zacc_ok terms 0 0 0 0 true (zfin_ok h)).2

theorem zipT_eq : ∀ (gs : List (Bool × ℕ)) (Us : List TM), gs.length ≤ Us.length →
    zipT gs Us = (List.range gs.length).map fun k =>
      ((gs.getD k (false, 0)).1, (gs.getD k (false, 0)).2, Us.getD k zeroTM)
  | [], Us, _ => by simp [zipT]
  | g :: gs, [], h => by simp at h
  | g :: gs, U :: Us, h => by
    show (g.1, g.2, U) :: zipT gs Us = _
    rw [zipT_eq gs Us (by simpa using h), List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def]

theorem zipWith_range {α β γ : Type*} (f : α → β → γ) (d1 : α) (d2 : β) : ∀ (l1 : List α) (l2 : List β),
    l1.length = l2.length →
    List.zipWith f l1 l2 = (List.range l1.length).map fun k => f (l1.getD k d1) (l2.getD k d2)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l1, y :: l2, h => by
    rw [List.zipWith_cons_cons, zipWith_range f d1 d2 l1 l2 (by simpa using h), List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def]

theorem foldl_max_ge {α : Type*} (g : α → ℕ) : ∀ (l : List α) (m : ℕ),
    m ≤ l.foldl (fun m y => Nat.max m (g y)) m ∧ ∀ x ∈ l, g x ≤ l.foldl (fun m y => Nat.max m (g y)) m
  | [], m => ⟨le_rfl, by simp⟩
  | y :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_max_ge g l (Nat.max m (g y))
    refine ⟨le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

theorem sv_cast (x : Bool × ℕ) : ((sv x : ℤ) : ℝ) = if x.1 then -(x.2 : ℝ) else x.2 := by
  unfold sv; cases x.1 <;> simp

theorem sv_pbGet {W : ℕ} (hW : 1 ≤ W) (z : List ℤ) (hb : ∀ x ∈ z, |x| < 2 ^ (W - 1)) (i : ℕ) (hi : i < z.length) :
    sv (pbGet W (Nat.ofDigits (2 ^ W) (z.map fun x => (x + 2 ^ (W - 1)).toNat)) i) = z.getD i 0 := by
  rw [pbGet_ofDigits hW z hb i hi, getD_of_lt _ _ hi]
  unfold sv
  by_cases h : z[i] < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

/-! ## Checkpoints and shifted comparisons -/

variable {N S B W : ℕ}

theorem ckOk_sound (hg : Good N S B W) {V Vt : TM} {f : ℝ → ℝ} (hV : Encl (mkCtx N S B W) V f)
    (hVt : RepOK (mkCtx N S B W) Vt) (hok : ckOk (mkCtx N S B W) V Vt = true) : Encl (mkCtx N S B W) Vt f := by
  have hok' := hok
  simp only [ckOk, Bool.and_eq_true, Nat.ble_eq] at hok'
  obtain ⟨⟨_, hDok⟩, hle⟩ := hok'
  obtain ⟨csV, alV, hRV, hfV⟩ := hV
  obtain ⟨csT, alT, hRT⟩ := hVt
  have h1 := Encl.self (polyOnly_rep hRV)
  have h2 := neg_sound (Encl.self (polyOnly_rep hRT))
  have h3 := add_sound h1 h2 hDok
  have h4 := rangeX_sound hg h3
  refine ⟨csT, alT, hRT, fun t ht => ?_⟩
  have e1 := hfV t ht
  have e2 := h4 t ht
  simp only [mk_S] at e1 e2 ⊢
  have hle' : ((rangeX (mkCtx N S B W) (add (mkCtx N S B W) (polyOnly V) (neg (mkCtx N S B W) (polyOnly Vt))) : ℕ) : ℝ)
      + (V.e : ℝ) ≤ (Vt.e : ℝ) := by exact_mod_cast hle
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  have key : |f t - evalZ csT t / 2 ^ S| ≤ |f t - evalZ csV t / 2 ^ S| +
      |evalZ csV t / 2 ^ S + -(evalZ csT t / 2 ^ S)| := by
    have := abs_add_le (f t - evalZ csV t / 2 ^ S) (evalZ csV t / 2 ^ S + -(evalZ csT t / 2 ^ S))
    have e : f t - evalZ csV t / 2 ^ S + (evalZ csV t / 2 ^ S + -(evalZ csT t / 2 ^ S)) = f t - evalZ csT t / 2 ^ S := by
      ring
    rwa [e] at this
  calc |f t - evalZ csT t / 2 ^ S| ≤ _ := key
    _ ≤ (V.e : ℝ) / 2 ^ S + (rangeX (mkCtx N S B W) (add (mkCtx N S B W) (polyOnly V)
          (neg (mkCtx N S B W) (polyOnly Vt))) : ℝ) / 2 ^ S := add_le_add e1 e2
    _ ≤ (Vt.e : ℝ) / 2 ^ S := by rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hS.le

theorem leShift_real {x y : ℕ} {e : ℤ} (h : leShift x y e = true) : (x : ℝ) * (2 : ℝ) ^ e ≤ y := by
  simp only [leShift, Nat.ble_eq] at h
  have h2 : x * 2 ^ e.toNat ≤ y * 2 ^ (-e).toNat := by rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]; exact h
  have h' : ((x * 2 ^ e.toNat : ℕ) : ℝ) ≤ ((y * 2 ^ (-e).toNat : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h'
  have he : e = (e.toNat : ℤ) - ((-e).toNat : ℤ) := by omega
  rw [he, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, mul_div_assoc', div_le_iff₀ (by positivity)]
  exact h'

/-! ## Semantic functions of a row -/

/-- the height-box variable `u(t)` of the cell -/
noncomputable def CellB.uf (cb : CellB) (t : ℝ) : ℝ :=
  ((if cb.ucNeg then -(cb.ucN : ℝ) else cb.ucN) + cb.rN * t) / 2 ^ 256

/-- `Σ_idx H_m(a) z_m,ch` over the row's entries -/
noncomputable def rowS (r : RowT) (H : ℕ → ℝ → ℝ) (zl : ℕ → List ℤ) (ch : ℕ) (a : ℝ) : ℝ :=
  ∑ idx ∈ Finset.range r.nms, H (r.mAt idx) a * ((zl (r.mAt idx)).getD ch 0 : ℝ)

theorem uf_abs (cb : CellB) (hu : 2 * (cb.ucN + cb.rN) ≤ 2 ^ 256) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |cb.uf t| ≤ 1 / 2 := by
  unfold CellB.uf
  have hu' : (2 : ℝ) * ((cb.ucN : ℝ) + cb.rN) ≤ 2 ^ 256 := by exact_mod_cast hu
  have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have h1 : |(if cb.ucNeg then -(cb.ucN : ℝ) else cb.ucN) + cb.rN * t| ≤ cb.ucN + cb.rN := by
    calc _ ≤ |(if cb.ucNeg then -(cb.ucN : ℝ) else cb.ucN)| + |(cb.rN : ℝ) * t| := abs_add_le _ _
      _ ≤ cb.ucN + cb.rN := by
        apply add_le_add
        · cases cb.ucNeg <;> simp
        · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_of_le_one_right (Nat.cast_nonneg _) hta
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 256), div_le_iff₀ (by positivity)]
  linarith

theorem msL_sum {M : Type*} [AddCommMonoid M] (r : RowT) (f : ℕ → M) :
    (r.msL.map f).sum = ∑ idx ∈ Finset.range r.nms, f (r.mAt idx) := by
  unfold RowT.mAt RowT.msL
  rw [List.map_map, list_sum_range']
  apply Finset.sum_congr rfl
  intro idx hidx
  rw [getD_of_lt _ _ (by simpa using hidx)]
  simp

theorem getD_map_natAbs (l : List ℤ) (i : ℕ) : (l.map Int.natAbs).getD i 0 = (l.getD i 0).natAbs := by
  by_cases h : i < l.length
  · rw [getD_of_lt _ _ (by simpa using h), getD_of_lt _ _ h, List.getElem_map]
  · rw [getD_of_ge _ _ (by simp; omega), getD_of_ge _ _ (by omega)]; rfl

theorem pvec_getD (r : RowT) (zl : ℕ → List ℤ) (n k i : ℕ) (hi : i < n) : (pvec r zl n k).getD i 0 = pval r zl k i := by
  rw [getD_of_lt _ _ (by simp [pvec, hi])]; simp [pvec]

theorem zip_range_map {α β : Type*} (f : ℕ → α) (g : ℕ → β) (n : ℕ) :
    ((List.range n).map f).zip ((List.range n).map g) = (List.range n).map fun i => (f i, g i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-! ## The components of `rowTMs` -/

noncomputable def rDt (cb : CellB) (Us : List TM) (r : RowT) : TM :=
  widen (zcomb cb.cT FDP (zipT r.dhL Us)) (Packed.cdiv (Nat.succ FDP) (Nat.shiftLeft r.Ld 256))

noncomputable def rRr (cb : CellB) (Us : List TM) (r : RowT) : TM := invN cb.cT 8 0 (rDt cb Us r)

noncomputable def rPb (cb : CellB) (r : RowT) (cvs : List ℕ) : List ℕ :=
  r.t.map fun t => Nat.land (Nat.add (contractK r.w cb.KC cvs (lsum cvs) t) (pvBias cb.WC cb.nC)) (mask cb.KC)

noncomputable def rWs (cb : CellB) (Us : List TM) (r : RowT) : List TM := (Us.take r.L).map fun U => mul cb.cT U (rRr cb Us r)

noncomputable def rVacc (cb : CellB) (Us : List TM) (r : RowT) (cvs : List ℕ) (ch : ℕ) : ℕ × ℕ × ℕ × ℕ × Bool :=
  ((zaccB cb.WC ch (rPb cb r cvs) (rWs cb Us r) 0 0).1, (zaccB cb.WC ch (rPb cb r cvs) (rWs cb Us r) 0 0).2,
    Nat.mul (slot cb.WC (lsum ((rPb cb r cvs).map (pbAbs cb.WC cb.nC))) ch)
      ((rWs cb Us r).foldl (fun m W => Nat.max m W.s) 0),
    Nat.mul (slot cb.WC (lsum ((rPb cb r cvs).map (pbAbs cb.WC cb.nC))) ch)
      ((rWs cb Us r).foldl (fun m W => Nat.max m W.e) 0),
    (rWs cb Us r).all TM.ok)

noncomputable def rVdelta (cb : CellB) (Us : List TM) (r : RowT) (cvs : List ℕ) (Fp ch : ℕ) : ℕ :=
  Packed.cdiv 256 (Nat.mul (Packed.cdiv (Nat.succ Fp)
    (Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256))
    (rangeX cb.cT (rRr cb Us r)))

noncomputable def rV (cb : CellB) (Us : List TM) (r : RowT) (cvs : List ℕ) (Fp ch : ℕ) : TM :=
  widen (zfin cb.cT Fp (rVacc cb Us r cvs ch)) (rVdelta cb Us r cvs Fp ch)

theorem rowTMs_eq (cb : CellB) (Us : List TM) (r : RowT) (cvs : List ℕ) (FpC FpD : ℕ) :
    rowTMs cb Us r cvs FpC FpD = (rDt cb Us r, rRr cb Us r,
      (List.range cb.nC).map fun ch => rV cb Us r cvs (cond (Nat.ble ch cb.N) FpC FpD) ch) := rfl

/-! ## Denominator and reciprocal -/

theorem rowDR_sound (cb : CellB) {nI : ℕ} (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2))
    (r : RowT) (a0 σ : ℝ) (H : ℕ → ℝ → ℝ) (dl : ℝ → ℝ) (hr : RowSem nI r a0 σ (1 / 2) H dl)
    (Us : List TM) (hUs : ∀ k < Us.length, (Us.getD k zeroTM).ok = true →
      Encl cb.cT (Us.getD k zeroTM) (fun t => cb.uf t ^ k))
    (hu : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |cb.uf t| ≤ 1 / 2)
    (hLd : r.Ld ≤ Us.length) (hFDP : FDP + 1 ≤ 2 * cb.BT + 2)
    (hDok : (rDt cb Us r).ok = true) (hRok : (rRr cb Us r).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, dl (a0 + σ * cb.uf t) ≠ 0) ∧
    Encl cb.cT (rRr cb Us r) (fun t => ((2 : ℝ) ^ (r.Fd - (FDP : ℤ)) * dl (a0 + σ * cb.uf t))⁻¹) := by
  have hcT : cb.cT = mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2) := rfl
  have hdl : r.dhL.length = r.Ld := by simp [RowT.dhL]
  set LD : List (Bool × ℕ × TM × (ℝ → ℝ)) := (List.range r.Ld).map fun k =>
    ((r.dhL.getD k (false, 0)).1, (r.dhL.getD k (false, 0)).2, Us.getD k zeroTM, fun t => cb.uf t ^ k) with hLD
  have hz : zipT r.dhL Us = LD.map fun x => (x.1, x.2.1, x.2.2.1) := by
    rw [zipT_eq r.dhL Us (by omega), hdl, hLD, List.map_map]; rfl
  have hzok : (zcomb cb.cT FDP (zipT r.dhL Us)).ok = true := hDok
  have hterms := zcomb_ok_terms hzok
  have hLenc : ∀ x ∈ LD, Encl (mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2)) x.2.2.1 x.2.2.2 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range.mp hk
    have hok : (Us.getD k zeroTM).ok = true := by
      apply hterms ((r.dhL.getD k (false, 0)).1, (r.dhL.getD k (false, 0)).2, Us.getD k zeroTM)
      rw [hz]; exact List.mem_map.mpr ⟨_, hx, rfl⟩
    exact hUs k (by omega) hok
  rw [hz, hcT] at hzok
  have hZ := zcomb_sound hg hFDP LD hLenc hzok
  have hsum : ∀ t, (LD.map fun x => (if x.1 then -(x.2.1 : ℝ) else x.2.1) * x.2.2.2 t).sum =
      evalZ r.dcoef (cb.uf t) := by
    intro t
    rw [hLD, List.map_map, list_sum_range']
    unfold RowT.dcoef
    rw [show r.dhL.map sv = (List.range r.Ld).map (fun k => sv (r.dhL.getD k (false, 0))) from ?_]
    · rw [evalZ_range]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Function.comp_apply, sv_cast]
    · apply List.ext_getElem (by simp [hdl])
      intro i h1 h2
      rw [List.getElem_map, List.getElem_map, List.getElem_range,
        getD_of_lt r.dhL (false, 0) (by simpa [hdl] using h2)]
  have hD : Encl (mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2)) (rDt cb Us r)
      (fun t => (2 : ℝ) ^ (r.Fd - (FDP : ℤ)) * dl (a0 + σ * cb.uf t)) := by
    unfold rDt
    rw [hz, hcT]
    apply widen_sound _ hZ
    intro t ht
    show |(2 : ℝ) ^ (r.Fd - (FDP : ℤ)) * dl (a0 + σ * cb.uf t) -
        (LD.map fun x => (if x.1 then -(x.2.1 : ℝ) else x.2.1) * x.2.2.2 t).sum / 2 ^ FDP| ≤
      ((Packed.cdiv (Nat.succ FDP) (Nat.shiftLeft r.Ld 256) : ℕ) : ℝ) / 2 ^ 256
    rw [hsum t]
    have h1 := hr.den (cb.uf t) (le_trans (hu t ht) (by norm_num))
    have hsh : Nat.shiftLeft r.Ld 256 = r.Ld * 2 ^ 256 := Nat.shiftLeft_eq r.Ld 256
    have h2 : (r.Ld : ℝ) * 2 ^ 256 / 2 ^ (FDP + 1) ≤
        ((Packed.cdiv (Nat.succ FDP) (Nat.shiftLeft r.Ld 256) : ℕ) : ℝ) := by
      have h := le_cdiv (Nat.succ FDP) (Nat.shiftLeft r.Ld 256)
      have e : ((Nat.shiftLeft r.Ld 256 : ℕ) : ℝ) = (r.Ld : ℝ) * 2 ^ 256 := by
        rw [hsh, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [e] at h
      exact h
    have hz2 : (2 : ℝ) ^ (r.Fd - (FDP : ℤ)) = 2 ^ r.Fd / 2 ^ FDP := by
      rw [zpow_sub₀ (by norm_num), zpow_natCast]
    rw [hz2]
    have e1 : (2 : ℝ) ^ r.Fd / 2 ^ FDP * dl (a0 + σ * cb.uf t) - evalZ r.dcoef (cb.uf t) / 2 ^ FDP =
        ((2 : ℝ) ^ r.Fd * dl (a0 + σ * cb.uf t) - evalZ r.dcoef (cb.uf t)) / 2 ^ FDP := by ring
    rw [e1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ FDP)]
    calc |(2 : ℝ) ^ r.Fd * dl (a0 + σ * cb.uf t) - evalZ r.dcoef (cb.uf t)| / 2 ^ FDP
        ≤ ((r.Ld : ℝ) / 2) / 2 ^ FDP := div_le_div_of_nonneg_right h1 (by positivity)
      _ = ((r.Ld : ℝ) * 2 ^ 256 / 2 ^ (FDP + 1)) / 2 ^ 256 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right h2 (by positivity)
  have hR := invN_sound hg hD 8 0 hRok
  exact ⟨fun t ht h0 => hR.1 t ht (by rw [h0, mul_zero]), hR.2⟩

/-! ## The channel values -/

theorem pval_natAbs (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl) (r : RowT)
    (hw : 1 ≤ r.w) (k ch : ℕ) : (pval r zl k ch).natAbs ≤ r.nms * 2 ^ (r.w - 1) * cb.cmax := by
  have := pval_abs cb cvA zl hch r hw k ch
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

theorem rowV_sound (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hWC : 1 ≤ cb.WC)
    (r : RowT) (a0 σ : ℝ) (H : ℕ → ℝ → ℝ) (dl : ℝ → ℝ) (hr : RowSem nI r a0 σ (1 / 2) H dl)
    (Us : List TM) (hUs : ∀ k < Us.length, (Us.getD k zeroTM).ok = true →
      Encl cb.cT (Us.getD k zeroTM) (fun t => cb.uf t ^ k))
    (hu : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |cb.uf t| ≤ 1 / 2)
    (hL : r.L ≤ Us.length)
    (hb : r.L * r.nms * 2 ^ (r.w - 1) * cb.cmax < 2 ^ (cb.WC - 1))
    (hdl0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, dl (a0 + σ * cb.uf t) ≠ 0)
    (hR : Encl cb.cT (rRr cb Us r) (fun t => ((2 : ℝ) ^ (r.Fd - (FDP : ℤ)) * dl (a0 + σ * cb.uf t))⁻¹))
    (Fp ch : ℕ) (hF : Fp + 1 ≤ 2 * cb.BT + 2) (hch' : ch < cb.nC)
    (hok : (rV cb Us r (r.msL.map fun m => cvA.getD m 0) Fp ch).ok = true) :
    Encl cb.cT (rV cb Us r (r.msL.map fun m => cvA.getD m 0) Fp ch)
      (fun t => (2 : ℝ) ^ (r.F + (FDP : ℤ) - r.Fd - (Fp : ℤ)) * rowS r H zl ch (a0 + σ * cb.uf t) /
        dl (a0 + σ * cb.uf t)) := by
  have hcT : cb.cT = mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2) := rfl
  set cvs := r.msL.map fun m => cvA.getD m 0 with hcvs
  have hw := hr.wpos
  have hL1 := hr.Lpos
  have hlen := hr.len
  have hms := hr.ltn
  have hb1 : r.nms * 2 ^ (r.w - 1) * cb.cmax < 2 ^ (cb.WC - 1) := by
    refine lt_of_le_of_lt ?_ hb
    calc r.nms * 2 ^ (r.w - 1) * cb.cmax = 1 * (r.nms * 2 ^ (r.w - 1) * cb.cmax) := by ring
      _ ≤ r.L * (r.nms * 2 ^ (r.w - 1) * cb.cmax) := Nat.mul_le_mul_right _ hL1
      _ = r.L * r.nms * 2 ^ (r.w - 1) * cb.cmax := by ring
  have hWlt : 2 ^ (cb.WC - 1) < 2 ^ cb.WC := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- contraction values
  have hpvz : ∀ k, ∀ x ∈ pvec r zl cb.nC k, |x| < 2 ^ (cb.WC - 1) := by
    intro k x hx
    obtain ⟨ch', _, rfl⟩ := List.mem_map.mp hx
    have := pval_abs cb cvA zl hch r hw k ch'
    have hb' : ((r.nms * 2 ^ (r.w - 1) * cb.cmax : ℕ) : ℤ) < 2 ^ (cb.WC - 1) := by exact_mod_cast hb1
    push_cast at hb'
    linarith
  have hPbl : (rPb cb r cvs).length = r.L := by simp [rPb, hr.tlen]
  have hPb : ∀ k < r.L, (rPb cb r cvs).getD k 0 =
      Nat.ofDigits (2 ^ cb.WC) ((pvec r zl cb.nC k).map fun x => (x + 2 ^ (cb.WC - 1)).toNat) := by
    intro k hk
    rw [getD_of_lt _ _ (by rw [hPbl]; exact hk)]
    simp only [rPb, List.getElem_map]
    rw [← getD_of_lt r.t 0 (by rw [hr.tlen]; exact hk)]
    exact pb_contract cb cvA zl hch r hlen hms hw hWC k hb1
  -- packed magnitudes of the contraction
  have hPA : lsum ((rPb cb r cvs).map (pbAbs cb.WC cb.nC)) =
      lsum (((List.range r.L).map fun k => (pvec r zl cb.nC k).map Int.natAbs).map (Nat.ofDigits (2 ^ cb.WC))) := by
    congr 1
    apply List.ext_getElem (by simp [hPbl])
    intro k h1 h2
    have hk : k < r.L := by simpa [hPbl] using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_map, List.getElem_range]
    rw [← getD_of_lt (rPb cb r cvs) 0 (by rw [hPbl]; exact hk), hPb k hk]
    exact pbAbs_ofDigits hWC _ (by simp [pvec]) (hpvz k)
  have hsumpv : ∀ i < cb.nC, ((((List.range r.L).map fun k => (pvec r zl cb.nC k).map Int.natAbs).map
      fun l => l.getD i 0).sum) = ∑ k ∈ Finset.range r.L, (pval r zl k i).natAbs := by
    intro i hi
    rw [List.map_map, list_sum_range']
    apply Finset.sum_congr rfl; intro k _
    simp only [Function.comp_apply]
    rw [getD_map_natAbs, pvec_getD r zl _ k i hi]
  have hpvbound : ∀ i, ∑ k ∈ Finset.range r.L, (pval r zl k i).natAbs ≤ r.L * r.nms * 2 ^ (r.w - 1) * cb.cmax := by
    intro i
    calc ∑ k ∈ Finset.range r.L, (pval r zl k i).natAbs ≤ ∑ _k ∈ Finset.range r.L, r.nms * 2 ^ (r.w - 1) * cb.cmax :=
          Finset.sum_le_sum (fun k _ => pval_natAbs cb cvA zl hch r hw k i)
      _ = r.L * r.nms * 2 ^ (r.w - 1) * cb.cmax := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  have hslotPA : slot cb.WC (lsum ((rPb cb r cvs).map (pbAbs cb.WC cb.nC))) ch =
      ∑ k ∈ Finset.range r.L, (pval r zl k ch).natAbs := by
    rw [hPA, slot_lsum (by omega) cb.nC _ (by
        intro l hl; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hl; simp [pvec])
      (fun i hi => by rw [hsumpv i hi]; exact lt_of_le_of_lt (hpvbound i) (lt_trans hb hWlt)) ch hch',
      hsumpv ch hch']
  -- packed magnitudes of the channel vectors
  have hzb : ∀ m ∈ r.msL, ∀ x ∈ zl m, |x| < 2 ^ (cb.WC - 1) := by
    intro m hm x hx
    have h1 := hch.bnd m x hx
    have hn : 1 ≤ r.nms := by rw [← hlen]; exact List.length_pos_of_mem hm
    have h2 : cb.cmax ≤ r.nms * 2 ^ (r.w - 1) * cb.cmax := by
      calc cb.cmax = 1 * 1 * cb.cmax := by ring
        _ ≤ r.nms * 2 ^ (r.w - 1) * cb.cmax :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul hn (Nat.one_le_two_pow))
    have : (cb.cmax : ℤ) < 2 ^ (cb.WC - 1) := by exact_mod_cast (lt_of_le_of_lt h2 hb1)
    linarith
  have hAs : lsum (cvs.map (pvAbs cb.WC cb.nC)) =
      lsum ((r.msL.map fun m => (zl m).map Int.natAbs).map (Nat.ofDigits (2 ^ cb.WC))) := by
    rw [hcvs, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro m hm
    simp only [Function.comp_apply]
    show pbAbs cb.WC cb.nC (Nat.land (Nat.add (cvA.getD m 0) (pvBias cb.WC cb.nC)) (mask (Nat.mul cb.WC cb.nC))) = _
    rw [pb_digits hWC (zl m) (hch.len m) (hzb m hm) _
      (hch.mod m (by have := hms m hm; have := hch.cvl; omega))]
    exact pbAbs_ofDigits hWC _ (hch.len m) (hzb m hm)
  have hsumz : ∀ i, (((r.msL.map fun m => (zl m).map Int.natAbs).map fun l => l.getD i 0).sum) =
      ∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD i 0).natAbs := by
    intro i
    rw [List.map_map, msL_sum]
    apply Finset.sum_congr rfl; intro idx _
    simp only [Function.comp_apply]
    rw [getD_map_natAbs]
  have hslotAs : slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch =
      ∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0).natAbs := by
    rw [hAs, slot_lsum (by omega) cb.nC _ (by
        intro l hl; obtain ⟨m, _, rfl⟩ := List.mem_map.mp hl; simp [hch.len m])
      (fun i hi => by
        rw [hsumz i]
        calc ∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD i 0).natAbs
            ≤ ∑ _idx ∈ Finset.range r.nms, cb.cmax := Finset.sum_le_sum (fun idx _ => by
              have := zl_abs cb cvA zl hch (r.mAt idx) i
              rw [Int.abs_eq_natAbs] at this; exact_mod_cast this)
          _ = r.nms * cb.cmax := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          _ ≤ r.nms * 2 ^ (r.w - 1) * cb.cmax := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
          _ < 2 ^ cb.WC := lt_trans hb1 hWlt) ch hch', hsumz ch]
  -- the products W_k = U^k R
  have hWsl : (rWs cb Us r).length = r.L := by simp [rWs]; omega
  have hWs : ∀ k < r.L, (rWs cb Us r).getD k zeroTM = mul cb.cT (Us.getD k zeroTM) (rRr cb Us r) := by
    intro k hk
    rw [getD_of_lt _ _ (by rw [hWsl]; exact hk)]
    simp [rWs, List.getElem?_eq_getElem (show k < Us.length by omega)]
  have hokW : (rWs cb Us r).all TM.ok = true := zfin_ok hok
  have hokWk : ∀ k < r.L, ((rWs cb Us r).getD k zeroTM).ok = true := by
    intro k hk
    rw [List.all_eq_true] at hokW
    rw [getD_of_lt _ _ (by rw [hWsl]; exact hk)]
    exact hokW _ (List.getElem_mem _)
  set LV : List (ℤ × TM × (ℝ → ℝ)) := (List.range r.L).map fun k => (pval r zl k ch, (rWs cb Us r).getD k zeroTM,
    fun t => cb.uf t ^ k * ((2 : ℝ) ^ (r.Fd - (FDP : ℤ)) * dl (a0 + σ * cb.uf t))⁻¹) with hLV
  have hLVe : ∀ x ∈ LV, Encl (mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2)) x.2.1 x.2.2 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range.mp hk
    have hok1 := hokWk k hk'
    rw [hWs k hk'] at hok1 ⊢
    exact mul_sound hg (hUs k (by omega) (mul_ok hok1).1) hR hok1
  have hPQ : ((rVacc cb Us r cvs ch).1 : ℤ) - (rVacc cb Us r cvs ch).2.1 = (LV.map fun x => x.1 * (x.2.1.v : ℤ)).sum := by
    show ((zaccB cb.WC ch (rPb cb r cvs) (rWs cb Us r) 0 0).1 : ℤ) - (zaccB cb.WC ch (rPb cb r cvs) (rWs cb Us r) 0 0).2 = _
    rw [zaccB_spec, zipWith_range _ 0 zeroTM _ _ (by rw [hPbl, hWsl]), hPbl, hLV, List.map_map]
    simp only [Nat.cast_zero, sub_self, zero_add]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    simp only [Function.comp_apply]
    rw [hPb k hk', sv_pbGet hWC _ (hpvz k) ch (by simp [pvec, hch']), pvec_getD r zl _ k ch hch']
  have hmaxs := foldl_max_ge TM.s (rWs cb Us r) 0
  have hmaxe := foldl_max_ge TM.e (rWs cb Us r) 0
  have hns : (LV.map fun x => x.1.natAbs * x.2.1.s).sum ≤ (rVacc cb Us r cvs ch).2.2.1 := by
    show _ ≤ Nat.mul (slot cb.WC (lsum ((rPb cb r cvs).map (pbAbs cb.WC cb.nC))) ch)
      ((rWs cb Us r).foldl (fun m W => Nat.max m W.s) 0)
    rw [hslotPA, hLV, List.map_map, list_sum_range']
    show _ ≤ (∑ k ∈ Finset.range r.L, (pval r zl k ch).natAbs) * ((rWs cb Us r).foldl (fun m W => Nat.max m W.s) 0)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    simp only [Function.comp_apply]
    apply Nat.mul_le_mul_left
    have := hmaxs.2 ((rWs cb Us r).getD k zeroTM)
      (by rw [getD_of_lt _ _ (by rw [hWsl]; exact List.mem_range.mp hk)]; exact List.getElem_mem _)
    exact this
  have hne : (LV.map fun x => x.1.natAbs * x.2.1.e).sum ≤ (rVacc cb Us r cvs ch).2.2.2.1 := by
    show _ ≤ Nat.mul (slot cb.WC (lsum ((rPb cb r cvs).map (pbAbs cb.WC cb.nC))) ch)
      ((rWs cb Us r).foldl (fun m W => Nat.max m W.e) 0)
    rw [hslotPA, hLV, List.map_map, list_sum_range']
    show _ ≤ (∑ k ∈ Finset.range r.L, (pval r zl k ch).natAbs) * ((rWs cb Us r).foldl (fun m W => Nat.max m W.e) 0)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k hk
    simp only [Function.comp_apply]
    apply Nat.mul_le_mul_left
    have := hmaxe.2 ((rWs cb Us r).getD k zeroTM)
      (by rw [getD_of_lt _ _ (by rw [hWsl]; exact List.mem_range.mp hk)]; exact List.getElem_mem _)
    exact this
  have hZ := zfin_sound hg hF LV hLVe (rVacc cb Us r cvs ch).1 (rVacc cb Us r cvs ch).2.1
    (rVacc cb Us r cvs ch).2.2.1 (rVacc cb Us r cvs ch).2.2.2.1 (rVacc cb Us r cvs ch).2.2.2.2 hPQ hns hne hok
  -- widening by the table rounding of the entries
  have hRr := rangeX_sound hg hR
  apply widen_sound (c := mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2)) _ hZ
  intro t ht
  set u := cb.uf t with hu_def
  set dv := dl (a0 + σ * u) with hdv
  have hdv0 : dv ≠ 0 := hdl0 t ht
  set ρ := ((2 : ℝ) ^ (r.Fd - (FDP : ℤ)) * dv)⁻¹ with hρ
  have hρb : |ρ| ≤ (rangeX cb.cT (rRr cb Us r) : ℝ) / 2 ^ 256 := hRr t ht
  have hf : (LV.map fun x => (x.1 : ℝ) * x.2.2 t).sum / 2 ^ Fp =
      ρ * (∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) * evalZ (r.ecoef idx) u) / 2 ^ Fp := by
    rw [hLV, List.map_map, list_sum_range', ← pval_eval, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro k _
    simp only [Function.comp_apply]
    ring
  have hg' : (2 : ℝ) ^ (r.F + (FDP : ℤ) - r.Fd - (Fp : ℤ)) * rowS r H zl ch (a0 + σ * u) / dv =
      ρ * (∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) * (2 ^ r.F * H (r.mAt idx) (a0 + σ * u))) /
        2 ^ Fp := by
    have e : (2 : ℝ) ^ (r.F + (FDP : ℤ) - r.Fd - (Fp : ℤ)) * (2 ^ (r.Fd - (FDP : ℤ)) * 2 ^ Fp) = 2 ^ r.F := by
      rw [← zpow_natCast (2 : ℝ) Fp, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      congr 1; ring
    have hpos1 : (2 : ℝ) ^ (r.Fd - (FDP : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hpos2 : (2 : ℝ) ^ Fp ≠ 0 := by positivity
    unfold rowS
    rw [hρ, ← e]
    field_simp
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro idx _; ring
  show |(2 : ℝ) ^ (r.F + (FDP : ℤ) - r.Fd - (Fp : ℤ)) * rowS r H zl ch (a0 + σ * u) / dv -
      (LV.map fun x => (x.1 : ℝ) * x.2.2 t).sum / 2 ^ Fp| ≤ ((rVdelta cb Us r cvs Fp ch : ℕ) : ℝ) / 2 ^ 256
  rw [hf, hg']
  have hdiff : ρ * (∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) * (2 ^ r.F * H (r.mAt idx) (a0 + σ * u))) /
        2 ^ Fp - ρ * (∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) * evalZ (r.ecoef idx) u) / 2 ^ Fp =
      ρ / 2 ^ Fp * ∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) *
        (2 ^ r.F * H (r.mAt idx) (a0 + σ * u) - evalZ (r.ecoef idx) u) := by
    simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro idx _; ring
  rw [hdiff]
  have hu1 : |u| ≤ 1 := le_trans (hu t ht) (by norm_num)
  have hsumb : |∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) *
      (2 ^ r.F * H (r.mAt idx) (a0 + σ * u) - evalZ (r.ecoef idx) u)| ≤
      ((slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch : ℕ) : ℝ) * ((r.dE : ℝ) / 2) := by
    rw [hslotAs, Nat.cast_sum, Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun idx hidx => ?_)
    rw [abs_mul]
    have e1 : |((zl (r.mAt idx)).getD ch 0 : ℝ)| = (((zl (r.mAt idx)).getD ch 0).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e1]
    exact mul_le_mul_of_nonneg_left (hr.ent idx (List.mem_range.mp hidx) u hu1) (Nat.cast_nonneg _)
  set As := ((slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch : ℕ) : ℝ) with hAs_def
  set rR := (rangeX cb.cT (rRr cb Us r) : ℝ) with hrR
  have hδ : (r.dE : ℝ) * As * rR / 2 ^ (Fp + 1) ≤ ((rVdelta cb Us r cvs Fp ch : ℕ) : ℝ) := by
    have hsh : Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256 =
        r.dE * slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch * 2 ^ 256 := Nat.shiftLeft_eq _ 256
    have c1 := le_cdiv (Nat.succ Fp) (Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256)
    have e2 : ((Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256 : ℕ) : ℝ) =
        (r.dE : ℝ) * As * 2 ^ 256 := by
      rw [hsh, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [e2] at c1
    have c2 := le_cdiv 256 (Nat.mul (Packed.cdiv (Nat.succ Fp)
      (Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256))
      (rangeX cb.cT (rRr cb Us r)))
    have e3 : ((Nat.mul (Packed.cdiv (Nat.succ Fp)
        (Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256))
        (rangeX cb.cT (rRr cb Us r)) : ℕ) : ℝ) =
        ((Packed.cdiv (Nat.succ Fp) (Nat.shiftLeft (Nat.mul r.dE (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch))
          256) : ℕ) : ℝ) * rR := by
      rw [hrR]; exact Nat.cast_mul _ _
    rw [e3] at c2
    have hrR0 : 0 ≤ rR := Nat.cast_nonneg _
    calc (r.dE : ℝ) * As * rR / 2 ^ (Fp + 1)
        = ((r.dE : ℝ) * As * 2 ^ 256 / 2 ^ (Fp + 1)) * rR / 2 ^ 256 := by field_simp
      _ ≤ ((Packed.cdiv (Nat.succ Fp) (Nat.shiftLeft (Nat.mul r.dE
            (slot cb.WC (lsum (cvs.map (pvAbs cb.WC cb.nC))) ch)) 256) : ℕ) : ℝ) * rR / 2 ^ 256 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right c1 hrR0
      _ ≤ _ := c2
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Fp)]
  have hAs0 : 0 ≤ As := Nat.cast_nonneg _
  calc |ρ| / 2 ^ Fp * |∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) *
        (2 ^ r.F * H (r.mAt idx) (a0 + σ * u) - evalZ (r.ecoef idx) u)|
      ≤ (rR / 2 ^ 256) / 2 ^ Fp * (As * ((r.dE : ℝ) / 2)) := by
        apply mul_le_mul (div_le_div_of_nonneg_right hρb (by positivity)) hsumb (abs_nonneg _)
        positivity
    _ = ((r.dE : ℝ) * As * rR / 2 ^ (Fp + 1)) / 2 ^ 256 := by
        field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right hδ (by positivity)

/-! ## The row theorem -/

/-- the error claim of a row: structured target errors and box radii, at height `a` -/
noncomputable def rowErr (cb : CellB) (r : RowT) (H : ℕ → ℝ → ℝ) (dl : ℝ → ℝ) (zl : ℕ → List ℤ) (a : ℝ) : ℝ :=
  ∑ tt ∈ Finset.range cb.nT, (cb.herr tt : ℝ) / 2 ^ 256 * |rowS r H zl (cb.N + 1 + tt) a| / (3 * |dl a|) +
  ∑ idx ∈ Finset.range r.nms, |H (r.mAt idx) a| * ((cb.Er (r.mAt idx) : ℝ) / 2 ^ 256) / |dl a|

theorem err_real (nT nms : ℕ) (herr rX Sv Hv mag Er : ℕ → ℝ) (dv ρ rR K P Bd A2 Ej : ℝ)
    (hdv : dv ≠ 0) (hK : 0 < K) (hP : 0 < P) (hBd : 0 < Bd) (hA2 : A2 = Bd * P * K)
    (hρ : ρ = (Bd * dv)⁻¹) (hρb : |ρ| ≤ rR / 2 ^ 256)
    (herr0 : ∀ tt, 0 ≤ herr tt) (hEr0 : ∀ i, 0 ≤ Er i)
    (hrX : ∀ tt < nT, |K * Sv tt / dv| ≤ rX tt / 2 ^ 256)
    (hmag : ∀ idx < nms, |A2 * Hv idx| ≤ mag idx)
    (hE : (∑ tt ∈ Finset.range nT, herr tt * rX tt) * P + 3 * (∑ idx ∈ Finset.range nms, mag idx * Er idx) * rR ≤
      3 * Ej * P * 2 ^ 256 * K) :
    ∑ tt ∈ Finset.range nT, herr tt / 2 ^ 256 * |Sv tt| / (3 * |dv|) +
      ∑ idx ∈ Finset.range nms, |Hv idx| * (Er idx / 2 ^ 256) / |dv| ≤ Ej / 2 ^ 256 := by
  have hdva : 0 < |dv| := abs_pos.mpr hdv
  have h2 : (0 : ℝ) < 2 ^ 256 := by positivity
  have hA2p : 0 < A2 := by rw [hA2]; positivity
  set c1 := (3 * 2 ^ 512 * K)⁻¹ with hc1
  set c2 := (P * K * 2 ^ 512)⁻¹ with hc2
  have hb1 : ∀ tt ∈ Finset.range nT, herr tt / 2 ^ 256 * |Sv tt| / (3 * |dv|) ≤ c1 * (herr tt * rX tt) := by
    intro tt htt
    have h := hrX tt (Finset.mem_range.mp htt)
    rw [abs_div, abs_mul, abs_of_pos hK] at h
    have h' : |Sv tt| / |dv| ≤ rX tt / (2 ^ 256 * K) := by
      have := div_le_div_of_nonneg_right h hK.le
      calc |Sv tt| / |dv| = K * |Sv tt| / |dv| / K := by field_simp
        _ ≤ rX tt / 2 ^ 256 / K := this
        _ = rX tt / (2 ^ 256 * K) := by rw [div_div]
    have he := herr0 tt
    calc herr tt / 2 ^ 256 * |Sv tt| / (3 * |dv|) = herr tt / (3 * 2 ^ 256) * (|Sv tt| / |dv|) := by
          field_simp
      _ ≤ herr tt / (3 * 2 ^ 256) * (rX tt / (2 ^ 256 * K)) := mul_le_mul_of_nonneg_left h' (by positivity)
      _ = c1 * (herr tt * rX tt) := by rw [hc1]; field_simp
  have hinv : 1 / |dv| = Bd * |ρ| := by
    rw [hρ, abs_inv, abs_mul, abs_of_pos hBd]; field_simp
  have hb2 : ∀ idx ∈ Finset.range nms, |Hv idx| * (Er idx / 2 ^ 256) / |dv| ≤ c2 * (mag idx * Er idx) * rR := by
    intro idx hidx
    have hm := hmag idx (Finset.mem_range.mp hidx)
    rw [abs_mul, abs_of_pos hA2p] at hm
    have hH : |Hv idx| ≤ mag idx / A2 := by rw [le_div_iff₀ hA2p]; linarith
    have hE0 := hEr0 idx
    calc |Hv idx| * (Er idx / 2 ^ 256) / |dv| = |Hv idx| * (Er idx / 2 ^ 256) * (1 / |dv|) := by ring
      _ = |Hv idx| * (Er idx / 2 ^ 256) * (Bd * |ρ|) := by rw [hinv]
      _ ≤ mag idx / A2 * (Er idx / 2 ^ 256) * (Bd * (rR / 2 ^ 256)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hH (by positivity))
            (mul_le_mul_of_nonneg_left hρb hBd.le) (by positivity)
          have : 0 ≤ |Hv idx| := abs_nonneg _
          have : 0 ≤ mag idx := le_trans (by positivity) hm
          positivity
      _ = c2 * (mag idx * Er idx) * rR := by rw [hc2, hA2]; field_simp
  have s1 := Finset.sum_le_sum hb1
  have s2 := Finset.sum_le_sum hb2
  rw [← Finset.mul_sum] at s1
  rw [← Finset.sum_mul, ← Finset.mul_sum] at s2
  calc _ ≤ c1 * (∑ tt ∈ Finset.range nT, herr tt * rX tt) +
        c2 * (∑ idx ∈ Finset.range nms, mag idx * Er idx) * rR := add_le_add s1 s2
    _ = ((∑ tt ∈ Finset.range nT, herr tt * rX tt) * P +
          3 * (∑ idx ∈ Finset.range nms, mag idx * Er idx) * rR) / (3 * P * K * 2 ^ 512) := by
        rw [hc1, hc2]; field_simp
    _ ≤ (3 * Ej * P * 2 ^ 256 * K) / (3 * P * K * 2 ^ 512) := div_le_div_of_nonneg_right hE (by positivity)
    _ = Ej / 2 ^ 256 := by field_simp

theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [getD_of_lt _ _ (by simp [hi])]; simp

theorem lsum_cast_range (f : ℕ → ℕ) (n : ℕ) :
    ((lsum ((List.range n).map f) : ℕ) : ℝ) = ∑ i ∈ Finset.range n, (f i : ℝ) := by
  rw [lsum_eq_sum, list_sum_range', Nat.cast_sum]

theorem rhs_cast (s m rR P : ℕ) :
    ((Nat.add (Nat.shiftLeft s P) (Nat.mul (Nat.mul 3 m) rR) : ℕ) : ℝ) = (s : ℝ) * 2 ^ P + 3 * (m : ℝ) * rR := by
  have : Nat.add (Nat.shiftLeft s P) (Nat.mul (Nat.mul 3 m) rR) = s * 2 ^ P + 3 * m * rR := by
    rw [← Nat.shiftLeft_eq]; rfl
  rw [this]; push_cast; ring

theorem lhs_cast (E P : ℕ) : ((Nat.shiftLeft (Nat.mul 3 E) P : ℕ) : ℝ) = 3 * (E : ℝ) * 2 ^ P := by
  have : Nat.shiftLeft (Nat.mul 3 E) P = 3 * E * 2 ^ P := by rw [← Nat.shiftLeft_eq]; rfl
  rw [this]; push_cast; ring

theorem zpow_neg_shift (κ : ℤ) : (2 : ℝ) ^ (-(256 + κ)) * (2 ^ 256 * 2 ^ κ) = 1 := by
  rw [← zpow_natCast (2 : ℝ) 256, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  simp

theorem ckOk_ok {c : Ctx} {V Vt : TM} (h : ckOk c V Vt = true) : Vt.ok = true := by
  simp only [ckOk, Bool.and_eq_true] at h; exact h.1.1.2

/-- **Row leaf soundness.** Every control-channel checkpoint encloses `2^κC Σ_m H_m(a) z_m,ch / λd(a)` on the
height box, and the error claim `Ẽ_j` bounds the structured target errors and the box radii. -/
theorem rowOk_sound (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hWC : 1 ≤ cb.WC)
    (hU : cb.U.ok = true) (hu0 : cb.ucN < 2 ^ (2 * cb.BT + 2)) (hu1 : cb.rN < 2 ^ (2 * cb.BT + 2))
    (hu2 : 2 * (cb.ucN + cb.rN) ≤ 2 ^ 256) (hKt : 1 ≤ cb.Kt)
    (r : RowT) (a0 σ : ℝ) (H : ℕ → ℝ → ℝ) (dl : ℝ → ℝ) (hr : RowSem nI r a0 σ (1 / 2) H dl)
    (Lmax : ℕ) (κC κD : ℤ) (Kc wv we : ℕ) (ck : CkRow)
    (hok : rowOk cb (upow cb.cT cb.U Lmax) cvA r κC κD Kc wv we ck = true) :
    (∀ ch ≤ cb.N, Encl cb.cT (ck.tm cb.cT Kc wv we ch)
      (fun t => (2 : ℝ) ^ κC * rowS r H zl ch (a0 + σ * cb.uf t) / dl (a0 + σ * cb.uf t))) ∧
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, rowErr cb r H dl zl (a0 + σ * cb.uf t) ≤ (ck.Ej : ℝ) / 2 ^ 256 := by
  set Us := upow cb.cT cb.U Lmax with hUsd
  have hUe : Encl cb.cT cb.U cb.uf := tmAff_sound hg cb.ucNeg cb.ucN cb.rN hu0 hu1 hKt hU
  have hUl : Us.length = Lmax + 1 := upowL_length _ _ _ _
  have hUs : ∀ k < Us.length, (Us.getD k zeroTM).ok = true → Encl cb.cT (Us.getD k zeroTM) (fun t => cb.uf t ^ k) :=
    fun k hk hok => upow_encl hg hUe Lmax k (by omega) hok
  have hu := uf_abs cb hu2
  have hsel : selectL cvA r.msL 0 = r.msL.map fun m => cvA.getD m 0 := by
    rw [selectL_spec cvA r.msL 0 hr.sorted (fun m hm => ⟨Nat.zero_le _, by
      have := hr.ltn m hm; have := hch.cvl; omega⟩)]
    simp
  unfold rowOk at hok
  dsimp only at hok
  rw [hsel, rowTMs_eq] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, Nat.ble_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨hFC0, hFD0⟩, hFC, hFD, hFDP, hL, hLd⟩, hb, hDok, hRok, hVok⟩, hctrl, hE⟩ := hok
  set cvs := r.msL.map fun m => cvA.getD m 0 with hcvs
  set FpCn := Int.toNat (fShift r κC) with hFpCn
  set FpDn := Int.toNat (fShift r κD) with hFpDn
  have hFC' : FpCn + 1 ≤ 2 * cb.BT + 2 := hFC
  have hFD' : FpDn + 1 ≤ 2 * cb.BT + 2 := hFD
  have hFDP' : FDP + 1 ≤ 2 * cb.BT + 2 := hFDP
  have hFCz : (FpCn : ℤ) = r.F - r.Fd + FDP - κC := by rw [hFpCn, Int.toNat_of_nonneg hFC0]; rfl
  have hFDz : (FpDn : ℤ) = r.F - r.Fd + FDP - κD := by rw [hFpDn, Int.toNat_of_nonneg hFD0]; rfl
  obtain ⟨hdl0, hR⟩ := rowDR_sound cb hg r a0 σ H dl hr Us hUs hu hLd hFDP' hDok hRok
  set Vf := fun ch => rV cb Us r cvs (cond (Nat.ble ch cb.N) FpCn FpDn) ch with hVf
  have hV : ∀ ch < cb.nC, Encl cb.cT (((List.range cb.nC).map Vf).getD ch zeroTM)
      (fun t => (2 : ℝ) ^ (r.F + (FDP : ℤ) - r.Fd - ((cond (Nat.ble ch cb.N) FpCn FpDn : ℕ) : ℤ)) *
        rowS r H zl ch (a0 + σ * cb.uf t) / dl (a0 + σ * cb.uf t)) := by
    intro ch hch'
    rw [getD_map_range _ _ _ _ hch']
    have hok1 : (Vf ch).ok = true := hVok _ (List.mem_map.mpr ⟨ch, List.mem_range.mpr hch', rfl⟩)
    have hF : cond (Nat.ble ch cb.N) FpCn FpDn + 1 ≤ 2 * cb.BT + 2 := by
      cases Nat.ble ch cb.N <;> simp <;> omega
    exact rowV_sound cb cvA zl hch hg hWC r a0 σ H dl hr Us hUs hu hL hb hdl0 hR _ ch hF hch' hok1
  refine ⟨fun ch hch' => ?_, fun t ht => ?_⟩
  · -- checkpoints of the control channels
    have hchN : ch < cb.nC := by show ch < Nat.succ cb.N + cb.nT; omega
    have hck := hctrl ch (by omega)
    have h1 := hV ch hchN
    have hble : Nat.ble ch cb.N = true := Nat.ble_eq.mpr hch'
    rw [hble] at h1
    have hexp : r.F + (FDP : ℤ) - r.Fd - ((cond true FpCn FpDn : ℕ) : ℤ) = κC := by
      show r.F + (FDP : ℤ) - r.Fd - (FpCn : ℤ) = κC
      rw [hFCz]; ring
    rw [hexp] at h1
    have hrep : RepOK (mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2)) (ck.tm cb.cT Kc wv we ch) :=
      (ofPQ_sound hg _ _ _ (ckOk_ok hck)).repOK
    exact ckOk_sound hg h1 hrep hck
  · -- the error claim
    have hE2 := leShift_real hE
    rw [rhs_cast, lhs_cast, lsum_cast_range] at hE2
    have hmer : r.msL.zip r.magL = (List.range r.nms).map fun i => (slot r.wms r.ms i, slot r.wm r.mag i) :=
      zip_range_map _ _ _
    rw [hmer, List.map_map, lsum_cast_range] at hE2
    set K := (2 : ℝ) ^ κD with hK
    set P := (2 : ℝ) ^ FpDn with hP
    set Bd := (2 : ℝ) ^ (r.Fd - (FDP : ℤ)) with hBd
    set rRv := ((rangeX cb.cT (rRr cb Us r) : ℕ) : ℝ) with hrRv
    have hKp : 0 < K := by rw [hK]; exact zpow_pos (by norm_num) _
    have hBdp : 0 < Bd := by rw [hBd]; exact zpow_pos (by norm_num) _
    have hA2 : (2 : ℝ) ^ r.F = Bd * P * K := by
      rw [hBd, hP, hK, ← zpow_natCast (2 : ℝ) FpDn, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      congr 1; rw [hFDz]; ring
    have hE3 : (∑ tt ∈ Finset.range cb.nT, (cb.herr tt : ℝ) *
          ((rangeX cb.cT (((List.range cb.nC).map Vf).getD (cb.N + 1 + tt) zeroTM) : ℕ) : ℝ)) * P +
        3 * (∑ idx ∈ Finset.range r.nms, ((r.magL.getD idx 0 : ℕ) : ℝ) * (cb.Er (r.mAt idx) : ℝ)) * rRv ≤
        3 * (ck.Ej : ℝ) * P * 2 ^ 256 * K := by
      have e0 := zpow_neg_shift κD
      have hsum1 : ∑ i ∈ Finset.range cb.nT, ((Nat.mul (cb.herr i) (rangeX cb.cT
          (((List.range cb.nC).map Vf).getD (Nat.add (Nat.succ cb.N) i) zeroTM)) : ℕ) : ℝ) =
          ∑ tt ∈ Finset.range cb.nT, (cb.herr tt : ℝ) *
            ((rangeX cb.cT (((List.range cb.nC).map Vf).getD (cb.N + 1 + tt) zeroTM) : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl; intro i _; rw [Nat.mul_eq, Nat.cast_mul]; rfl
      have hsum2 : ∑ i ∈ Finset.range r.nms, ((((fun x : ℕ × ℕ => Nat.mul x.2 (cb.Er x.1)) ∘
          fun i => (slot r.wms r.ms i, slot r.wm r.mag i)) i : ℕ) : ℝ) =
          ∑ idx ∈ Finset.range r.nms, ((r.magL.getD idx 0 : ℕ) : ℝ) * (cb.Er (r.mAt idx) : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi
        have hi' := Finset.mem_range.mp hi
        simp only [Function.comp_apply, Nat.mul_eq, Nat.cast_mul]
        unfold RowT.mAt RowT.msL RowT.magL
        rw [getD_map_range _ _ _ _ hi', getD_map_range _ _ _ _ hi']
      rw [hsum1, hsum2] at hE2
      have := mul_le_mul_of_nonneg_right hE2 (by positivity : (0 : ℝ) ≤ 2 ^ 256 * K)
      rw [mul_assoc _ ((2 : ℝ) ^ (-(256 + κD))), e0, mul_one] at this
      linarith
    unfold rowErr
    apply err_real cb.nT r.nms (fun tt => (cb.herr tt : ℝ))
      (fun tt => ((rangeX cb.cT (((List.range cb.nC).map Vf).getD (cb.N + 1 + tt) zeroTM) : ℕ) : ℝ))
      (fun tt => rowS r H zl (cb.N + 1 + tt) (a0 + σ * cb.uf t)) (fun idx => H (r.mAt idx) (a0 + σ * cb.uf t))
      (fun idx => ((r.magL.getD idx 0 : ℕ) : ℝ)) (fun idx => (cb.Er (r.mAt idx) : ℝ))
      (dl (a0 + σ * cb.uf t)) ((Bd * dl (a0 + σ * cb.uf t))⁻¹) rRv K P Bd ((2 : ℝ) ^ r.F) (ck.Ej : ℝ)
      (hdl0 t ht) hKp (by positivity) hBdp hA2 rfl (rangeX_sound hg hR t ht)
      (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) _ _ hE3
    · intro tt htt
      have hch' : cb.N + 1 + tt < cb.nC := by show cb.N + 1 + tt < Nat.succ cb.N + cb.nT; omega
      have h1 := hV _ hch'
      have hble : Nat.ble (cb.N + 1 + tt) cb.N = false := by
        rw [Bool.eq_false_iff]; intro h; have := Nat.ble_eq.mp h; omega
      rw [hble] at h1
      have hexp : r.F + (FDP : ℤ) - r.Fd - ((cond false FpCn FpDn : ℕ) : ℤ) = κD := by
        show r.F + (FDP : ℤ) - r.Fd - (FpDn : ℤ) = κD
        rw [hFDz]; ring
      rw [hexp] at h1
      exact rangeX_sound hg h1 t ht
    · intro idx hidx
      exact hr.mag idx hidx (cb.uf t) (hu t ht)

end ThomsonCompact.Floor.B
