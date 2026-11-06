import ThomsonCompact.Floor.B.SoundBlockSplit
import ThomsonCompact.Floor.B.KernelQ2

/-!
# Sequential column leaves: `blockOkS` implies `blockOkQ` (F3f)

`blockOkS_imp`: with the block rows `uvsOf row j0 nr`, the checkpoints `cksOf ckd j0 nr` and the weights
`wsL n ww wsN`, `wEL n ww wEN`, a passing sequential leaf `blockOkS` is a passing `blockOkQ` leaf (every intermediate
value is the same), so `blockSplit_sound` applies unchanged.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open scoped BigOperators

theorem cksOf_list (ckL : List CkRow) (d : CkRow) (j0 nr : ℕ) (h : j0 + nr ≤ ckL.length) :
    cksOf (fun j => ckL.getD j d) j0 nr = (ckL.drop j0).take nr := by
  apply List.ext_getElem
  · rw [show (cksOf (fun j => ckL.getD j d) j0 nr).length = nr by simp [cksOf], List.length_take,
      List.length_drop]
    omega
  · intro k h1 h2
    simp only [cksOf, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [cksOf] at h1; show j0 + k < ckL.length; omega), Option.getD_some]
    rfl

/-! ## The loops -/

theorem touchR_eq {α : Type} (u : ℕ) : ∀ (l : List ((ℕ × ℕ) × α)), touchR u l = touchV l u
  | [] => rfl
  | x :: l => by
    have ih := touchR_eq u l
    show cond (Nat.beq x.1.1 u) ((x.1.2, x.2) :: touchR u l)
      (cond (and (Nat.beq x.1.2 u) (Bool.not (Nat.beq x.1.1 u))) ((x.1.1, x.2) :: touchR u l) (touchR u l)) = _
    rw [ih]
    unfold touchV
    rw [List.filterMap_cons]
    cases Nat.beq x.1.1 u <;> cases Nat.beq x.1.2 u <;> rfl

theorem st1L_eq (wz zq : ℕ) : ∀ (t : List (ℕ × PAcc)) (acc : PAcc),
    st1L wz zq t acc = t.foldl (fun acc x => let z := zsm wz zq x.1; cond (Nat.beq z.2 0) acc (acc.addm z.1 z.2 x.2)) acc
  | [], _ => rfl
  | x :: t, acc => st1L_eq wz zq t _

theorem foldl_fix {α β : Type*} (f : β → α → β) : ∀ (l : List α) (b : β), (∀ x ∈ l, f b x = b) → l.foldl f b = b
  | [], _, _ => rfl
  | x :: l, b, h => by
    rw [List.foldl_cons, h x List.mem_cons_self]
    exact foldl_fix f l b (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem mem_zip_range' {α : Type*} {x : α × ℕ} {l : List α} {u0 : ℕ} (h : x ∈ l.zip (List.range' u0 l.length)) :
    u0 ≤ x.2 := by
  have := (List.of_mem_zip h).2
  rw [List.mem_range'] at this
  omega

/-- stage 2 with the early stop: rows of `Zi` vanish above the diagonal -/
theorem st2L_eq (wz zp p : ℕ) (hz : ∀ u, p < u → (zsm wz zp u).2 = 0) :
    ∀ (Ys : List PAcc) (u0 : ℕ) (acc : PAcc),
    st2L wz zp p Ys u0 acc = (Ys.zip (List.range' u0 Ys.length)).foldl (fun acc x => let z := zsm wz zp x.2;
      cond (or (Nat.beq z.2 0) (Nat.beq x.1.A 0)) acc (acc.addm z.1 z.2 x.1)) acc
  | [], _, _ => rfl
  | Y :: Ys, u0, acc => by
    show cond (Nat.blt p u0) acc (st2L wz zp p Ys (u0 + 1) (cond (or (Nat.beq (zsm wz zp u0).2 0) (Nat.beq Y.A 0)) acc
      (acc.addm (zsm wz zp u0).1 (zsm wz zp u0).2 Y))) = _
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons]
    by_cases hp : p < u0
    · have hb : Nat.blt p u0 = true := Nat.blt_eq.mpr hp
      rw [hb, cond_true]
      have h0 : (zsm wz zp u0).2 = 0 := hz u0 hp
      simp only [h0, Nat.beq_refl, Bool.true_or, cond_true]
      symm
      apply foldl_fix
      intro x hx
      have hx2 := mem_zip_range' hx
      simp only [hz x.2 (by omega), Nat.beq_refl, Bool.true_or, cond_true]
    · have hb : Nat.blt p u0 = false := by
        rw [Bool.eq_false_iff]; intro h'; exact hp (Nat.blt_eq.mp h')
      rw [hb, cond_false]
      exact st2L_eq wz zp p hz Ys (u0 + 1) _

theorem stage2z_st2L (wz zp p : ℕ) (hz : ∀ u, p < u → (zsm wz zp u).2 = 0) (Ys : List PAcc) :
    st2L wz zp p Ys 0 PAcc.zero = stage2z wz zp Ys := by
  rw [st2L_eq wz zp p hz, stage2z, List.range_eq_range']

theorem zsm_zero_of_shift {wz z p : ℕ} (h : Nat.shiftRight z (wz * (p + 1)) = 0) (u : ℕ) (hu : p < u) :
    (zsm wz z u).2 = 0 := by
  unfold zsm smDec
  show (slot wz z u) >>> 1 = 0
  have : slot wz z u = 0 := by
    rw [slot_eq]
    have e : z / 2 ^ (wz * u) = 0 := by
      have h' : z / 2 ^ (wz * (p + 1)) = 0 := by rw [← Nat.shiftRight_eq_div_pow]; exact h
      have e2 : 2 ^ (wz * u) = 2 ^ (wz * (p + 1)) * 2 ^ (wz * (u - (p + 1))) := by
        rw [← pow_add]; congr 1
        rw [← Nat.mul_add]; congr 1; omega
      rw [e2, ← Nat.div_div_eq_div_mul, h', Nat.zero_div]
    rw [e]; rfl
  rw [this]; rfl

theorem zLower_spec (wz : ℕ) : ∀ (l : List ℕ) (p0 : ℕ), zLower wz l p0 = true →
    ∀ i < l.length, ∀ u, p0 + i < u → (zsm wz (l.getD i 0) u).2 = 0
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | z :: l, p0, h, i, hi => by
    have h' : (Nat.beq (Nat.shiftRight z (Nat.mul wz (Nat.succ p0))) 0 && zLower wz l (Nat.succ p0)) = true := h
    rw [Bool.and_eq_true] at h'
    intro u hu
    rcases i with _ | i
    · exact zsm_zero_of_shift (Nat.eq_of_beq_eq_true h'.1) u (by omega)
    · have := zLower_spec wz l (p0 + 1) h'.2 i (by simp at hi; omega) u (by omega)
      simpa using this

/-! ## One pair, one column, the column fold -/

theorem rsAddN_eq (LS ww n p q t wN acc : ℕ) (hp : p < n) (hq : q < n) :
    rsAddN LS ww p q t wN acc = rsAdd LS p q t ((List.range n).map (slot ww wN)) acc := by
  unfold rsAddN rsAdd
  rw [getD_map_range _ _ _ _ hp, getD_map_range _ _ _ _ hq]

theorem bupdS_eq (c : Ctx) (FG LB LE LS ww n ch0 nch smax : ℕ) (okV : Bool) (wsN : ℕ → ℕ) (wEN : ℕ) (p q : ℕ)
    (hp : p < n) (hq : q < n) (G : PAcc) (st : List ℕ × ℕ × Bool × ℕ) :
    bupdS c FG LB LE LS ww nch smax okV ((List.range nch).map fun i => wsN (Nat.add ch0 i)) wEN p q G st =
      bupd c FG LB LE LS ch0 nch smax okV (wsL n ww wsN) (wEL n ww wEN) p q G st := by
  unfold bupdS bupd
  dsimp only
  have e1 : (List.zip ((List.range nch).map fun ch =>
        zfin c FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV))
        ((List.range nch).map fun i => wsN (Nat.add ch0 i))) =
      ((bTs c FG LB LE nch smax okV G).zip (List.range nch)).map fun x => (x.1, wsN (Nat.add ch0 x.2)) := by
    rw [List.zip_map_right]; rfl
  rw [e1, List.zip_map_right, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    exact rsAddN_eq LS ww n p q _ _ _ hp hq
  · congr 1
    exact rsAddN_eq LS ww n p q _ _ _ hp hq

/-- one column: the sequential pairs `p ≤ q` = the pair fold of `blockOkQ` -/
theorem colS_eq (c : Ctx) (wz FG LB LE LS ww n ch0 nch smax : ℕ) (okV : Bool) (wsN : ℕ → ℕ) (wEN q : ℕ)
    (hq : q < n) (Ys : List PAcc) :
    ∀ (l : List ℕ) (p0 : ℕ) (st : List ℕ × ℕ × Bool × ℕ),
    (∀ i < l.length, ∀ u, p0 + i < u → (zsm wz (l.getD i 0) u).2 = 0) →
    colS c wz FG LB LE LS ww nch smax okV ((List.range nch).map fun i => wsN (Nat.add ch0 i)) wEN q Ys l p0 st =
      (l.zip (List.range' p0 l.length)).foldl (fun st' zp => cond (Nat.ble zp.2 q)
        (bupd c FG LB LE LS ch0 nch smax okV (wsL n ww wsN) (wEL n ww wEN) zp.2 q (stage2z wz zp.1 Ys) st') st') st
  | [], _, _, _ => rfl
  | zp :: l, p0, st, hz => by
    show cond (Nat.blt q p0) st (colS c wz FG LB LE LS ww nch smax okV
      ((List.range nch).map fun i => wsN (Nat.add ch0 i)) wEN q Ys l (p0 + 1)
      (bupdS c FG LB LE LS ww nch smax okV ((List.range nch).map fun i => wsN (Nat.add ch0 i)) wEN p0 q
        (st2L wz zp p0 Ys 0 PAcc.zero) st)) = _
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons]
    by_cases hp : q < p0
    · have hb : Nat.blt q p0 = true := Nat.blt_eq.mpr hp
      have hb2 : Nat.ble p0 q = false := by rw [Bool.eq_false_iff]; intro h'; have := Nat.ble_eq.mp h'; omega
      rw [hb, cond_true, hb2, cond_false]
      symm
      apply foldl_fix
      intro x hx
      have hx2 := mem_zip_range' hx
      have : Nat.ble x.2 q = false := by rw [Bool.eq_false_iff]; intro h'; have := Nat.ble_eq.mp h'; omega
      rw [this, cond_false]
    · have hb : Nat.blt q p0 = false := by rw [Bool.eq_false_iff]; intro h'; exact hp (Nat.blt_eq.mp h')
      have hb2 : Nat.ble p0 q = true := Nat.ble_eq.mpr (by omega)
      rw [hb, cond_false, hb2, cond_true]
      have h0 : ∀ u, p0 < u → (zsm wz zp u).2 = 0 := fun u hu => by
        have := hz 0 (by simp) u (by omega); simpa using this
      rw [stage2z_st2L wz zp p0 h0 Ys, bupdS_eq c FG LB LE LS ww n ch0 nch smax okV wsN wEN p0 q (by omega) hq]
      exact colS_eq c wz FG LB LE LS ww n ch0 nch smax okV wsN wEN q hq Ys l (p0 + 1) _ (fun i hi u hu => by
        have := hz (i + 1) (by simp; omega) u (by omega); simpa using this)

/-- the column fold of `blockOkS` is the column fold of `blockOkQ` -/
theorem bfoldS_eq (c : Ctx) (wz FG LB LE LS ww n ch0 nch smax : ℕ) (okV : Bool) (wsN : ℕ → ℕ) (wEN : ℕ)
    (zrows : List ℕ) (hzl : zrows.length = n) (hzL : zLower wz zrows 0 = true) (cols : List (ℕ × ℕ))
    (hcols : ∀ zq ∈ cols, zq.2 < n) (tl : List (List (ℕ × PAcc))) :
    bfoldS c wz FG LB LE LS ww nch smax okV ((List.range nch).map fun i => wsN (Nat.add ch0 i)) wEN zrows cols tl =
      bfoldQ c wz FG LB LE LS ch0 nch smax okV (wsL n ww wsN) (wEL n ww wEN) (zrows.zip (List.range n)) cols tl := by
  unfold bfoldS bfoldQ
  apply foldl_congr_mem
  intro st zq hzq
  have hst1 : (tl.map fun t => st1L wz zq.1 t PAcc.zero) = stage1z wz zq.1 tl := by
    unfold stage1z
    apply List.map_congr_left; intro t _; rw [st1L_eq]
  rw [hst1]
  have hz := zLower_spec wz zrows 0 hzL
  rw [colS_eq c wz FG LB LE LS ww n ch0 nch smax okV wsN wEN zq.2 (hcols zq hzq) _ zrows 0 st
    (fun i hi u hu => hz i hi u hu)]
  rw [← hzl, ← List.range_eq_range']
  rfl

/-! ## The leaf -/

theorem foldl_max_le (M : ℕ) : ∀ (l : List ℕ) (m : ℕ), m ≤ M → (∀ x ∈ l, x ≤ M) → l.foldl Nat.max m ≤ M
  | [], m, hm, _ => hm
  | x :: l, m, hm, h => foldl_max_le M l (Nat.max m x) (Nat.max_le.mpr ⟨hm, h x List.mem_cons_self⟩)
      (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem wmax_le_pow (n ww : ℕ) (wsN : ℕ → ℕ) (wEN ch0 nch : ℕ) :
    (List.range nch).foldl (fun m i => (wsL n ww wsN (Nat.add ch0 i)).foldl Nat.max m)
      ((wEL n ww wEN).foldl Nat.max 0) ≤ 2 ^ ww := by
  have hs : ∀ (N x i : ℕ), x ∈ (List.range N).map (slot ww i) → x ≤ 2 ^ ww := by
    intro N x i hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact (slot_lt ww i k).le
  have h0 : (wEL n ww wEN).foldl Nat.max 0 ≤ 2 ^ ww :=
    foldl_max_le _ _ 0 (Nat.zero_le _) (fun x hx => hs n x wEN hx)
  generalize (wEL n ww wEN).foldl Nat.max 0 = m0 at h0
  induction (List.range nch) generalizing m0 with
  | nil => exact h0
  | cons i l ih =>
    rw [List.foldl_cons]
    exact ih _ (foldl_max_le _ _ m0 h0 (fun x hx => hs n x _ hx))

/-- **A passing sequential column leaf is a passing `blockOkQ` leaf.** -/
theorem blockOkS_imp (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG LB LE LS ch0 nch ww : ℕ) (wsN : ℕ → ℕ) (wEN : ℕ) (q0 nq : ℕ) (Rp : ℕ → ℕ) (RpE : ℕ)
    (h : blockOkS cb (uvsOf row j0 nr) (cksOf ckd j0 nr) Kc wv we n wz zrows FG LB LE LS ch0 nch ww wsN wEN q0 nq
      Rp RpE = true) :
    blockOkQ cb row Kc wv we ckd j0 nr n wz zrows FG LB LE LS ch0 nch (wsL n ww wsN) (wEL n ww wEN) q0 nq Rp RpE
      = true := by
  set B : BGrp := ⟨cb, row, Kc, wv, we, ckd, j0, nr, n, wz, zrows, FG, LB, LE, LS, ch0, nch, wsL n ww wsN,
    wEL n ww wEN⟩ with hB
  have hpk : (cksOf ckd j0 nr).map (fun ck => ckPack cb.cT Kc wv we LB LE ck ch0 nch) = B.pk := by
    rw [B.pk_eq]; unfold cksOf; rw [List.map_map]; rfl
  have htl : (List.range n).map (fun u => touchR u (((uvsOf row j0 nr).zip B.pk).map fun x => (x.1, x.2.1))) =
      B.tl := by
    show _ = btl row B.pk j0 nr n
    unfold btl
    apply List.map_congr_left
    intro u _
    rw [touchR_eq]
    congr 1
    apply List.ext_getElem (by simp [uvsOf, bjs])
    intro k h1 h2
    simp [uvsOf, bjs]
  have hEj : (cksOf ckd j0 nr).foldl (fun m ck => Nat.max m ck.Ej) 0 = B.Ejmax := by
    show _ = (bjs j0 nr).foldl (fun m j => Nat.max m (ckd j).Ej) 0
    unfold cksOf bjs; rw [List.foldl_map, List.foldl_map]
  -- unfold the sequential leaf
  have h' := h
  unfold blockOkS at h'
  dsimp only at h'
  rw [hpk, htl, hEj] at h'
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h'
  obtain ⟨⟨⟨⟨hok, hFG⟩, hch⟩, ⟨hzl, hzL⟩, hovB, hovE, hovS⟩, hY, hYE⟩ := h'
  have hcols : ∀ zq ∈ ((zrows.zip (List.range n)).drop q0).take nq, zq.2 < n := by
    intro zq hzq
    have := (List.of_mem_zip (List.mem_of_mem_drop (List.mem_of_mem_take hzq))).2
    exact List.mem_range.mp this
  have hres := bfoldS_eq cb.cT wz FG LB LE LS ww n ch0 nch (B.pk.foldl (fun m x => Nat.max m x.2.2.2) 0)
    (B.pk.all fun x => x.2.1) wsN wEN zrows hzl hzL _ hcols B.tl
  rw [hres] at hok hovB hovE hovS hY hYE
  show B.leaf q0 nq Rp RpE = true
  rw [BGrp.leaf_eq]
  dsimp only
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq]
  refine ⟨⟨⟨⟨hok, hFG⟩, hch⟩, hzl, hovB, hovE, ?_⟩, hY, hYE⟩
  refine lt_of_le_of_lt ?_ hovS
  show Nat.mul (Nat.mul (Nat.mul n _) B.wmax) 2 ≤ Nat.mul (Nat.mul (Nat.mul n _) (Nat.pow 2 ww)) 2
  have := wmax_le_pow n ww wsN wEN ch0 nch
  simp only [Nat.mul_eq, Nat.pow_eq]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)

end ThomsonCompact.Floor.B
