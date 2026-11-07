import ThomsonCompact.Floor.B.SoundBlockQ
import ThomsonCompact.Floor.B.KernelQ

/-!
# Column-split block leaves: soundness (F3f)

`blockSplit_sound`: the column leaves `blockOkQ` (pairs `p ≤ q` with `q` in one column part, packed row sums bounded
by stored partial sums) of one channel group, together with the aggregation leaf `blockAggOk` (Young checks of the
summed partial sums), give the conclusions of `blockOk_sound` (`BlockSound`).

Steps (Floor/HANDOVER.md, Remaining 1): (a) skipping zero metric entries / untouched indices does not change the
accumulators (`stage1z_eq`, `stage2z_eq`: a stage-1 accumulator with `A = 0` is zero); (b) `bfoldQ` is the
`outer_spec` fold over the columns of the leaf (`bfoldQ_eq`); (c) per leaf: the pair facts and the partial row sums
(`BGrp.leaf_spec`); (d) the column parts partition `[0, n)` (`parts_sum`), so the partial row sums add up to the
full ones, and `young_qb` applies.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open Blueprint.CAP
open scoped BigOperators

/-! ## (a) Skipping zero terms -/

theorem PAcc.addm_zero_n (acc : PAcc) (ng : Bool) (x : PAcc) : acc.addm ng 0 x = acc := by
  cases acc; simp [PAcc.addm]

theorem PAcc.addm_zero_x (acc : PAcc) (ng : Bool) (n : ℕ) : acc.addm ng n PAcc.zero = acc := by
  cases acc; cases ng <;> simp [PAcc.addm, PAcc.zero]

theorem foldl_congr_mem {α β : Type*} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ b, ∀ x ∈ l, f b x = g b x) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, b, h => by
    simp only [List.foldl_cons]
    rw [h b x List.mem_cons_self]
    exact foldl_congr_mem f g l _ (fun b y hy => h b y (List.mem_cons_of_mem _ hy))

theorem stage1z_eq (wz zq : ℕ) (tl : List (List (ℕ × PAcc))) : stage1z wz zq tl = stage1 wz zq tl := by
  unfold stage1z stage1
  apply List.map_congr_left
  intro t _
  apply foldl_congr_mem
  intro acc x _
  cases h : Nat.beq (zsm wz zq x.1).2 0
  · simp only [h, cond_false]
  · simp only [h, cond_true]
    rw [Nat.eq_of_beq_eq_true h, PAcc.addm_zero_n]

theorem IsComb.eq_zero {nr : ℕ} {X : ℕ → PAcc} {x : PAcc} {s : ℕ → ℤ} {a : ℕ → ℕ} (h : IsComb nr X x s a)
    (hA : x.A = 0) : x = PAcc.zero := by
  obtain ⟨ap, an, _, ha, hP, hQ⟩ := h.ex
  have ha0 : ∀ i ∈ Finset.range nr, a i = 0 := by
    have h1 := h.A
    rw [hA] at h1
    exact Finset.sum_eq_zero_iff.mp h1.symm
  have hap : ∀ i ∈ Finset.range nr, ap i = 0 := fun i hi => by have := ha i; have := ha0 i hi; omega
  have han : ∀ i ∈ Finset.range nr, an i = 0 := fun i hi => by have := ha i; have := ha0 i hi; omega
  have e1 : x.P = 0 := by rw [hP]; exact Finset.sum_eq_zero (fun i hi => by rw [hap i hi, zero_mul])
  have e2 : x.Q = 0 := by rw [hQ]; exact Finset.sum_eq_zero (fun i hi => by rw [han i hi, zero_mul])
  have e3 : x.E = 0 := by rw [h.E]; exact Finset.sum_eq_zero (fun i hi => by rw [ha0 i hi, zero_mul])
  have e4 : x.H = 0 := by rw [h.H]; exact Finset.sum_eq_zero (fun i hi => by rw [ha0 i hi, zero_mul])
  cases x
  simp only at e1 e2 e3 e4 hA
  simp [PAcc.zero, e1, e2, e3, e4, hA]

theorem stage2z_eq (wz zp : ℕ) (Ys : List PAcc) (hY : ∀ Y ∈ Ys, Y.A = 0 → Y = PAcc.zero) :
    stage2z wz zp Ys = stage2 wz zp Ys := by
  unfold stage2z stage2
  apply foldl_congr_mem
  intro acc x hx
  have hx1 : x.1 ∈ Ys := (List.of_mem_zip hx).1
  cases h1 : Nat.beq (zsm wz zp x.2).2 0
  · cases h2 : Nat.beq x.1.A 0
    · simp only [h1, h2, Bool.or_false, cond_false]
    · simp only [h1, h2, Bool.or_true, cond_true]
      rw [hY x.1 hx1 (Nat.eq_of_beq_eq_true h2), PAcc.addm_zero_x]
  · simp only [h1, Bool.true_or, cond_true]
    rw [Nat.eq_of_beq_eq_true h1, PAcc.addm_zero_n]

/-- stage 2 on stage-1 outputs: untouched indices carry zero accumulators -/
theorem stage2z_stage1 (nr : ℕ) (X : ℕ → PAcc) (hQ : ∀ i, (X i).Q = 0) (hA : ∀ i, (X i).A = 1)
    (uI vI : ℕ → ℕ) (n wz zp zq : ℕ) :
    stage2z wz zp (stage1 wz zq ((List.range n).map (touchV ((List.range nr).map fun i => ((uI i, vI i), X i))))) =
      stage2 wz zp (stage1 wz zq ((List.range n).map (touchV ((List.range nr).map fun i => ((uI i, vI i), X i))))) := by
  apply stage2z_eq
  intro Y hY hY0
  rw [stage1_eq] at hY
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hY
  exact (stage1_comb nr X hQ hA uI vI wz zq u).eq_zero hY0

/-! ## (b) The column fold -/

theorem bfoldQ_eq (c : Ctx) (wz FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (nz nzq : List (ℕ × ℕ)) (tl : List (List (ℕ × PAcc)))
    (h2 : ∀ zp zq, stage2z wz zp (stage1 wz zq tl) = stage2 wz zp (stage1 wz zq tl)) :
    bfoldQ c wz FG LB LE LS ch0 nch smax okV ws wE nz nzq tl =
      nzq.foldl (fun st zq => nz.foldl (fun st' zp => cond (Nat.ble zp.2 zq.2)
        (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 (stage1 wz zq.1 tl)) st') st') st)
        (List.replicate nch 0, 0, true, 0) := by
  unfold bfoldQ
  simp only [stage1z_eq, h2]
  rfl

/-! ## Sums over column parts -/

/-- the columns `q0 ≤ q < q0 + nq` of `[0, n)` as an index range -/
theorem sum_range_ind (n q0 nq : ℕ) (F : ℕ → ℕ) :
    ∑ q ∈ Finset.range n, (if q0 ≤ q ∧ q < q0 + nq then F q else 0) =
      ∑ i ∈ Finset.range (min nq (n - q0)), F (q0 + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : q0 ≤ n ∧ n < q0 + nq
    · rw [if_pos h, show min nq (n + 1 - q0) = min nq (n - q0) + 1 by omega, Finset.sum_range_succ,
        show q0 + min nq (n - q0) = n by omega]
    · rw [if_neg h, add_zero, show min nq (n + 1 - q0) = min nq (n - q0) by omega]

theorem drop_take_zip (zrows : List ℕ) (n q0 nq : ℕ) (hz : zrows.length = n) :
    ((zrows.zip (List.range n)).drop q0).take nq =
      (List.range (min nq (n - q0))).map fun i => (zrows.getD (q0 + i) 0, q0 + i) := by
  apply List.ext_getElem
  · simp [hz]
  · intro k h1 h2
    have hk : k < min nq (n - q0) := by simpa using h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_zip, List.getElem_range, List.getElem_map]
    have hl : q0 + k < zrows.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

theorem rsT_zero (LS p q : ℕ) (w : List ℕ) : rsT LS p q 0 w = 0 := by
  unfold rsT; split_ifs <;> simp

theorem ite_rsT (c : Prop) [Decidable c] (LS p q t : ℕ) (w : List ℕ) :
    (if c then rsT LS p q t w else 0) = rsT LS p q (if c then t else 0) w := by
  split_ifs
  · rfl
  · rw [rsT_zero]

/-- the kernel's column sums as the packed row sums of the masked pair values -/
theorem cols_sum (LS n q0 nq : ℕ) (t : ℕ → ℕ → ℕ) (w : List ℕ) :
    ∑ i ∈ Finset.range (min nq (n - q0)), ∑ p ∈ Finset.range n,
      (if p ≤ q0 + i then rsT LS p (q0 + i) (t p (q0 + i)) w else 0) =
    ∑ q ∈ Finset.range n, ∑ p ∈ Finset.range n,
      (if p ≤ q then rsT LS p q (if q0 ≤ q ∧ q < q0 + nq then t p q else 0) w else 0) := by
  rw [← sum_range_ind n q0 nq (fun q => ∑ p ∈ Finset.range n, if p ≤ q then rsT LS p q (t p q) w else 0)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q0 ≤ q ∧ q < q0 + nq
  · rw [if_pos hq]
    apply Finset.sum_congr rfl; intro p _
    rw [if_pos hq]
  · rw [if_neg hq]
    symm
    apply Finset.sum_eq_zero; intro p _
    rw [if_neg hq, rsT_zero]; simp

/-! ## (d) Partitions of `[0, n)` into column parts -/

theorem lsum_cons (x : ℕ) (l : List ℕ) : lsum (x :: l) = x + lsum l := rfl

theorem lsum_take_succ (x : ℕ) (l : List ℕ) (k : ℕ) : lsum ((x :: l).take (k + 1)) = x + lsum (l.take k) := rfl

/-- every `m < Σ nqs` lies in exactly one part -/
theorem parts_sum : ∀ (nqs : List ℕ) (m a : ℕ), m < lsum nqs →
    ∑ k ∈ Finset.range nqs.length,
      (if lsum (nqs.take k) ≤ m ∧ m < lsum (nqs.take k) + nqs.getD k 0 then a else 0) = a
  | [], m, a, h => by simp [lsum] at h
  | x :: l, m, a, h => by
    rw [List.length_cons, Finset.sum_range_succ']
    by_cases hm : m < x
    · have e0 : (if lsum ((x :: l).take 0) ≤ m ∧ m < lsum ((x :: l).take 0) + (x :: l).getD 0 0 then a else 0) = a := by
        rw [if_pos]; simp [lsum]; omega
      rw [e0]
      have : ∀ k ∈ Finset.range l.length,
          (if lsum ((x :: l).take (k + 1)) ≤ m ∧ m < lsum ((x :: l).take (k + 1)) + (x :: l).getD (k + 1) 0
            then a else 0) = 0 := by
        intro k _
        rw [if_neg]
        rw [lsum_take_succ]; omega
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero, zero_add]
    · have e0 : (if lsum ((x :: l).take 0) ≤ m ∧ m < lsum ((x :: l).take 0) + (x :: l).getD 0 0 then a else 0) = 0 := by
        rw [if_neg]; simp [lsum]; omega
      rw [e0, add_zero]
      have h' : m - x < lsum l := by rw [lsum_cons] at h; omega
      conv_rhs => rw [← parts_sum l (m - x) a h']
      apply Finset.sum_congr rfl
      intro k _
      rw [lsum_take_succ]
      have e : (x :: l).getD (k + 1) 0 = l.getD k 0 := by simp [List.getD_eq_getElem?_getD]
      rw [e]
      congr 1
      apply propext
      omega

/-- every `m < Σ nqs` lies in some part -/
theorem parts_cover (nqs : List ℕ) (m : ℕ) (h : m < lsum nqs) :
    ∃ k < nqs.length, lsum (nqs.take k) ≤ m ∧ m < lsum (nqs.take k) + nqs.getD k 0 := by
  by_contra hne
  push Not at hne
  have h1 := parts_sum nqs m 1 h
  rw [Finset.sum_eq_zero (fun k hk => if_neg (fun hc => absurd (hne k (Finset.mem_range.mp hk) hc.1) (by omega)))] at h1
  exact absurd h1 (by norm_num)

theorem lsum_map_getD {α : Type*} (g : α → ℕ) (d : α) : ∀ l : List α,
    lsum (l.map g) = ∑ k ∈ Finset.range l.length, g (l.getD k d)
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, lsum_cons, lsum_map_getD g d l, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-! ## (c) One channel group and its column leaves -/

/-- the data of one channel group of a block (shared by its column leaves) -/
structure BGrp where
  cb : CellB
  row : ℕ → RowT
  Kc : ℕ
  wv : ℕ
  we : ℕ
  ckd : ℕ → CkRow
  j0 : ℕ
  nr : ℕ
  n : ℕ
  wz : ℕ
  zrows : List ℕ
  FG : ℕ
  LB : ℕ
  LE : ℕ
  LS : ℕ
  ch0 : ℕ
  nch : ℕ
  ws : ℕ → List ℕ
  wE : List ℕ

namespace BGrp
variable (B : BGrp)

noncomputable def pk : List (PAcc × Bool × ℕ × ℕ) := bpk B.cb.cT B.Kc B.wv B.we B.LB B.LE B.ckd B.j0 B.nr B.ch0 B.nch
noncomputable def okV : Bool := B.pk.all fun x => x.2.1
noncomputable def emax : ℕ := B.pk.foldl (fun m x => Nat.max m x.2.2.1) 0
noncomputable def smax : ℕ := B.pk.foldl (fun m x => Nat.max m x.2.2.2) 0
noncomputable def Ejmax : ℕ := (bjs B.j0 B.nr).foldl (fun m j => Nat.max m (B.ckd j).Ej) 0
noncomputable def tl : List (List (ℕ × PAcc)) := btl B.row B.pk B.j0 B.nr B.n
/-- the accumulator of the pair `(p, q)` -/
noncomputable def G (p q : ℕ) : PAcc := stage2 B.wz (B.zrows.getD p 0) (stage1 B.wz (B.zrows.getD q 0) B.tl)
/-- the channel TM `ch` of the pair `(p, q)` -/
noncomputable def T (ch p q : ℕ) : TM := (bTs B.cb.cT B.FG B.LB B.LE B.nch B.smax B.okV (B.G p q)).getD ch zeroTM
/-- the error part of the pair `(p, q)` -/
noncomputable def HH (p q : ℕ) : ℕ := Packed.cdiv 64 (B.G p q).H
noncomputable def wmax : ℕ :=
  (List.range B.nch).foldl (fun m i => (B.ws (Nat.add B.ch0 i)).foldl Nat.max m) (B.wE.foldl Nat.max 0)
/-- the column leaf `q0 ≤ q < q0 + nq` -/
noncomputable def leaf (q0 nq : ℕ) (Rp : ℕ → ℕ) (RpE : ℕ) : Bool :=
  blockOkQ B.cb B.row B.Kc B.wv B.we B.ckd B.j0 B.nr B.n B.wz B.zrows B.FG B.LB B.LE B.LS B.ch0 B.nch B.ws B.wE
    q0 nq Rp RpE

/-- the payload of row `i` -/
noncomputable def X (i : ℕ) : PAcc := (ckPack B.cb.cT B.Kc B.wv B.we B.LB B.LE (B.ckd (B.j0 + i)) B.ch0 B.nch).1
/-- the checkpoint TM of row `i`, channel `ch0 + c` -/
noncomputable def Tc (i c : ℕ) : TM := (B.ckd (B.j0 + i)).tm B.cb.cT B.Kc B.wv B.we (B.ch0 + c)
noncomputable def uI (i : ℕ) : ℕ := (B.row (B.j0 + i)).u
noncomputable def vI (i : ℕ) : ℕ := (B.row (B.j0 + i)).v

theorem leaf_eq (q0 nq : ℕ) (Rp : ℕ → ℕ) (RpE : ℕ) :
    B.leaf q0 nq Rp RpE =
      (let res := bfoldQ B.cb.cT B.wz B.FG B.LB B.LE B.LS B.ch0 B.nch B.smax B.okV B.ws B.wE
         (B.zrows.zip (List.range B.n)) (((B.zrows.zip (List.range B.n)).drop q0).take nq) B.tl
       let tzmax := res.2.2.2
       let Tmax := Nat.max (Nat.add (Nat.add B.cb.cT.twoB (Packed.cdiv B.FG (Nat.pow 2 B.LE))) B.cb.cT.m)
         (Packed.cdiv 64 (Nat.mul tzmax B.Ejmax))
       and (and (and (and res.2.2.1 (Nat.blt B.FG B.cb.cT.W)) (Nat.ble (Nat.add B.ch0 B.nch) (Nat.succ B.cb.N)))
          (and (Nat.beq B.zrows.length B.n)
            (and (Nat.blt (Nat.mul tzmax B.cb.cT.twoK) (Nat.pow 2 B.LB))
              (and (Nat.blt (Nat.mul tzmax B.emax) (Nat.pow 2 B.LE))
                (Nat.blt (Nat.mul (Nat.mul (Nat.mul B.n Tmax) B.wmax) 2) (Nat.pow 2 B.LS))))))
        (and ((res.1.zip (List.range B.nch)).all fun x => slotsLe B.LS B.n x.1 (Rp (Nat.add B.ch0 x.2)))
          (slotsLe B.LS B.n res.2.1 RpE))) := rfl

theorem pk_eq : B.pk = (List.range B.nr).map fun i =>
    ckPack B.cb.cT B.Kc B.wv B.we B.LB B.LE (B.ckd (B.j0 + i)) B.ch0 B.nch := by
  unfold pk bpk bjs; rw [List.map_map]; rfl

theorem X_spec (i : ℕ) : (B.X i).P = ∑ c ∈ Finset.range B.nch, (B.Tc i c).v * 2 ^ (B.LB * c) ∧ (B.X i).Q = 0 ∧
    (B.X i).E = ∑ c ∈ Finset.range B.nch, (B.Tc i c).e * 2 ^ (B.LE * c) ∧ (B.X i).H = (B.ckd (B.j0 + i)).Ej ∧
    (B.X i).A = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := ckPack_spec B.cb.cT B.Kc B.wv B.we B.LB B.LE (B.ckd (B.j0 + i)) B.ch0 B.nch
  exact ⟨h1, h2, h3, h4, h5⟩

theorem Tc_le (i : ℕ) (hi : i < B.nr) (c : ℕ) (hc : c < B.nch) : (B.Tc i c).s ≤ B.smax ∧ (B.Tc i c).e ≤ B.emax := by
  obtain ⟨_, _, _, _, _, _, h7, h8⟩ := ckPack_spec B.cb.cT B.Kc B.wv B.we B.LB B.LE (B.ckd (B.j0 + i)) B.ch0 B.nch
  have hmem : ckPack B.cb.cT B.Kc B.wv B.we B.LB B.LE (B.ckd (B.j0 + i)) B.ch0 B.nch ∈ B.pk := by
    rw [pk_eq]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  exact ⟨le_trans (h8 c hc) ((foldl_max_ge (fun x : PAcc × Bool × ℕ × ℕ => x.2.2.2) B.pk 0).2 _ hmem),
    le_trans (h7 c hc) ((foldl_max_ge (fun x : PAcc × Bool × ℕ × ℕ => x.2.2.1) B.pk 0).2 _ hmem)⟩

theorem Ej_le (i : ℕ) (hi : i < B.nr) : (B.ckd (B.j0 + i)).Ej ≤ B.Ejmax :=
  (foldl_max_ge (fun j => (B.ckd j).Ej) (bjs B.j0 B.nr) 0).2 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem tl_eq : B.tl = (List.range B.n).map (touchV ((List.range B.nr).map fun i => ((B.uI i, B.vI i), B.X i))) := by
  unfold tl btl
  congr 2
  rw [pk_eq]; unfold bjs
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp [uI, vI, X]

theorem G_comb (huv : ∀ i < B.nr, B.uI i < B.n ∧ B.vI i < B.n) (p q : ℕ) :
    IsComb B.nr B.X (B.G p q)
      (fun i => if i < B.nr then sG B.uI B.vI B.wz (B.zrows.getD p 0) (B.zrows.getD q 0) i else 0)
      (fun i => if i < B.nr then aG B.uI B.vI B.wz (B.zrows.getD p 0) (B.zrows.getD q 0) i else 0) := by
  unfold G
  rw [tl_eq]
  exact stage2_comb B.nr B.X (fun i => (B.X_spec i).2.1) (fun i => (B.X_spec i).2.2.2.2) B.uI B.vI B.n B.wz _ _ huv

theorem stage2z_tl (zp zq : ℕ) : stage2z B.wz zp (stage1 B.wz zq B.tl) = stage2 B.wz zp (stage1 B.wz zq B.tl) := by
  rw [tl_eq]
  exact stage2z_stage1 B.nr B.X (fun i => (B.X_spec i).2.1) (fun i => (B.X_spec i).2.2.2.2) B.uI B.vI B.n B.wz zp zq

theorem slotsLe_spec {LS n rs R : ℕ} (h : slotsLe LS n rs R = true) : ∀ p < n, slot LS rs p ≤ slot LS R p := by
  intro p hp
  unfold slotsLe at h
  rw [List.all_eq_true] at h
  have := h p (List.mem_range.mpr hp)
  simpa using this

/-- **One column leaf**: channel bound, the pair facts of its columns, and the partial row sums. -/
theorem leaf_spec (huv : ∀ i < B.nr, B.uI i < B.n ∧ B.vI i < B.n) (hLS : 0 < B.LS)
    {q0 nq : ℕ} {Rp : ℕ → ℕ} {RpE : ℕ} (h : B.leaf q0 nq Rp RpE = true) :
    B.ch0 + B.nch ≤ B.cb.N + 1 ∧ B.FG < B.cb.cT.W ∧ B.zrows.length = B.n ∧
    (∀ q < B.n, q0 ≤ q → q < q0 + nq → ∀ p ≤ q,
      (∀ ch < B.nch, (B.T ch p q).ok = true) ∧ (B.G p q).A * B.cb.cT.twoK < 2 ^ B.LB ∧
        (B.G p q).A * B.emax < 2 ^ B.LE) ∧
    (∀ ch < B.nch, ∀ x < B.n, ∑ q ∈ Finset.range B.n,
      (if q0 ≤ max x q ∧ max x q < q0 + nq then range (B.T ch (min x q) (max x q)) else 0) *
        (B.ws (B.ch0 + ch)).getD q 0 ≤ slot B.LS (Rp (B.ch0 + ch)) x) ∧
    (∀ x < B.n, ∑ q ∈ Finset.range B.n,
      (if q0 ≤ max x q ∧ max x q < q0 + nq then B.HH (min x q) (max x q) else 0) * B.wE.getD q 0 ≤
        slot B.LS RpE x) := by
  rw [leaf_eq] at h
  set res := bfoldQ B.cb.cT B.wz B.FG B.LB B.LE B.LS B.ch0 B.nch B.smax B.okV B.ws B.wE
    (B.zrows.zip (List.range B.n)) (((B.zrows.zip (List.range B.n)).drop q0).take nq) B.tl with hres
  set Tmax := Nat.max (Nat.add (Nat.add B.cb.cT.twoB (Packed.cdiv B.FG (Nat.pow 2 B.LE))) B.cb.cT.m)
    (Packed.cdiv 64 (Nat.mul res.2.2.2 B.Ejmax)) with hTmax
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hok, hFG⟩, hch⟩, hzl, hovB, hovE, hovS⟩, hY, hYE⟩ := h
  set m := min nq (B.n - q0) with hm
  have hnz := zip_range_eq B.zrows B.n hzl
  have hcols := drop_take_zip B.zrows B.n q0 nq hzl
  have hbf := bfoldQ_eq B.cb.cT B.wz B.FG B.LB B.LE B.LS B.ch0 B.nch B.smax B.okV B.ws B.wE
    (B.zrows.zip (List.range B.n)) (((B.zrows.zip (List.range B.n)).drop q0).take nq) B.tl
    (fun zp zq => B.stage2z_tl zp zq)
  rw [hbf] at hres
  obtain ⟨r1, r2, r3, r4, _, r6⟩ := outer_spec B.cb.cT B.FG B.LB B.LE B.LS B.ch0 B.nch B.smax B.okV B.ws B.wE B.wz B.tl
    (B.zrows.zip (List.range B.n)) (((B.zrows.zip (List.range B.n)).drop q0).take nq)
    (List.replicate B.nch 0, 0, true, 0) (by simp)
  rw [← hres] at r1 r2 r3 r4 r6
  rw [hcols, hnz] at r2 r3 r4 r6
  -- membership of the columns of the leaf
  have hmemq : ∀ q < B.n, q0 ≤ q → q < q0 + nq →
      (B.zrows.getD q 0, q) ∈ (List.range m).map fun i => (B.zrows.getD (q0 + i) 0, q0 + i) := by
    intro q hq h0 h1
    refine List.mem_map.mpr ⟨q - q0, List.mem_range.mpr (by omega), ?_⟩
    rw [show q0 + (q - q0) = q by omega]
  have hmemp : ∀ p < B.n, (B.zrows.getD p 0, p) ∈ (List.range B.n).map fun i => (B.zrows.getD i 0, i) :=
    fun p hp => List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩
  have hpair : ∀ q < B.n, q0 ≤ q → q < q0 + nq → ∀ p ≤ q,
      (∀ ch < B.nch, (B.T ch p q).ok = true) ∧ (B.G p q).A ≤ res.2.2.2 := by
    intro q hq h0 h1 p hpq
    refine ⟨fun ch hch => ?_, ?_⟩
    · exact (r4 hok).2 _ (hmemq q hq h0 h1) _ (hmemp p (by omega)) hpq ch hch
    · exact r6 _ (hmemq q hq h0 h1) _ (hmemp p (by omega)) hpq
  -- bounds of the pair values of the leaf
  have hcomb := fun p q => B.G_comb huv p q
  have htT : ∀ ch < B.nch, ∀ q < B.n, q0 ≤ q → q < q0 + nq → ∀ p ≤ q, range (B.T ch p q) ≤ Tmax := by
    intro ch hch q hq h0 h1 p hpq
    have hok' := (hpair q hq h0 h1 p hpq).1 ch hch
    simp only [T, bTs, getD_map_range _ _ _ _ hch] at hok' ⊢
    have hs := zfin_s_lt hok'
    rw [range_eq, zfin_e]
    dsimp only
    have hc1 := cdiv_mono B.FG (slot_lt B.LE (B.G p q).E ch).le
    apply le_trans _ (Nat.le_max_left _ _)
    show _ ≤ B.cb.cT.twoB + Packed.cdiv B.FG (2 ^ B.LE) + B.cb.cT.m
    omega
  have hHT : ∀ q < B.n, q0 ≤ q → q < q0 + nq → ∀ p ≤ q, B.HH p q ≤ Tmax := by
    intro q hq h0 h1 p hpq
    apply le_trans _ (Nat.le_max_right _ _)
    apply cdiv_mono
    rw [(hcomb p q).H]
    calc ∑ i ∈ Finset.range B.nr,
          (if i < B.nr then aG B.uI B.vI B.wz (B.zrows.getD p 0) (B.zrows.getD q 0) i else 0) * (B.X i).H
        ≤ ∑ i ∈ Finset.range B.nr,
          (if i < B.nr then aG B.uI B.vI B.wz (B.zrows.getD p 0) (B.zrows.getD q 0) i else 0) * B.Ejmax :=
          Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (by
            rw [(B.X_spec i).2.2.2.1]; exact B.Ej_le i (Finset.mem_range.mp hi))
      _ = (B.G p q).A * B.Ejmax := by rw [(hcomb p q).A, Finset.sum_mul]
      _ ≤ res.2.2.2 * B.Ejmax := Nat.mul_le_mul_right _ (hpair q hq h0 h1 p hpq).2
  have hwm := wmax_ge B.ws B.wE B.ch0 B.nch
  refine ⟨hch, hFG, hzl, fun q hq h0 h1 p hpq => ⟨(hpair q hq h0 h1 p hpq).1, ?_, ?_⟩, fun ch hch x hx => ?_,
    fun x hx => ?_⟩
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (hpair q hq h0 h1 p hpq).2) hovB
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (hpair q hq h0 h1 p hpq).2) hovE
  · -- control channel `ch`
    have hmem : (res.1.getD ch 0, ch) ∈ res.1.zip (List.range B.nch) := by
      have hl : ch < res.1.length := by rw [r1]; exact hch
      rw [List.mem_iff_getElem]
      exact ⟨ch, by simp [hl, hch], by simp [List.getElem?_eq_getElem hl]⟩
    have hy := slotsLe_spec (hY _ hmem) x hx
    rw [r2 ch hch] at hy
    have h0 : (List.replicate B.nch 0).getD ch 0 = 0 := by rw [getD_of_lt _ _ (by simp [hch])]; simp
    rw [h0, zero_add, List.map_map, list_sum_range'] at hy
    simp only [Function.comp_apply, List.map_map, list_sum_range'] at hy
    have e := cols_sum B.LS B.n q0 nq (fun p q => range (B.T ch p q)) (B.ws (B.ch0 + ch))
    simp only [T, G] at e hy
    rw [e] at hy
    rw [rows_of_rs B.LS B.n Tmax B.wmax hLS _ (B.ws (B.ch0 + ch)) ?_ (hwm.2 ch hch) hovS x hx] at hy
    · simpa [T, G] using hy
    · intro q hq p hpq
      split_ifs with hc
      · exact htT ch hch q hq hc.1 hc.2 p hpq
      · exact Nat.zero_le _
  · -- error part
    have hy := slotsLe_spec hYE x hx
    rw [r3, zero_add, List.map_map, list_sum_range'] at hy
    simp only [Function.comp_apply, List.map_map, list_sum_range'] at hy
    have e := cols_sum B.LS B.n q0 nq (fun p q => B.HH p q) B.wE
    simp only [HH, G] at e hy
    rw [e] at hy
    rw [rows_of_rs B.LS B.n Tmax B.wmax hLS _ B.wE ?_ hwm.1 hovS x hx] at hy
    · simpa [HH, G] using hy
    · intro q hq p hpq
      split_ifs with hc
      · exact hHT q hq hc.1 hc.2 p hpq
      · exact Nat.zero_le _

end BGrp

/-! ## The split block leaves of one channel group -/

/-- the column-split leaves of one channel group: an aggregation leaf and one column leaf per part
(`q0_k = Σ_{i<k} nq_i`) -/
def blockSplitOk (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ)
    (wE : List ℕ) (Geta : ℕ) : Prop :=
  ∃ (nqs : List ℕ) (Rps : List (ℕ → ℕ)) (RpEs : List ℕ), 0 < nqs.length ∧
    blockAggOk cb n FG κC Sc Gc LS ch0 nch nqs Rps RpEs ws Γs wE Geta = true ∧
    ∀ k < nqs.length, blockOkQ cb row Kc wv we ckd j0 nr n wz zrows FG LB LE LS ch0 nch ws wE
      (lsum (nqs.take k)) (nqs.getD k 0) (Rps.getD k fun _ => 0) (RpEs.getD k 0) = true

/-- the conclusions of a block leaf for the control channels `ch0 … ch0+nch-1` (as in `blockOk_sound`) -/
def BlockSound (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc ch0 nch : ℕ) (Γs : ℕ → ℕ) (Geta : ℕ) : Prop :=
  ch0 + nch ≤ cb.N + 1 ∧
  ∀ f : ℕ → ℕ → ℝ → ℝ, (∀ i < nr, ∀ c < nch, Encl cb.cT ((ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c)) (f i c)) →
    (∀ c < nch, ∀ t ∈ Set.Icc (-1 : ℝ) 1, QuadraticBound
      (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) (fun i => f i c t) *
        (zMat n wz zrows).transpose) (2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (Γs (ch0 + c) : ℝ))) ∧
    (∀ c < nch, (Γs (ch0 + c) : ℝ) * 2 ^ ((FG : ℤ) - κC - 64) ≤ (Gc : ℝ) * cb.D * 2 ^ Sc) ∧
    (∀ e : ℕ → ℝ, (∀ i < nr, |e i| ≤ ((ckd (j0 + i)).Ej : ℝ) / 2 ^ 256) → QuadraticBound
      (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) e *
        (zMat n wz zrows).transpose) (1 / 2 ^ 256 * (Geta : ℝ)))

/-- a plain block leaf gives `BlockSound` -/
theorem blockOk_blockSound (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ)
    (wE : List ℕ) (Geta : ℕ)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hLB : 0 < LB) (hLE : 0 < LE) (hLS : 0 < LS)
    (huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n)
    (h : blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true) :
    BlockSound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc ch0 nch Γs Geta := by
  have hch : ch0 + nch ≤ cb.N + 1 := by
    have h' := h
    rw [blockOk_eq] at h'
    dsimp only at h'
    simp only [Bool.and_eq_true, Nat.ble_eq] at h'
    exact h'.1.1.2
  exact ⟨hch, fun f hT => (blockOk_sound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE
    Geta hg hLB hLE hLS huv f hT h).2⟩

theorem youngSum_spec {LS n : ℕ} {Rs w : List ℕ} {Γ : ℕ} (h : youngSum LS n Rs w Γ = true) :
    ∀ p < n, 0 < w.getD p 0 ∧ lsum (Rs.map fun R => slot LS R p) ≤ Γ * w.getD p 0 := by
  intro p hp
  unfold youngSum at h
  rw [List.all_eq_true] at h
  have := h p (List.mem_range.mpr hp)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at this
  exact this

/-- the partial row sums of the column parts add up to the full row sums -/
theorem agg_rows (n : ℕ) (nqs : List ℕ) (hsum : lsum nqs = n) (t : ℕ → ℕ → ℕ) (w : List ℕ) (x : ℕ) (hx : x < n)
    (R : ℕ → ℕ)
    (hk : ∀ k < nqs.length, ∑ q ∈ Finset.range n, (if lsum (nqs.take k) ≤ max x q ∧
        max x q < lsum (nqs.take k) + nqs.getD k 0 then t (min x q) (max x q) else 0) * w.getD q 0 ≤ R k) :
    ∑ q ∈ Finset.range n, t (min x q) (max x q) * w.getD q 0 ≤ ∑ k ∈ Finset.range nqs.length, R k := by
  calc ∑ q ∈ Finset.range n, t (min x q) (max x q) * w.getD q 0
      = ∑ q ∈ Finset.range n, ∑ k ∈ Finset.range nqs.length, (if lsum (nqs.take k) ≤ max x q ∧
          max x q < lsum (nqs.take k) + nqs.getD k 0 then t (min x q) (max x q) else 0) * w.getD q 0 := by
        apply Finset.sum_congr rfl; intro q hq
        have hmq : max x q < lsum nqs := by have := Finset.mem_range.mp hq; omega
        rw [← parts_sum nqs (max x q) (t (min x q) (max x q) * w.getD q 0) hmq]
        apply Finset.sum_congr rfl; intro k _
        split_ifs <;> simp
    _ = ∑ k ∈ Finset.range nqs.length, ∑ q ∈ Finset.range n, (if lsum (nqs.take k) ≤ max x q ∧
          max x q < lsum (nqs.take k) + nqs.getD k 0 then t (min x q) (max x q) else 0) * w.getD q 0 :=
        Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range nqs.length, R k := Finset.sum_le_sum fun k hk' => hk k (Finset.mem_range.mp hk')

/-- **Soundness of the column-split block leaves**: the conclusions of `blockOk_sound` for the channel group. -/
theorem blockSplit_sound (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ)
    (wE : List ℕ) (Geta : ℕ)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hLB : 0 < LB) (hLE : 0 < LE) (hLS : 0 < LS)
    (huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n)
    (h : blockSplitOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta) :
    BlockSound cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc ch0 nch Γs Geta := by
  obtain ⟨nqs, Rps, RpEs, hlen, hagg, hleaves⟩ := h
  set B : BGrp := ⟨cb, row, Kc, wv, we, ckd, j0, nr, n, wz, zrows, FG, LB, LE, LS, ch0, nch, ws, wE⟩ with hB
  have huvB : ∀ i < B.nr, B.uI i < B.n ∧ B.vI i < B.n := huv
  have hL := fun k (hk : k < nqs.length) => B.leaf_spec huvB hLS (q0 := lsum (nqs.take k)) (nq := nqs.getD k 0)
    (Rp := Rps.getD k fun _ => 0) (RpE := RpEs.getD k 0) (hleaves k hk)
  obtain ⟨hch, hFG, hzl, -⟩ := hL 0 hlen
  -- the aggregation leaf
  unfold blockAggOk at hagg
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hagg
  obtain ⟨⟨hsum, hlR, hlRE⟩, hYs, hYE⟩ := hagg
  -- every pair `p ≤ q < n` belongs to the leaf of the part of `q`
  have hP : ∀ q < n, ∀ p ≤ q, (∀ ch < nch, (B.T ch p q).ok = true) ∧ (B.G p q).A * cb.cT.twoK < 2 ^ LB ∧
      (B.G p q).A * B.emax < 2 ^ LE := by
    intro q hq p hpq
    obtain ⟨k, hk, h0, h1⟩ := parts_cover nqs q (by omega)
    exact (hL k hk).2.2.2.1 q hq h0 h1 p hpq
  refine ⟨hch, fun f hT => ?_⟩
  have hTe : ∀ c < nch, ∀ q < n, ∀ p ≤ q, Encl cb.cT (B.T c p q) (fun t => (∑ i ∈ Finset.range nr,
      ((if i < nr then sG B.uI B.vI wz (zrows.getD p 0) (zrows.getD q 0) i else 0 : ℤ) : ℝ) * f i c t) / 2 ^ FG) := by
    intro c hc q hq p hpq
    obtain ⟨hok, hA1, hA2⟩ := hP q hq p hpq
    have hok' := hok c hc
    simp only [BGrp.T, bTs] at hok' ⊢
    rw [getD_map_range _ _ _ _ hc] at hok' ⊢
    exact pair_encl hg (by have : B.FG < 2 * cb.BT + 2 := hFG; omega) nr nch LB LE hLB hLE B.X (fun i c => B.Tc i c) f
      (fun i => (B.X_spec i).1) (fun i => (B.X_spec i).2.2.1) hT _ _ _ (B.G_comb huvB p q) B.smax B.emax
      (fun i hi c hc => (B.Tc_le i hi c hc).1) (fun i hi c hc => (B.Tc_le i hi c hc).2) hA1 hA2 B.okV c hc hok'
  refine ⟨fun c hc t ht => ?_, fun c hc => ?_, fun e he => ?_⟩
  · -- centre channels
    set w := ws (ch0 + c) with hw
    set E := zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) (fun i => f i c t) *
      (zMat n wz zrows).transpose with hE
    have hEe : ∀ p q : Fin n, E p q = (∑ i ∈ Finset.range nr, f i c t *
        (sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)) / 2 ^ 64 :=
      fun p q => congr_entry n nr wz zrows B.uI B.vI huv _ p q
    have hsym : ∀ p q, E p q = E q p := by
      intro p q; rw [hEe, hEe]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [sG_symm]
    have hbd : ∀ q < n, ∀ p ≤ q, |∑ i ∈ Finset.range nr, f i c t *
        (sG B.uI B.vI wz (zrows.getD p 0) (zrows.getD q 0) i : ℝ)| / 2 ^ FG ≤ (range (B.T c p q) : ℝ) / 2 ^ 256 := by
      intro q hq p hpq
      have := range_sound (hTe c hc q hq p hpq) t ht
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ FG)] at this
      have e : ∑ i ∈ Finset.range nr,
          ((if i < nr then sG B.uI B.vI wz (zrows.getD p 0) (zrows.getD q 0) i else 0 : ℤ) : ℝ) * f i c t =
          ∑ i ∈ Finset.range nr, f i c t * (sG B.uI B.vI wz (zrows.getD p 0) (zrows.getD q 0) i : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi
        rw [if_pos (Finset.mem_range.mp hi), mul_comm]
      rw [e] at this
      exact this
    have hyc := (hYs c (List.mem_range.mpr hc))
    apply young_qb E (fun p q => range (B.T c p q)) w (Γs (ch0 + c)) _ (by positivity) hsym
    · intro p q
      have key : ∀ (p q : Fin n), p.val ≤ q.val →
          |E p q| ≤ 2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (range (B.T c p.val q.val) : ℝ) := by
        intro p q hpq
        rw [hEe, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
        have h1 := hbd q.val q.isLt p.val hpq
        have e2 : (2 : ℝ) ^ ((FG : ℤ) - 64) = 2 ^ FG / 2 ^ 64 := by
          rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num
        rw [e2]
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ FG)
        rw [mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ FG ≠ 0)] at h2
        calc |∑ i ∈ Finset.range nr, f i c t * (sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| /
              2 ^ 64
            ≤ (2 ^ FG * ((range (B.T c p.val q.val) : ℝ) / 2 ^ 256)) / 2 ^ 64 :=
              div_le_div_of_nonneg_right h2 (by positivity)
          _ = _ := by ring
      by_cases hpq : p.val ≤ q.val
      · rw [min_eq_left hpq, max_eq_right hpq]; exact key p q hpq
      · have hqp : q.val ≤ p.val := by omega
        rw [min_eq_right hqp, max_eq_left hqp, hsym]; exact key q p hqp
    · intro p hp
      exact (youngSum_spec hyc.1 p hp).1
    · intro p hp
      have hy := (youngSum_spec hyc.1 p hp).2
      rw [List.map_map, lsum_map_getD _ (fun _ => 0)] at hy
      refine le_trans ?_ hy
      rw [hlR]
      refine agg_rows n nqs hsum (fun p q => range (B.T c p q)) w p hp _ (fun k hk => ?_)
      exact (hL k hk).2.2.2.2.1 c hc p hp
  · -- the centre-bound scaling
    have hx := (hYs c (List.mem_range.mpr hc)).2
    have := leShift_real hx
    have e : ((Nat.mul Gc (Nat.shiftLeft cb.D Sc) : ℕ) : ℝ) = (Gc : ℝ) * cb.D * 2 ^ Sc := by
      rw [show Nat.mul Gc (Nat.shiftLeft cb.D Sc) = Gc * (cb.D * 2 ^ Sc) by rw [← Nat.shiftLeft_eq]; rfl]
      push_cast; ring
    rw [e] at this
    exact this
  · -- the error part
    set E := zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) e *
      (zMat n wz zrows).transpose with hE
    have hEe : ∀ p q : Fin n, E p q = (∑ i ∈ Finset.range nr, e i *
        (sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)) / 2 ^ 64 :=
      fun p q => congr_entry n nr wz zrows B.uI B.vI huv _ p q
    have hsym : ∀ p q, E p q = E q p := by
      intro p q; rw [hEe, hEe]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [sG_symm]
    apply young_qb E (fun p q => B.HH p q) wE Geta _ (by positivity) hsym
    · intro p q
      have key : ∀ (p q : Fin n), |E p q| ≤ 1 / 2 ^ 256 * (B.HH p.val q.val : ℝ) := by
        intro p q
        rw [hEe, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
        have hG := B.G_comb huvB p.val q.val
        have hH := hG.H
        have h1 : |∑ i ∈ Finset.range nr, e i * (sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| ≤
            ((B.G p.val q.val).H : ℝ) / 2 ^ 256 := by
          rw [hH, Nat.cast_sum, Finset.sum_div]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
          have hi' := Finset.mem_range.mp hi
          have hi'' : i < B.nr := hi'
          rw [abs_mul]
          have ha := hG.natAbs_le i
          simp only [hi'', if_true] at ha
          have ha' : |(sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| ≤
              (aG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ) := by
            rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast ha
          rw [if_pos hi'', (B.X_spec i).2.2.2.1]
          push_cast
          calc |e i| * |(sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)|
              ≤ ((ckd (j0 + i)).Ej : ℝ) / 2 ^ 256 *
                  (aG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ) :=
                mul_le_mul (he i hi') ha' (abs_nonneg _) (by positivity)
            _ = _ := by ring
        have h2 := le_cdiv 64 (B.G p.val q.val).H
        calc |∑ i ∈ Finset.range nr, e i * (sG B.uI B.vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| / 2 ^ 64
            ≤ ((B.G p.val q.val).H : ℝ) / 2 ^ 256 / 2 ^ 64 := div_le_div_of_nonneg_right h1 (by positivity)
          _ = ((B.G p.val q.val).H : ℝ) / 2 ^ 64 / 2 ^ 256 := by ring
          _ ≤ (B.HH p.val q.val : ℝ) / 2 ^ 256 := div_le_div_of_nonneg_right h2 (by positivity)
          _ = _ := by ring
      by_cases hpq : p.val ≤ q.val
      · rw [min_eq_left hpq, max_eq_right hpq]; exact key p q
      · have hqp : q.val ≤ p.val := by omega
        rw [min_eq_right hqp, max_eq_left hqp, hsym]; exact key q p
    · intro p hp; exact (youngSum_spec hYE p hp).1
    · intro p hp
      have hy := (youngSum_spec hYE p hp).2
      rw [lsum_map_getD _ 0] at hy
      refine le_trans ?_ hy
      rw [hlRE]
      exact agg_rows n nqs hsum (fun p q => B.HH p q) wE p hp _ (fun k hk => (hL k hk).2.2.2.2.2 p hp)

end ThomsonCompact.Floor.B
