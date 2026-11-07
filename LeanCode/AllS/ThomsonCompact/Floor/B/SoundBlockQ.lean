import ThomsonCompact.Floor.B.SoundBlock
import AllS.Units.N_AI.N_correction_bounds.N_weighted_quadratic

/-!
# Block leaf: quadratic bounds (F3b)

`blockOk_sound`: for every control channel of the leaf and every point of the height box, the congruence
`Z M(f) Zᵀ` of the block insertion of the checkpoint functions has the quadratic bound `Γ 2^(FG-64) 2^-256`
(weighted Young with the data weights); `Γ 2^(FG-κC-64) ≤ Gc D 2^Sc`; the congruence of any vector bounded by the
error claims `Ẽ_j 2^-256` has the bound `Geta 2^-256`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open Blueprint.CAP
open scoped BigOperators

/-! ## Matrices -/

/-- `Z = Zi 2^-32` with rows `zrows` (sign-magnitude slots of width `wz`) -/
noncomputable def zMat (n wz : ℕ) (zrows : List ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p a => (zv wz (zrows.getD p.val 0) a.val : ℝ) / 2 ^ 32

/-- the block insertion of a vector `w` over the rows `i < nr` with coordinates `(uI i, vI i)` -/
noncomputable def insM (n nr : ℕ) (uI vI : ℕ → ℕ) (w : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => ∑ i ∈ Finset.range nr,
    w i * (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0)

theorem double_sum_point {n : ℕ} (f g : Fin n → ℝ) (u v : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n, f a * (if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0) * g b =
      f u * g v + (if u ≠ v then f v * g u else 0) := by
  by_cases huv : u = v
  · subst huv
    have : ∀ a b : Fin n, f a * (if (a = u ∧ b = u) ∨ (a = u ∧ b = u) then (1 : ℝ) else 0) * g b =
        if b = u then (if a = u then f a * g b else 0) else 0 := by
      intro a b; by_cases ha : a = u <;> by_cases hb : b = u <;> simp [ha, hb]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, ne_eq, not_true_eq_false, if_false, add_zero]
  · have : ∀ a b : Fin n, f a * (if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then (1 : ℝ) else 0) * g b =
        (if b = v then (if a = u then f a * g b else 0) else 0) +
          (if b = u then (if a = v then f a * g b else 0) else 0) := by
      intro a b
      by_cases ha : a = u
      · subst ha
        have hav : ¬ a = v := huv
        by_cases hb : b = v
        · subst hb; simp [hav, Ne.symm hav]
        · by_cases hb' : b = a <;> simp [hb, hb', hav]
      · by_cases ha' : a = v
        · subst ha'
          by_cases hb : b = u
          · subst hb; simp [ha]
          · simp [hb, ha]
        · by_cases hb : b = v <;> by_cases hb' : b = u <;> simp [ha, ha', hb, hb']
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [huv]

/-- `(Z M(w) Zᵀ)_pq = 2^-64 Σ_i w_i sG_pq(i)` -/
theorem congr_entry (n nr wz : ℕ) (zrows : List ℕ) (uI vI : ℕ → ℕ) (huv : ∀ i < nr, uI i < n ∧ vI i < n)
    (w : ℕ → ℝ) (p q : Fin n) :
    (zMat n wz zrows * insM n nr uI vI w * (zMat n wz zrows).transpose) p q =
      (∑ i ∈ Finset.range nr, w i * (sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)) / 2 ^ 64 := by
  set Z := zMat n wz zrows with hZ
  have e1 : (Z * insM n nr uI vI w * Z.transpose) p q =
      ∑ i ∈ Finset.range nr, w i * ∑ a : Fin n, ∑ b : Fin n, Z p a *
        (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0) * Z q b := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, insM, Matrix.of_apply]
    calc ∑ b : Fin n, (∑ a : Fin n, Z p a * ∑ i ∈ Finset.range nr, w i *
            (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0)) * Z q b
        = ∑ b : Fin n, ∑ a : Fin n, ∑ i ∈ Finset.range nr, w i * (Z p a *
            (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0) * Z q b) := by
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ i ∈ Finset.range nr, w i * (Z p a *
            (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0) * Z q b) :=
          Finset.sum_comm
      _ = ∑ a : Fin n, ∑ i ∈ Finset.range nr, ∑ b : Fin n, w i * (Z p a *
            (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0) * Z q b) := by
          apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
      _ = ∑ i ∈ Finset.range nr, ∑ a : Fin n, ∑ b : Fin n, w i * (Z p a *
            (if (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i) then 1 else 0) * Z q b) :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
  rw [e1, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hu, hv⟩ := huv i (Finset.mem_range.mp hi)
  set u : Fin n := ⟨uI i, hu⟩
  set v : Fin n := ⟨vI i, hv⟩
  have hind : ∀ a b : Fin n, ((a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i)) ↔
      ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
    intro a b; simp only [u, v, Fin.ext_iff]
  simp only [hind]
  rw [double_sum_point (fun a => Z p a) (fun b => Z q b) u v]
  simp only [hZ, zMat, Matrix.of_apply, u, v, sG]
  have huv' : (u ≠ v) ↔ (uI i ≠ vI i) := by simp [u, v, Fin.ext_iff]
  by_cases h : uI i = vI i
  · have h' : ¬ (u ≠ v) := by rw [huv']; exact not_not.mpr h
    simp only [ne_eq, Fin.mk.injEq, h, not_true_eq_false, if_false, add_zero]
    push_cast; ring
  · simp only [ne_eq, Fin.mk.injEq, h, not_false_eq_true, if_true]
    push_cast; ring

theorem sG_symm (uI vI : ℕ → ℕ) (wz zp zq i : ℕ) : sG uI vI wz zp zq i = sG uI vI wz zq zp i := by
  unfold sG
  by_cases h : uI i = vI i
  · simp [h, mul_comm]
  · simp [h]; ring

/-! ## Weighted Young -/

theorem young_qb {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) (t : ℕ → ℕ → ℕ) (w : List ℕ) (Γ : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hsym : ∀ i j, E i j = E j i)
    (hE : ∀ i j : Fin n, |E i j| ≤ κ * t (min i.val j.val) (max i.val j.val))
    (hw : ∀ p < n, 0 < w.getD p 0)
    (hrow : ∀ p < n, ∑ q ∈ Finset.range n, t (min p q) (max p q) * w.getD q 0 ≤ Γ * w.getD p 0) :
    QuadraticBound E (κ * Γ) := by
  apply correction_bounds_weighted_quadratic E (fun i j => κ * t (min i.val j.val) (max i.val j.val))
    (fun i => (w.getD i.val 0 : ℝ)) (κ * Γ) hsym
  · intro i j; simp [min_comm, max_comm]
  · intro i j; positivity
  · exact hE
  · intro i; exact_mod_cast hw i.val i.isLt
  · positivity
  · intro i
    have hwi : (0 : ℝ) < w.getD i.val 0 := by exact_mod_cast hw i.val i.isLt
    have h := hrow i.val i.isLt
    have h' : (∑ q ∈ Finset.range n, ((t (min i.val q) (max i.val q) * w.getD q 0 : ℕ) : ℝ)) ≤
        ((Γ * w.getD i.val 0 : ℕ) : ℝ) := by exact_mod_cast h
    rw [← Fin.sum_univ_eq_sum_range (fun q => ((t (min i.val q) (max i.val q) * w.getD q 0 : ℕ) : ℝ))] at h'
    rw [← Finset.sum_div, div_le_iff₀ hwi]
    calc ∑ j : Fin n, κ * (t (min i.val j.val) (max i.val j.val) : ℝ) * (w.getD j.val 0 : ℝ)
        = κ * ∑ j : Fin n, ((t (min i.val j.val) (max i.val j.val) * w.getD j.val 0 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; push_cast; ring
      _ ≤ κ * ((Γ * w.getD i.val 0 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h' hκ.le
      _ = κ * Γ * w.getD i.val 0 := by push_cast; ring

/-! ## Small facts about the kernel's maxima and bounds -/

theorem cdiv_mono (S : ℕ) {x y : ℕ} (h : x ≤ y) : Packed.cdiv S x ≤ Packed.cdiv S y := by
  show (x + (2 ^ S - 1)) >>> S ≤ (y + (2 ^ S - 1)) >>> S
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_div_right (by omega)

theorem foldl_nmax_ge : ∀ (l : List ℕ) (m : ℕ), m ≤ l.foldl Nat.max m ∧ ∀ x ∈ l, x ≤ l.foldl Nat.max m
  | [], m => ⟨le_rfl, by simp⟩
  | y :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_nmax_ge l (Nat.max m y)
    refine ⟨le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

theorem getD_le_foldl_max (l : List ℕ) (m q : ℕ) : l.getD q 0 ≤ l.foldl Nat.max m := by
  by_cases h : q < l.length
  · rw [getD_of_lt _ _ h]; exact (foldl_nmax_ge l m).2 _ (List.getElem_mem h)
  · rw [getD_of_ge _ _ (by omega)]; exact Nat.zero_le _

/-- the kernel's `wmax` bounds all weights -/
theorem wmax_ge (ws : ℕ → List ℕ) (wE : List ℕ) (ch0 : ℕ) : ∀ (nch : ℕ),
    (∀ q, wE.getD q 0 ≤ (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0)) ∧
    (∀ c < nch, ∀ q, (ws (ch0 + c)).getD q 0 ≤
      (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0))
  | 0 => ⟨fun q => getD_le_foldl_max wE 0 q, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | nch + 1 => by
    obtain ⟨h1, h2⟩ := wmax_ge ws wE ch0 nch
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set M := (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0)
    have hM : M ≤ (ws (Nat.add ch0 nch)).foldl Nat.max M := (foldl_nmax_ge _ M).1
    refine ⟨fun q => le_trans (h1 q) hM, fun c hc q => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · exact le_trans (h2 c hc q) hM
    · exact getD_le_foldl_max _ M q

theorem slot_lt (w x i : ℕ) : slot w x i < 2 ^ w := by
  rw [slot_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## The block leaf -/

noncomputable def bjs (j0 nr : ℕ) : List ℕ := (List.range nr).map (Nat.add j0)

noncomputable def bpk (c : Ctx) (Kc wv we LB LE : ℕ) (ckd : ℕ → CkRow) (j0 nr ch0 nch : ℕ) :
    List (PAcc × Bool × ℕ × ℕ) :=
  (bjs j0 nr).map fun j => ckPack c Kc wv we LB LE (ckd j) ch0 nch

noncomputable def btl (row : ℕ → RowT) (pk : List (PAcc × Bool × ℕ × ℕ)) (j0 nr n : ℕ) : List (List (ℕ × PAcc)) :=
  (List.range n).map (touchV (((bjs j0 nr).zip pk).map fun x => (((row x.1).u, (row x.1).v), x.2.1)))

theorem blockOk_eq (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ)
    (wE : List ℕ) (Geta : ℕ) :
    blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta =
      (let pk := bpk cb.cT Kc wv we LB LE ckd j0 nr ch0 nch
       let okV := pk.all fun x => x.2.1
       let emax := pk.foldl (fun m x => Nat.max m x.2.2.1) 0
       let smax := pk.foldl (fun m x => Nat.max m x.2.2.2) 0
       let Ejmax := (bjs j0 nr).foldl (fun m j => Nat.max m (ckd j).Ej) 0
       let res := bres cb.cT wz FG LB LE LS ch0 nch smax okV ws wE zrows n (btl row pk j0 nr n)
       let tzmax := res.2.2.2
       let Tmax := Nat.max (Nat.add (Nat.add cb.cT.twoB (Packed.cdiv FG (Nat.pow 2 LE))) cb.cT.m)
         (Packed.cdiv 64 (Nat.mul tzmax Ejmax))
       let wmax := (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0)
       let Dc := Nat.shiftLeft cb.D Sc
       let ex : Int := (FG : Int) - κC - 64
       and (and (and (and res.2.2.1 (Nat.blt FG cb.cT.W)) (Nat.ble (Nat.add ch0 nch) (Nat.succ cb.N)))
          (and (Nat.beq zrows.length n)
            (and (Nat.blt (Nat.mul tzmax cb.cT.twoK) (Nat.pow 2 LB))
              (and (Nat.blt (Nat.mul tzmax emax) (Nat.pow 2 LE))
                (Nat.blt (Nat.mul (Nat.mul (Nat.mul n Tmax) wmax) 2) (Nat.pow 2 LS))))))
        (and ((res.1.zip (List.range nch)).all fun x =>
          and (youngChk LS n x.1 (ws (Nat.add ch0 x.2)) (Γs (Nat.add ch0 x.2)))
            (leShift (Γs (Nat.add ch0 x.2)) (Nat.mul Gc Dc) ex))
          (youngChk LS n res.2.1 wE Geta))) := rfl

theorem range_eq (A : TM) : range A = A.s + A.e := rfl

theorem zfin_e (c : Ctx) (F : ℕ) (r : ℕ × ℕ × ℕ × ℕ × Bool) : (zfin c F r).e = Packed.cdiv F r.2.2.2.1 + c.m := rfl

theorem zfin_s_lt {c : Ctx} {F : ℕ} {r : ℕ × ℕ × ℕ × ℕ × Bool} (h : (zfin c F r).ok = true) :
    (zfin c F r).s < c.twoB := by
  have h' : (r.2.2.2.2 && Nat.blt r.2.2.1 (Nat.pow 2 (Nat.mul 2 c.B)) && Nat.blt (zfin c F r).s c.twoB) = true := h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h'
  exact h'.2

theorem youngChk_spec {LS n rs : ℕ} {w : List ℕ} {Γ : ℕ} (h : youngChk LS n rs w Γ = true) :
    ∀ p < n, 0 < w.getD p 0 ∧ slot LS rs p ≤ Γ * w.getD p 0 := by
  intro p hp
  unfold youngChk at h
  rw [List.all_eq_true] at h
  have := h p (List.mem_range.mpr hp)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at this
  exact this

/-- row sums of the packed accumulators -/
theorem rows_of_rs (LS n Tm wm : ℕ) (hLS : 0 < LS) (t : ℕ → ℕ → ℕ) (w : List ℕ)
    (ht : ∀ q < n, ∀ p ≤ q, t p q ≤ Tm) (hw : ∀ q, w.getD q 0 ≤ wm) (hov : n * Tm * wm * 2 < 2 ^ LS) (p : ℕ) (hp : p < n) :
    slot LS (∑ q ∈ Finset.range n, ∑ p ∈ Finset.range n, (if p ≤ q then rsT LS p q (t p q) w else 0)) p =
      ∑ q ∈ Finset.range n, t (min p q) (max p q) * w.getD q 0 := by
  rw [rs_rearrange]
  apply slot_rows hLS n _ _ p hp
  intro p' hp'
  calc ∑ q ∈ Finset.range n, t (min p' q) (max p' q) * w.getD q 0 ≤ ∑ _q ∈ Finset.range n, Tm * wm :=
        Finset.sum_le_sum fun q hq => Nat.mul_le_mul
          (ht _ (by have := Finset.mem_range.mp hq; omega) _ (min_le_max)) (hw q)
    _ = n * Tm * wm := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
    _ < 2 ^ LS := by omega

/-- **Block leaf soundness.** -/
theorem blockOk_sound (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG : ℕ) (κC : ℤ) (Sc Gc LB LE LS ch0 nch : ℕ) (ws : ℕ → List ℕ) (Γs : ℕ → ℕ)
    (wE : List ℕ) (Geta : ℕ)
    (hg : Good cb.Kt 256 cb.BT (2 * cb.BT + 2)) (hLB : 0 < LB) (hLE : 0 < LE) (hLS : 0 < LS)
    (huv : ∀ i < nr, (row (j0 + i)).u < n ∧ (row (j0 + i)).v < n)
    (f : ℕ → ℕ → ℝ → ℝ)
    (hT : ∀ i < nr, ∀ c < nch, Encl cb.cT ((ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c)) (f i c))
    (h : blockOk cb row Kc wv we ckd j0 nr n wz zrows FG κC Sc Gc LB LE LS ch0 nch ws Γs wE Geta = true) :
    ch0 + nch ≤ cb.N + 1 ∧
    (∀ c < nch, ∀ t ∈ Set.Icc (-1 : ℝ) 1, QuadraticBound
      (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) (fun i => f i c t) *
        (zMat n wz zrows).transpose) (2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (Γs (ch0 + c) : ℝ))) ∧
    (∀ c < nch, (Γs (ch0 + c) : ℝ) * 2 ^ ((FG : ℤ) - κC - 64) ≤ (Gc : ℝ) * cb.D * 2 ^ Sc) ∧
    (∀ e : ℕ → ℝ, (∀ i < nr, |e i| ≤ ((ckd (j0 + i)).Ej : ℝ) / 2 ^ 256) → QuadraticBound
      (zMat n wz zrows * insM n nr (fun i => (row (j0 + i)).u) (fun i => (row (j0 + i)).v) e *
        (zMat n wz zrows).transpose) (1 / 2 ^ 256 * (Geta : ℝ))) := by
  have hcT : cb.cT = mkCtx cb.Kt 256 cb.BT (2 * cb.BT + 2) := rfl
  rw [blockOk_eq] at h
  set pk := bpk cb.cT Kc wv we LB LE ckd j0 nr ch0 nch with hpk
  set okV := pk.all fun x => x.2.1 with hokV
  set emax := pk.foldl (fun m x => Nat.max m x.2.2.1) 0 with hemax
  set smax := pk.foldl (fun m x => Nat.max m x.2.2.2) 0 with hsmax
  set Ejmax := (bjs j0 nr).foldl (fun m j => Nat.max m (ckd j).Ej) 0 with hEjmax
  set tl := btl row pk j0 nr n with htl
  set res := bres cb.cT wz FG LB LE LS ch0 nch smax okV ws wE zrows n tl with hres
  set Tmax := Nat.max (Nat.add (Nat.add cb.cT.twoB (Packed.cdiv FG (Nat.pow 2 LE))) cb.cT.m)
    (Packed.cdiv 64 (Nat.mul res.2.2.2 Ejmax)) with hTmax
  set wmax := (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0) with hwmax
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hok, hFG⟩, hch⟩, hzl, hovB, hovE, hovS⟩, hY, hYE⟩ := h
  -- rows and payloads
  set uI := fun i => (row (j0 + i)).u with huI
  set vI := fun i => (row (j0 + i)).v with hvI
  set X := fun i => (ckPack cb.cT Kc wv we LB LE (ckd (j0 + i)) ch0 nch).1 with hX
  set Tc := fun i c => (ckd (j0 + i)).tm cb.cT Kc wv we (ch0 + c) with hTc
  have hpk' : pk = (List.range nr).map fun i => ckPack cb.cT Kc wv we LB LE (ckd (j0 + i)) ch0 nch := by
    rw [hpk]; unfold bpk bjs; rw [List.map_map]; rfl
  have hXs : ∀ i, (X i).P = ∑ c ∈ Finset.range nch, (Tc i c).v * 2 ^ (LB * c) ∧ (X i).Q = 0 ∧
      (X i).E = ∑ c ∈ Finset.range nch, (Tc i c).e * 2 ^ (LE * c) ∧ (X i).H = (ckd (j0 + i)).Ej ∧ (X i).A = 1 := by
    intro i
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := ckPack_spec cb.cT Kc wv we LB LE (ckd (j0 + i)) ch0 nch
    exact ⟨h1, h2, h3, h4, h5⟩
  have hsm : ∀ i < nr, ∀ c < nch, (Tc i c).s ≤ smax ∧ (Tc i c).e ≤ emax := by
    intro i hi c hc
    obtain ⟨_, _, _, _, _, _, h7, h8⟩ := ckPack_spec cb.cT Kc wv we LB LE (ckd (j0 + i)) ch0 nch
    have hmem : ckPack cb.cT Kc wv we LB LE (ckd (j0 + i)) ch0 nch ∈ pk := by
      rw [hpk']; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    exact ⟨le_trans (h8 c hc) ((foldl_max_ge (fun x : PAcc × Bool × ℕ × ℕ => x.2.2.2) pk 0).2 _ hmem),
      le_trans (h7 c hc) ((foldl_max_ge (fun x : PAcc × Bool × ℕ × ℕ => x.2.2.1) pk 0).2 _ hmem)⟩
  have hEj : ∀ i < nr, (ckd (j0 + i)).Ej ≤ Ejmax := by
    intro i hi
    exact (foldl_max_ge (fun j => (ckd j).Ej) (bjs j0 nr) 0).2 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have htl' : tl = (List.range n).map (touchV ((List.range nr).map fun i => ((uI i, vI i), X i))) := by
    rw [htl]; unfold btl
    congr 2
    rw [hpk']; unfold bjs
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [huI, hvI, hX]
  have hcomb : ∀ p q, IsComb nr X (stage2 wz (zrows.getD p 0) (stage1 wz (zrows.getD q 0) tl))
      (fun i => if i < nr then sG uI vI wz (zrows.getD p 0) (zrows.getD q 0) i else 0)
      (fun i => if i < nr then aG uI vI wz (zrows.getD p 0) (zrows.getD q 0) i else 0) := by
    intro p q
    rw [htl']
    exact stage2_comb nr X (fun i => (hXs i).2.1) (fun i => (hXs i).2.2.2.2) uI vI n wz _ _ huv
  obtain ⟨r1, r2, r3, r4, r5⟩ := bres_spec cb.cT wz FG LB LE LS ch0 nch smax okV ws wE zrows n tl hzl
  have hGA : ∀ q < n, ∀ p ≤ q, (stage2 wz (zrows.getD p 0) (stage1 wz (zrows.getD q 0) tl)).A * 2 ^ ((2 * cb.BT + 2) * (2 * cb.Kt + 1)) < 2 ^ LB ∧
      (stage2 wz (zrows.getD p 0) (stage1 wz (zrows.getD q 0) tl)).A * emax < 2 ^ LE := by
    intro q hq p hpq
    have := r5 q hq p hpq
    exact ⟨lt_of_le_of_lt (Nat.mul_le_mul_right _ this) hovB, lt_of_le_of_lt (Nat.mul_le_mul_right _ this) hovE⟩
  have hwm := wmax_ge ws wE ch0 nch
  have hmem : ∀ c < nch, (res.1.getD c 0, c) ∈ res.1.zip (List.range nch) := by
    intro c hc
    have hl : c < res.1.length := by rw [r1]; exact hc
    rw [List.mem_iff_getElem]
    exact ⟨c, by simp [hl, hc], by simp [List.getElem?_eq_getElem hl]⟩
  refine ⟨hch, ?_, ?_, ?_⟩
  · -- centre channels
    intro c hc t ht
    set w := ws (ch0 + c) with hw
    set TT := fun p q => (bTs cb.cT FG LB LE nch smax okV (stage2 wz (zrows.getD p 0) (stage1 wz (zrows.getD q 0) tl))).getD c zeroTM with hTT
    have hTTe : ∀ q < n, ∀ p ≤ q, Encl cb.cT (TT p q) (fun t => (∑ i ∈ Finset.range nr,
        ((if i < nr then sG uI vI wz (zrows.getD p 0) (zrows.getD q 0) i else 0 : ℤ) : ℝ) * f i c t) / 2 ^ FG) := by
      intro q hq p hpq
      have hok' := r4 hok q hq p hpq c hc
      simp only [hTT, bTs, getD_map_range _ _ _ _ hc] at hok' ⊢
      exact pair_encl hg (by have : FG < 2 * cb.BT + 2 := hFG; omega) nr nch LB LE hLB hLE X Tc f (fun i => (hXs i).1) (fun i => (hXs i).2.2.1)
        hT _ _ _ (hcomb p q) smax emax (fun i hi c hc => (hsm i hi c hc).1) (fun i hi c hc => (hsm i hi c hc).2)
        (hGA q hq p hpq).1 (hGA q hq p hpq).2 okV c hc hok'
    set E := zMat n wz zrows * insM n nr uI vI (fun i => f i c t) * (zMat n wz zrows).transpose with hE
    have hEe : ∀ p q : Fin n, E p q = (∑ i ∈ Finset.range nr, f i c t *
        (sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)) / 2 ^ 64 :=
      fun p q => congr_entry n nr wz zrows uI vI huv _ p q
    have hsym : ∀ p q, E p q = E q p := by
      intro p q; rw [hEe, hEe]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [sG_symm]
    have hbd : ∀ q < n, ∀ p ≤ q, |∑ i ∈ Finset.range nr, f i c t *
        (sG uI vI wz (zrows.getD p 0) (zrows.getD q 0) i : ℝ)| / 2 ^ FG ≤ (range (TT p q) : ℝ) / 2 ^ 256 := by
      intro q hq p hpq
      have := range_sound (hTTe q hq p hpq) t ht
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ FG)] at this
      have e : ∑ i ∈ Finset.range nr,
          ((if i < nr then sG uI vI wz (zrows.getD p 0) (zrows.getD q 0) i else 0 : ℤ) : ℝ) * f i c t =
          ∑ i ∈ Finset.range nr, f i c t * (sG uI vI wz (zrows.getD p 0) (zrows.getD q 0) i : ℝ) := by
        apply Finset.sum_congr rfl; intro i hi
        rw [if_pos (Finset.mem_range.mp hi), mul_comm]
      rw [e] at this
      exact this
    apply young_qb E (fun p q => range (TT p q)) w (Γs (ch0 + c)) _ (by positivity) hsym
    · intro p q
      have key : ∀ (p q : Fin n), p.val ≤ q.val → |E p q| ≤ 2 ^ ((FG : ℤ) - 64) / 2 ^ 256 * (range (TT p.val q.val) : ℝ) := by
        intro p q hpq
        rw [hEe, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
        have h1 := hbd q.val q.isLt p.val hpq
        have e2 : (2 : ℝ) ^ ((FG : ℤ) - 64) = 2 ^ FG / 2 ^ 64 := by
          rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num
        rw [e2]
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 ^ FG)
        rw [mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ FG ≠ 0)] at h2
        calc |∑ i ∈ Finset.range nr, f i c t * (sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| / 2 ^ 64
            ≤ (2 ^ FG * ((range (TT p.val q.val) : ℝ) / 2 ^ 256)) / 2 ^ 64 :=
              div_le_div_of_nonneg_right h2 (by positivity)
          _ = _ := by ring
      by_cases hpq : p.val ≤ q.val
      · rw [min_eq_left hpq, max_eq_right hpq]; exact key p q hpq
      · have hqp : q.val ≤ p.val := by omega
        rw [min_eq_right hqp, max_eq_left hqp, hsym]; exact key q p hqp
    · intro p hp
      have hx := hY (res.1.getD c 0, c) (hmem c hc)
      exact (youngChk_spec hx.1 p hp).1
    · intro p hp
      have hx := hY (res.1.getD c 0, c) (hmem c hc)
      have hyc := (youngChk_spec hx.1 p hp).2
      rw [r2 c hc] at hyc
      rw [rows_of_rs LS n Tmax wmax hLS (fun p q => range (TT p q)) w ?_ (hwm.2 c hc) hovS p hp] at hyc
      · exact hyc
      · intro q hq p' hpq
        have hok' := r4 hok q hq p' hpq c hc
        simp only [hTT, bTs, getD_map_range _ _ _ _ hc] at hok' ⊢
        have hs := zfin_s_lt hok'
        rw [range_eq, zfin_e]
        dsimp only
        have hc1 := cdiv_mono FG (slot_lt LE (stage2 wz (zrows.getD p' 0) (stage1 wz (zrows.getD q 0) tl)).E c).le
        apply le_trans _ (Nat.le_max_left _ _)
        show _ ≤ cb.cT.twoB + Packed.cdiv FG (2 ^ LE) + cb.cT.m
        omega
  · -- the centre-bound scaling
    intro c hc
    have hx := hY (res.1.getD c 0, c) (hmem c hc)
    have := leShift_real hx.2
    have e : ((Nat.mul Gc (Nat.shiftLeft cb.D Sc) : ℕ) : ℝ) = (Gc : ℝ) * cb.D * 2 ^ Sc := by
      rw [show Nat.mul Gc (Nat.shiftLeft cb.D Sc) = Gc * (cb.D * 2 ^ Sc) by rw [← Nat.shiftLeft_eq]; rfl]
      push_cast; ring
    rw [e] at this
    exact this
  · -- the error part
    intro e he
    set E := zMat n wz zrows * insM n nr uI vI e * (zMat n wz zrows).transpose with hE
    have hEe : ∀ p q : Fin n, E p q = (∑ i ∈ Finset.range nr, e i *
        (sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)) / 2 ^ 64 :=
      fun p q => congr_entry n nr wz zrows uI vI huv _ p q
    have hsym : ∀ p q, E p q = E q p := by
      intro p q; rw [hEe, hEe]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [sG_symm]
    set HH := fun p q => Packed.cdiv 64 (stage2 wz (zrows.getD p 0) (stage1 wz (zrows.getD q 0) tl)).H with hHH
    apply young_qb E HH wE Geta _ (by positivity) hsym
    · intro p q
      have key : ∀ (p q : Fin n), |E p q| ≤ 1 / 2 ^ 256 * (HH p.val q.val : ℝ) := by
        intro p q
        rw [hEe, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
        have hG := hcomb p.val q.val
        have hH := hG.H
        have h1 : |∑ i ∈ Finset.range nr, e i * (sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| ≤
            ((stage2 wz (zrows.getD p.val 0) (stage1 wz (zrows.getD q.val 0) tl)).H : ℝ) / 2 ^ 256 := by
          rw [hH, Nat.cast_sum, Finset.sum_div]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
          have hi' := Finset.mem_range.mp hi
          rw [abs_mul]
          have ha := hG.natAbs_le i
          simp only [hi', if_true] at ha
          have ha' : |(sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| ≤
              (aG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ) := by
            rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast ha
          rw [if_pos hi', (hXs i).2.2.2.1]
          push_cast
          calc |e i| * |(sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)|
              ≤ ((ckd (j0 + i)).Ej : ℝ) / 2 ^ 256 * (aG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ) :=
                mul_le_mul (he i hi') ha' (abs_nonneg _) (by positivity)
            _ = _ := by ring
        have h2 := le_cdiv 64 (stage2 wz (zrows.getD p.val 0) (stage1 wz (zrows.getD q.val 0) tl)).H
        calc |∑ i ∈ Finset.range nr, e i * (sG uI vI wz (zrows.getD p.val 0) (zrows.getD q.val 0) i : ℝ)| / 2 ^ 64
            ≤ ((stage2 wz (zrows.getD p.val 0) (stage1 wz (zrows.getD q.val 0) tl)).H : ℝ) / 2 ^ 256 / 2 ^ 64 :=
              div_le_div_of_nonneg_right h1 (by positivity)
          _ = ((stage2 wz (zrows.getD p.val 0) (stage1 wz (zrows.getD q.val 0) tl)).H : ℝ) / 2 ^ 64 / 2 ^ 256 := by ring
          _ ≤ (HH p.val q.val : ℝ) / 2 ^ 256 := div_le_div_of_nonneg_right h2 (by positivity)
          _ = _ := by ring
      by_cases hpq : p.val ≤ q.val
      · rw [min_eq_left hpq, max_eq_right hpq]; exact key p q
      · have hqp : q.val ≤ p.val := by omega
        rw [min_eq_right hqp, max_eq_left hqp, hsym]; exact key q p
    · intro p hp; exact (youngChk_spec hYE p hp).1
    · intro p hp
      have hyc := (youngChk_spec hYE p hp).2
      rw [r3] at hyc
      rw [rows_of_rs LS n Tmax wmax hLS HH wE ?_ hwm.1 hovS p hp] at hyc
      · exact hyc
      · intro q hq p' hpq
        apply le_trans _ (Nat.le_max_right _ _)
        apply cdiv_mono
        have hG := hcomb p' q
        rw [hG.H]
        calc ∑ i ∈ Finset.range nr, (if i < nr then aG uI vI wz (zrows.getD p' 0) (zrows.getD q 0) i else 0) * (X i).H
            ≤ ∑ i ∈ Finset.range nr, (if i < nr then aG uI vI wz (zrows.getD p' 0) (zrows.getD q 0) i else 0) * Ejmax :=
              Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (by
                rw [(hXs i).2.2.2.1]; exact hEj i (Finset.mem_range.mp hi))
          _ = (stage2 wz (zrows.getD p' 0) (stage1 wz (zrows.getD q 0) tl)).A * Ejmax := by rw [hG.A, Finset.sum_mul]
          _ ≤ res.2.2.2 * Ejmax := Nat.mul_le_mul_right _ (r5 q hq p' hpq)

end ThomsonCompact.Floor.B
