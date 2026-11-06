import ThomsonCompact.Fixed.Sound

/-!
# Soundness of the fixed-table kernel, part 2: the leaf loop (workstream F4)

`leafOk_sound`: if a leaf check passes (and the one-time `tabOk`), then for every row `r < n` and every slice
position `p < len`

  `Σ_{g ∈ Γ list} sv g · lk (N column g.idx) r · lk (H slice row g.idx) (i0 + p) = [r = i0 + p] · sQ(B)`,

where `lk l i` is the (signed) value of index `i` in the sparse list `l` (zero if absent).
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-! ## Sparse lists -/

/-- Value of index `i` in a sparse list. -/
def lk (l : List (Nat × Bool × Nat)) (i : Nat) : ℤ := (l.map fun e => if e.1 = i then sv e.2 else 0).sum

@[simp] theorem lk_nil (i : Nat) : lk [] i = 0 := rfl

theorem lk_cons (e : Nat × Bool × Nat) (es : List (Nat × Bool × Nat)) (i : Nat) :
    lk (e :: es) i = (if e.1 = i then sv e.2 else 0) + lk es i := by
  simp [lk]

/-- Indices strictly increasing and `≥ lo`. -/
def Inc : Nat → List (Nat × Bool × Nat) → Prop
  | _, [] => True
  | lo, e :: es => lo ≤ e.1 ∧ Inc (e.1 + 1) es

theorem Inc.cons {lo : Nat} {e : Nat × Bool × Nat} {es : List (Nat × Bool × Nat)} (h1 : lo ≤ e.1)
    (h2 : Inc (e.1 + 1) es) : Inc lo (e :: es) := ⟨h1, h2⟩

theorem Inc.head {lo : Nat} {e : Nat × Bool × Nat} {es : List (Nat × Bool × Nat)} (h : Inc lo (e :: es)) :
    lo ≤ e.1 := h.1

theorem Inc.tail {lo : Nat} {e : Nat × Bool × Nat} {es : List (Nat × Bool × Nat)} (h : Inc lo (e :: es)) :
    Inc (e.1 + 1) es := h.2

theorem Inc.mono {lo lo' : Nat} (h : lo' ≤ lo) : ∀ {l}, Inc lo l → Inc lo' l
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨le_trans h h1, h2⟩

theorem lk_of_lt : ∀ {lo : Nat} {l : List (Nat × Bool × Nat)} {i : Nat}, Inc lo l → i < lo → lk l i = 0
  | _, [], _, _, _ => rfl
  | lo, e :: es, i, ⟨h1, h2⟩, hi => by
    rw [lk_cons, if_neg (by omega), lk_of_lt h2 (by omega), add_zero]

theorem lk_head {lo : Nat} (e : Nat × Bool × Nat) (es : List (Nat × Bool × Nat)) (h : Inc lo (e :: es)) :
    lk (e :: es) e.1 = sv e.2 := by
  rw [lk_cons, if_pos rfl, lk_of_lt h.2 (by omega), add_zero]

theorem lk_cons_ne (e : Nat × Bool × Nat) (es : List (Nat × Bool × Nat)) (i : Nat) (h : e.1 ≠ i) :
    lk (e :: es) i = lk es i := by
  rw [lk_cons, if_neg h, zero_add]

/-! ## Accumulators -/

/-- Value of an accumulator cell. -/
def ival (e : Nat × Nat) : ℤ := (e.1 : ℤ) - e.2

theorem beq_cases (a b : Nat) {α : Sort*} (x y : α) :
    Bool.rec (motive := fun _ => α) x y (Nat.beq a b) = if a = b then y else x := by
  cases h : Nat.beq a b
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

theorem addRow_nil (σ : Bool) (m : Nat) (row : List (Nat × Bool × Nat)) (pos : Nat) :
    addRow σ m [] row pos = [] := rfl

theorem addRow_cons_nil (σ : Bool) (m : Nat) (y : Nat × Nat) (ys : List (Nat × Nat)) (pos : Nat) :
    addRow σ m (y :: ys) [] pos = y :: ys := rfl

theorem addRow_cons_cons (σ : Bool) (m : Nat) (y : Nat × Nat) (ys : List (Nat × Nat))
    (e : Nat × Bool × Nat) (es : List (Nat × Bool × Nat)) (pos : Nat) :
    addRow σ m (y :: ys) (e :: es) pos =
      if e.1 = pos then
        Bool.rec (motive := fun _ => Nat × Nat) (Nat.add y.1 (Nat.mul m e.2.2), y.2)
            (y.1, Nat.add y.2 (Nat.mul m e.2.2)) (xor σ e.2.1) :: addRow σ m ys es (Nat.add pos 1)
      else y :: addRow σ m ys (e :: es) (Nat.add pos 1) := by
  show Bool.rec (motive := fun _ => List (Nat × Nat)) _ _ (Nat.beq e.1 pos) = _
  rw [beq_cases]
  rfl

theorem ival_upd (σ : Bool) (m : Nat) (y : Nat × Nat) (e : Nat × Bool × Nat) :
    ival (Bool.rec (motive := fun _ => Nat × Nat) (Nat.add y.1 (Nat.mul m e.2.2), y.2)
      (y.1, Nat.add y.2 (Nat.mul m e.2.2)) (xor σ e.2.1)) =
      ival y + sv (σ, m) * sv e.2 := by
  rw [← sv_xor σ e.2.1 m e.2.2]
  cases hx : xor σ e.2.1
  · show ((Nat.add y.1 (Nat.mul m e.2.2) : ℕ) : ℤ) - (y.2 : ℤ) = ((y.1 : ℤ) - y.2) + sv (false, m * e.2.2)
    simp only [sv, nat_add, nat_mul, Bool.false_eq_true, ↓reduceIte]; push_cast; ring
  · show ((y.1 : ℕ) : ℤ) - ((Nat.add y.2 (Nat.mul m e.2.2) : ℕ) : ℤ) = ((y.1 : ℤ) - y.2) + sv (true, m * e.2.2)
    simp only [sv, nat_add, nat_mul, ↓reduceIte]; push_cast; ring

theorem length_addRow (σ : Bool) (m : Nat) : ∀ (ys : List (Nat × Nat)) (row : List (Nat × Bool × Nat)) (pos : Nat),
    (addRow σ m ys row pos).length = ys.length
  | [], _, _ => rfl
  | y :: ys, [], pos => rfl
  | y :: ys, e :: es, pos => by
    rw [addRow_cons_cons]
    split_ifs <;> simp [length_addRow σ m ys]

theorem addRow_get (σ : Bool) (m : Nat) : ∀ (ys : List (Nat × Nat)) (row : List (Nat × Bool × Nat)) (pos : Nat),
    Inc pos row → ∀ p, p < ys.length →
      ival ((addRow σ m ys row pos).getD p (0, 0)) = ival (ys.getD p (0, 0)) + sv (σ, m) * lk row (pos + p)
  | [], _, _, _, p, hp => absurd hp (by simp)
  | y :: ys, [], pos, _, p, _ => by rw [addRow_cons_nil]; simp
  | y :: ys, e :: es, pos, hinc, p, hp => by
    rw [addRow_cons_cons]
    by_cases he : e.1 = pos
    · rw [if_pos he]
      cases p with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero]
        rw [ival_upd, ← he, lk_head e es hinc]
      | succ p =>
        simp only [List.getD_cons_succ]
        rw [addRow_get σ m ys es (Nat.add pos 1) (Inc.mono (by rw [nat_add]; omega) hinc.tail) p
          (by simpa using hp), lk_cons_ne e es _ (by omega)]
        rw [nat_add]; ring_nf
    · rw [if_neg he]
      have hlt : pos < e.1 := lt_of_le_of_ne hinc.1 (Ne.symm he)
      cases p with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero]
        rw [lk_of_lt (lo := pos + 1) (Inc.cons hlt hinc.tail) (by omega), mul_zero, add_zero]
      | succ p =>
        simp only [List.getD_cons_succ]
        rw [addRow_get σ m ys (e :: es) (Nat.add pos 1) (Inc.cons (by rw [nat_add]; omega) hinc.tail) p
          (by simpa using hp)]
        rw [nat_add]; ring_nf


/-! ## Rows -/

theorem walkRows_nil (gs : Bool) (gm : Nat) (hs : List (Nat × Bool × Nat)) (i0 : Nat)
    (col : List (Nat × Bool × Nat)) (i : Nat) : walkRows gs gm hs i0 [] col i = [] := rfl

theorem walkRows_cons_nil (gs : Bool) (gm : Nat) (hs : List (Nat × Bool × Nat)) (i0 : Nat)
    (y : List (Nat × Nat)) (Ys : List (List (Nat × Nat))) (i : Nat) :
    walkRows gs gm hs i0 (y :: Ys) [] i = y :: Ys := rfl

theorem walkRows_cons_cons (gs : Bool) (gm : Nat) (hs : List (Nat × Bool × Nat)) (i0 : Nat)
    (y : List (Nat × Nat)) (Ys : List (List (Nat × Nat))) (e : Nat × Bool × Nat) (es : List (Nat × Bool × Nat))
    (i : Nat) :
    walkRows gs gm hs i0 (y :: Ys) (e :: es) i =
      if e.1 = i then addRow (xor gs e.2.1) (Nat.mul gm e.2.2) y hs i0 :: walkRows gs gm hs i0 Ys es (Nat.add i 1)
      else y :: walkRows gs gm hs i0 Ys (e :: es) (Nat.add i 1) := by
  show Bool.rec (motive := fun _ => List (List (Nat × Nat))) _ _ (Nat.beq e.1 i) = _
  rw [beq_cases]
  rfl

/-- All rows have length `len`. -/
def Shape (len : Nat) (Y : List (List (Nat × Nat))) : Prop := ∀ r, r < Y.length → (Y.getD r []).length = len

theorem walkRows_shape (gs : Bool) (gm : Nat) (hs : List (Nat × Bool × Nat)) (i0 len : Nat) :
    ∀ (Y : List (List (Nat × Nat))) (col : List (Nat × Bool × Nat)) (i : Nat), Shape len Y →
      (walkRows gs gm hs i0 Y col i).length = Y.length ∧ Shape len (walkRows gs gm hs i0 Y col i)
  | [], _, _, _ => ⟨rfl, fun r hr => absurd hr (by rw [walkRows_nil]; simp)⟩
  | y :: Ys, [], i, h => by rw [walkRows_cons_nil]; exact ⟨rfl, h⟩
  | y :: Ys, e :: es, i, h => by
    have hY : Shape len Ys := fun r hr => by simpa using h (r + 1) (by simpa using hr)
    rw [walkRows_cons_cons]
    split_ifs
    · obtain ⟨h1, h2⟩ := walkRows_shape gs gm hs i0 len Ys es (Nat.add i 1) hY
      refine ⟨by simp [h1], fun r hr => ?_⟩
      cases r with
      | zero => simpa [length_addRow] using h 0 (by simp)
      | succ r => simpa using h2 r (by simpa [h1] using hr)
    · obtain ⟨h1, h2⟩ := walkRows_shape gs gm hs i0 len Ys (e :: es) (Nat.add i 1) hY
      refine ⟨by simp [h1], fun r hr => ?_⟩
      cases r with
      | zero => simpa using h 0 (by simp)
      | succ r => simpa using h2 r (by simpa [h1] using hr)

theorem walkRows_get (gs : Bool) (gm : Nat) (hs : List (Nat × Bool × Nat)) (i0 : Nat) (hhs : Inc i0 hs) :
    ∀ (Y : List (List (Nat × Nat))) (col : List (Nat × Bool × Nat)) (i : Nat), Inc i col →
      ∀ r p, r < Y.length → p < (Y.getD r []).length →
        ival (((walkRows gs gm hs i0 Y col i).getD r []).getD p (0, 0)) =
          ival ((Y.getD r []).getD p (0, 0)) + sv (gs, gm) * lk col (i + r) * lk hs (i0 + p)
  | [], _, _, _, r, p, hr, _ => absurd hr (by simp)
  | y :: Ys, [], i, _, r, p, _, _ => by rw [walkRows_cons_nil]; simp
  | y :: Ys, e :: es, i, hinc, r, p, hr, hp => by
    rw [walkRows_cons_cons]
    by_cases he : e.1 = i
    · rw [if_pos he]
      cases r with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero] at hp ⊢
        rw [addRow_get _ _ y hs i0 hhs p hp, ← he, lk_head e es hinc]
        show _ = _ + sv (gs, gm) * sv e.2 * _
        rw [show Nat.mul gm e.2.2 = gm * e.2.2 from rfl, sv_xor]
      | succ r =>
        simp only [List.getD_cons_succ] at hp ⊢
        rw [walkRows_get gs gm hs i0 hhs Ys es (Nat.add i 1) (Inc.mono (by rw [nat_add]; omega) hinc.tail) r p
          (by simpa using hr) hp, lk_cons_ne e es _ (by omega)]
        rw [nat_add]; ring_nf
    · rw [if_neg he]
      have hlt : i < e.1 := lt_of_le_of_ne hinc.head (Ne.symm he)
      cases r with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero]
        rw [lk_of_lt (lo := i + 1) (Inc.cons hlt hinc.tail) (by omega), mul_zero, zero_mul, add_zero]
      | succ r =>
        simp only [List.getD_cons_succ] at hp ⊢
        rw [walkRows_get gs gm hs i0 hhs Ys (e :: es) (Nat.add i 1) (Inc.cons (by rw [nat_add]; omega) hinc.tail)
          r p (by simpa using hr) hp]
        rw [nat_add]; ring_nf

/-! ## Columns -/

/-- `N` column `k` and `H` slice row `k` as decoded by the kernel. -/
noncomputable def ncol (T : Tab) (k : Nat) : List (Nat × Bool × Nat) := decValVec (T.nc k) (T.nn k) 0
noncomputable def hrow (T : Tab) (S : Slice) (k : Nat) : List (Nat × Bool × Nat) :=
  decPolyVec T.R (S.hc k) (S.hn k) 0

theorem colsGo_nil (T : Tab) (S : Slice) (Y : List (List (Nat × Nat))) : colsGo T S [] Y = Y := rfl

theorem colsGo_cons (T : Tab) (S : Slice) (g : Nat × Bool × Nat) (gl : List (Nat × Bool × Nat))
    (Y : List (List (Nat × Nat))) :
    colsGo T S (g :: gl) Y = colsGo T S gl (match hrow T S g.1 with
      | [] => Y
      | _ :: _ => walkRows g.2.1 g.2.2 (hrow T S g.1) S.i0 Y (ncol T g.1) 0) := by
  show colsGo T S gl ((fun hs => List.rec (motive := fun _ => List (List (Nat × Nat))) Y
    (fun _ _ _ => walkRows g.2.1 g.2.2 hs S.i0 Y (ncol T g.1) 0) hs) (hrow T S g.1)) = _
  congr 1
  cases hrow T S g.1 <;> rfl

theorem colsGo_get (T : Tab) (S : Slice) (len : Nat) :
    ∀ (gl : List (Nat × Bool × Nat)) (Y : List (List (Nat × Nat))),
      (∀ g ∈ gl, Inc 0 (ncol T g.1) ∧ Inc S.i0 (hrow T S g.1)) → Shape len Y →
      (colsGo T S gl Y).length = Y.length ∧ Shape len (colsGo T S gl Y) ∧
      ∀ r p, r < Y.length → p < len →
        ival (((colsGo T S gl Y).getD r []).getD p (0, 0)) =
          ival ((Y.getD r []).getD p (0, 0)) +
            (gl.map fun g => sv g.2 * lk (ncol T g.1) r * lk (hrow T S g.1) (S.i0 + p)).sum
  | [], Y, _, hY => ⟨rfl, hY, fun r p _ _ => by simp [colsGo_nil]⟩
  | g :: gl, Y, hg, hY => by
    rw [colsGo_cons]
    have hg' : ∀ g' ∈ gl, Inc 0 (ncol T g'.1) ∧ Inc S.i0 (hrow T S g'.1) := fun g' h => hg g' (by simp [h])
    obtain ⟨hn, hh⟩ := hg g (by simp)
    -- one column step
    have step : ∃ Y', (match hrow T S g.1 with
        | [] => Y
        | _ :: _ => walkRows g.2.1 g.2.2 (hrow T S g.1) S.i0 Y (ncol T g.1) 0) = Y' ∧
        Y'.length = Y.length ∧ Shape len Y' ∧ ∀ r p, r < Y.length → p < len →
          ival ((Y'.getD r []).getD p (0, 0)) = ival ((Y.getD r []).getD p (0, 0)) +
            sv g.2 * lk (ncol T g.1) r * lk (hrow T S g.1) (S.i0 + p) := by
      refine ⟨_, rfl, ?_⟩
      cases hr : hrow T S g.1 with
      | nil => exact ⟨rfl, hY, fun r p _ _ => by simp⟩
      | cons e es =>
        rw [hr] at hh
        obtain ⟨h1, h2⟩ := walkRows_shape g.2.1 g.2.2 (e :: es) S.i0 len Y (ncol T g.1) 0 hY
        refine ⟨h1, h2, fun r p hr' hp => ?_⟩
        show ival (((walkRows g.2.1 g.2.2 (e :: es) S.i0 Y (ncol T g.1) 0).getD r []).getD p (0, 0)) = _
        rw [walkRows_get _ _ _ _ hh Y _ 0 hn r p hr' (by rw [hY r hr']; exact hp), zero_add]
    obtain ⟨Y', hY'eq, hl, hs, hv⟩ := step
    rw [hY'eq]
    obtain ⟨h1, h2, h3⟩ := colsGo_get T S len gl Y' hg' hs
    refine ⟨h1.trans hl, h2, fun r p hr hp => ?_⟩
    rw [h3 r p (hl ▸ hr) hp, hv r p hr hp, List.map_cons, List.sum_cons]
    ring


/-! ## Final checks -/

theorem sliceOk_cons (i sq : Nat) (e : Nat × Nat) (es : List (Nat × Nat)) (pos : Nat) :
    sliceOk i sq (e :: es) pos =
      (Bool.rec (motive := fun _ => Bool) (Nat.beq e.1 e.2) (Nat.beq e.1 (Nat.add e.2 sq)) (Nat.beq i pos) &&
        sliceOk i sq es (Nat.add pos 1)) := rfl

theorem sliceOk_get (i sq : Nat) : ∀ (y : List (Nat × Nat)) (pos : Nat), sliceOk i sq y pos = true →
    ∀ p, p < y.length → ival (y.getD p (0, 0)) = if i = pos + p then (sq : ℤ) else 0
  | [], _, _, p, hp => absurd hp (by simp)
  | e :: es, pos, h, p, hp => by
    rw [sliceOk_cons, Bool.and_eq_true, beq_cases] at h
    cases p with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      by_cases hi : i = pos
      · rw [if_pos hi] at h; rw [if_pos hi]
        have := Nat.eq_of_beq_eq_true h.1
        simp only [ival, this, nat_add]; push_cast; ring
      · rw [if_neg hi] at h; rw [if_neg hi]
        have := Nat.eq_of_beq_eq_true h.1
        simp only [ival, this]; ring
    | succ p =>
      simp only [List.getD_cons_succ]
      rw [sliceOk_get i sq es (Nat.add pos 1) h.2 p (by simpa using hp), nat_add]
      simp only [show pos + 1 + p = pos + (p + 1) by ring]

/-- `rowsOk` from row index `i`. -/
noncomputable def rowsAux (sq : Nat) (Y : List (List (Nat × Nat))) (i0 : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun y _ ih i => sliceOk i sq y i0 && ih (Nat.add i 1)) Y

theorem rowsAux_get (sq i0 : Nat) : ∀ (Y : List (List (Nat × Nat))) (i : Nat), rowsAux sq Y i0 i = true →
    ∀ r, r < Y.length → sliceOk (i + r) sq (Y.getD r []) i0 = true
  | [], _, _, r, hr => absurd hr (by simp)
  | y :: Ys, i, h, r, hr => by
    have h' : (sliceOk i sq y i0 && rowsAux sq Ys i0 (Nat.add i 1)) = true := h
    rw [Bool.and_eq_true] at h'
    cases r with
    | zero => simpa using h'.1
    | succ r =>
      have := rowsAux_get sq i0 Ys (Nat.add i 1) h'.2 r (by simpa using hr)
      simpa [nat_add, show i + 1 + r = i + (r + 1) by ring] using this

theorem rep_eq {α : Type} (x : α) : ∀ n, rep x n = List.replicate n x
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, ← rep_eq x n]; rfl

/-! ## Header checks -/

/-- One past the last index (or `lo`). -/
def lastNext (lo : Nat) : List (Nat × Bool × Nat) → Nat
  | [] => lo
  | e :: es => lastNext (e.1 + 1) es

theorem Inc.append : ∀ {lo : Nat} {l1 l2 : List (Nat × Bool × Nat)}, Inc lo l1 → Inc (lastNext lo l1) l2 →
    Inc lo (l1 ++ l2)
  | _, [], _, _, h2 => h2
  | _, e :: es, _, h1, h2 => Inc.cons h1.head (Inc.append h1.tail h2)

theorem valsOk_spec (hi : Nat) : ∀ (n lo x : Nat), 1 ≤ valsOk hi n lo x →
    Inc lo (decVals n x) ∧ (∀ e ∈ decVals n x, e.1 < hi) ∧ valsOk hi n lo x = lastNext lo (decVals n x) + 1
  | 0, lo, x, _ => ⟨trivial, fun e he => by simp [decVals] at he, rfl⟩
  | n + 1, lo, x, h => by
    have hv : valsOk hi (n + 1) lo x = Bool.rec (motive := fun _ => Nat) 0
        (valsOk hi n (Nat.add (Nat.land x 4095) 1)
          (Nat.shiftRight x (Nat.add 32 (Nat.land (Nat.shiftRight x 13) 524287))))
        (Nat.ble lo (Nat.land x 4095) && Nat.blt (Nat.land x 4095) hi) := rfl
    have hd : decVals (n + 1) x = (Nat.land x 4095, Nat.beq (Nat.land (Nat.shiftRight x 12) 1) 1,
        Nat.land (Nat.shiftRight x 32) (Nat.sub (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight x 13) 524287)) 1)) ::
        decVals n (Nat.shiftRight x (Nat.add 32 (Nat.land (Nat.shiftRight x 13) 524287))) := rfl
    rw [hd]
    cases hc : (Nat.ble lo (Nat.land x 4095) && Nat.blt (Nat.land x 4095) hi)
    · rw [hv, hc] at h; exact absurd (show 1 ≤ 0 from h) (by omega)
    · rw [hv, hc] at h ⊢
      rw [Bool.and_eq_true] at hc
      have h1 : lo ≤ Nat.land x 4095 := Nat.le_of_ble_eq_true hc.1
      have h2 : Nat.land x 4095 < hi := Nat.blt_eq.mp hc.2
      obtain ⟨i1, i2, i3⟩ := valsOk_spec hi n _ _ h
      refine ⟨Inc.cons h1 (by simpa [nat_add] using i1), fun e he => ?_, by simpa [lastNext, nat_add] using i3⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact h2
      · exact i2 e he

theorem valsOkVec_pos (hi : Nat) (ch : Nat → Nat) : ∀ (n c lo1 : Nat), 1 ≤ valsOkVec hi ch n c lo1 → 1 ≤ lo1
  | 0, _, _, h => h
  | n + 1, c, lo1, h => by
    have hv : valsOkVec hi ch (n + 1) c lo1 = Bool.rec (motive := fun _ => Nat) 0
        (valsOkVec hi ch n (Nat.add c 1) (valsOk hi (Nat.land (ch c) 255) (Nat.sub lo1 1) (Nat.shiftRight (ch c) 8)))
        (Nat.ble 1 lo1) := rfl
    cases hc : Nat.ble 1 lo1
    · rw [hv, hc] at h; exact absurd (show 1 ≤ 0 from h) (by omega)
    · exact Nat.le_of_ble_eq_true hc

theorem valsOkVec_spec (hi : Nat) (ch : Nat → Nat) : ∀ (n c lo1 : Nat), 1 ≤ valsOkVec hi ch n c lo1 →
    Inc (lo1 - 1) (decValVec ch n c) ∧ ∀ e ∈ decValVec ch n c, e.1 < hi
  | 0, _, _, _ => ⟨trivial, fun e he => by simp [decValVec] at he⟩
  | n + 1, c, lo1, h => by
    have hv : valsOkVec hi ch (n + 1) c lo1 = Bool.rec (motive := fun _ => Nat) 0
        (valsOkVec hi ch n (Nat.add c 1) (valsOk hi (Nat.land (ch c) 255) (Nat.sub lo1 1) (Nat.shiftRight (ch c) 8)))
        (Nat.ble 1 lo1) := rfl
    have hd : decValVec ch (n + 1) c = decVals (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++
        decValVec ch n (Nat.add c 1) := rfl
    have hlo := valsOkVec_pos hi ch (n + 1) c lo1 h
    rw [hv, show Nat.ble 1 lo1 = true from Nat.ble_eq.mpr hlo] at h
    have hin := valsOkVec_pos hi ch n _ _ h
    obtain ⟨a1, a2, a3⟩ := valsOk_spec hi _ _ _ hin
    obtain ⟨b1, b2⟩ := valsOkVec_spec hi ch n _ _ h
    rw [hd]
    refine ⟨Inc.append (by simpa [nat_sub] using a1) (by rw [a3] at b1; simpa [nat_sub] using b1), fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact a2 e he
    · exact b2 e he

/-! ## The leaf theorem -/

theorem tabOk_spec (T : Tab) (h : tabOk T = true) :
    (Inc 0 (decValVec T.gc T.gn 0) ∧ ∀ e ∈ decValVec T.gc T.gn 0, e.1 < T.n) ∧
      ∀ k, k < T.n → Inc 0 (ncol T k) ∧ ∀ e ∈ ncol T k, e.1 < T.n := by
  have h' : (Nat.ble 1 (valsOkVec T.n T.gc T.gn 0 1) &&
      Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && Nat.ble 1 (valsOkVec T.n (T.nc k) (T.nn k) 0 1)) T.n)
      = true := h
  rw [Bool.and_eq_true] at h'
  refine ⟨valsOkVec_spec _ _ _ _ _ (Nat.le_of_ble_eq_true h'.1), ?_⟩
  have key : ∀ m, Nat.rec (motive := fun _ => Bool) true
      (fun k ih => ih && Nat.ble 1 (valsOkVec T.n (T.nc k) (T.nn k) 0 1)) m = true →
      ∀ k, k < m → Inc 0 (ncol T k) ∧ ∀ e ∈ ncol T k, e.1 < T.n := by
    intro m
    induction m with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ m ih =>
      intro hm k hk
      have hm' : (Nat.rec (motive := fun _ => Bool) true
          (fun k ih => ih && Nat.ble 1 (valsOkVec T.n (T.nc k) (T.nn k) 0 1)) m &&
          Nat.ble 1 (valsOkVec T.n (T.nc m) (T.nn m) 0 1)) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih hm'.1 k hk
      · exact valsOkVec_spec _ _ _ _ _ (Nat.le_of_ble_eq_true hm'.2)
  exact key T.n h'.2

end ThomsonCompact.Fixed
