import ThomsonCompact.CoeffMap.GramPackSound
import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.DenseSound

/-!
# Soundness of the narrow W0 entries (F2g)

For `w0OkN d c bi = true` (the D12 block check `w0Ok` and the narrow slot bounds):

* `dColB_slot`: slot `p` of the biased narrow column `dColB ent wn n q` is `dotE ent p q + 2^(wn-1)` for **every**
  `p < n` (`dotE ent p q = Σ_{l ≤ min(p,q)} x(q,l) x(p,l)`; `CoeffMap.dPack_cast` at width `wn`), so `sgnSlot` decodes
  the dot product (`ival_sgnSlot`);
* `accN_cast`: `pos - neg = Σ_{k ≤ nw} czI k p · 2^(W k)` (`CoeffMap.uPair_cast`, the algebra `CoeffMap.gram_alg` at one
  row);
* `winN_window`: the biased window `winN` is the window of the D12 packed column `gPackB` (both are the digits
  `czI k p + 2^(W-1)`, `CoeffMap.window_eq`), hence `entryN_eq`: the narrow entry TM **is** the D12 entry TM
  `entryTM … (gPackB d c bi q) p`, and `CoeffMap.entryTM_sound` applies;
* `WTn_sound`: every `WTn d c bi i j` with `ok = true` encloses the (symmetric, zero-padded) literal Gram entry
  `litW d bi i j`; `WTn_symm`: `WTn` is symmetric as a function of the indices;
* `flat_block`: the flattened data (`CellData.flat`) decode the same literal blocks when the chunks hold the fields
  (`n(n-1)/2 ≤ nchK · perK`, `n(n+1)/2 ≤ nchF · perF`), hence `WTn_sound_flat`: the narrow entries of the flattened data
  enclose the literal Gram entries of the **original** data (the conditions follow from `ok`).
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

/-! ## Narrow columns -/

/-- The integer dot product of rows `p` and `q` of a lower-triangular entry function (slot `p` of the column `D_q`). -/
def dotE (ent : ℕ → ℕ → Bool × ℕ) (p q : ℕ) : ℤ :=
  ∑ l ∈ Finset.range (q + 1), if l ≤ p then ival (ent q l) * ival (ent p l) else 0

theorem ival_pair (y H : ℕ) : ival (Nat.blt y H, Nat.add (Nat.sub y H) (Nat.sub H y)) = (y : ℤ) - H := by
  unfold ival
  split_ifs with hc
  · have h : y < H := Nat.blt_eq.mp hc
    show -(((y - H + (H - y) : ℕ)) : ℤ) = _
    rw [show y - H + (H - y) = H - y by omega, Nat.cast_sub h.le]
    ring
  · have h : ¬ y < H := fun h' => hc (Nat.blt_eq.mpr h')
    show (((y - H + (H - y) : ℕ)) : ℤ) = _
    rw [show y - H + (H - y) = y - H by omega, Nat.cast_sub (by omega)]

theorem ival_sgnSlot (wn x p : ℕ) (z : ℤ) (hs : (slotAt wn x p : ℤ) = z + 2 ^ (wn - 1)) :
    ival (sgnSlot wn x p) = z := by
  have hH : Nat.shiftLeft 1 (Nat.sub wn 1) = 2 ^ (wn - 1) := by rw [shl_eq]; exact one_mul _
  have e : sgnSlot wn x p = (Nat.blt (slotAt wn x p) (Nat.shiftLeft 1 (Nat.sub wn 1)),
      Nat.add (Nat.sub (slotAt wn x p) (Nat.shiftLeft 1 (Nat.sub wn 1)))
        (Nat.sub (Nat.shiftLeft 1 (Nat.sub wn 1)) (slotAt wn x p))) := rfl
  rw [e, ival_pair, hs, hH]
  push_cast
  ring

/-- **Slot `p` of a biased narrow column** is the biased dot product of rows `p` and `q` (any `p < n`). -/
theorem dColB_slot (ent : ℕ → ℕ → Bool × ℕ) (wn n q p : ℕ) (h1 : 1 ≤ wn) (hp : p < n)
    (hb : ∀ p l, l ≤ p → p < n → (ent p l).2 * 2 ^ (wn * p) ≤ 2 ^ (wn * n))
    (hd : ∀ p, p < n → |dotE ent p q| < 2 ^ (wn - 1)) :
    (slotAt wn (dColB ent wn n q) p : ℤ) = dotE ent p q + 2 ^ (wn - 1) := by
  set zs : List ℤ := (List.range n).map fun p => dotE ent p q with hzs
  have hlen : zs.length = n := by simp [hzs]
  have hbz : ∀ x ∈ zs, |x| < 2 ^ (wn - 1) := by
    intro x hx
    simp only [hzs, List.mem_map, List.mem_range] at hx
    obtain ⟨p', hp', rfl⟩ := hx
    exact hd p' hp'
  have hhor : horner (2 ^ wn : ℤ) zs = ∑ p ∈ Finset.range n, dotE ent p q * 2 ^ (wn * p) := by
    rw [horner_eq_sum, hlen]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hzs, List.getD_eq_getElem?_getD]
    simp [Finset.mem_range.mp hi, pow_mul]
  have hV : (dPack ent wn (2 ^ (wn * n)) n q : ℤ) % 2 ^ (wn * n) = horner (2 ^ wn : ℤ) zs % 2 ^ (wn * n) := by
    have h : ((dPack ent wn (2 ^ (wn * n)) n q : ℕ) : ZMod (2 ^ (wn * n))) =
        ∑ p ∈ Finset.range n, ((dotE ent p q : ℤ) : ZMod (2 ^ (wn * n))) * 2 ^ (wn * p) :=
      dPack_cast ent wn (wn * n) n q hb
    have h2 : ((dPack ent wn (2 ^ (wn * n)) n q : ℕ) : ZMod (2 ^ (wn * n))) =
        ((horner (2 ^ wn : ℤ) zs : ℤ) : ZMod (2 ^ (wn * n))) := by
      rw [h, hhor]
      push_cast
      rfl
    rw [← Int.cast_natCast] at h2
    have h3 := (ZMod.intCast_eq_intCast_iff' _ _ _).mp h2
    push_cast at h3
    exact h3
  have hm := mod_biased h1 le_rfl zs hlen hbz _ hV
  have hcol : dColB ent wn n q = Nat.ofDigits (2 ^ wn) (zs.map fun x => (x + 2 ^ (wn - 1)).toNat) := by
    unfold dColB
    rw [show Nat.pow 2 (Nat.mul wn n) = 2 ^ (wn * n) from rfl, land_mask_eq,
      show Nat.shiftLeft 1 (Nat.sub wn 1) = 2 ^ (wn - 1) by rw [shl_eq]; exact one_mul _]
    exact hm
  have hdig : ∀ r, r < n → (dotE ent r q + 2 ^ (wn - 1)).toNat < 2 ^ wn := by
    intro r hr
    have := abs_lt.mp (hd r hr)
    have hH : (2 : ℤ) ^ wn = 2 * 2 ^ (wn - 1) := by
      conv_lhs => rw [show wn = (wn - 1) + 1 by omega]
      exact pow_succ' 2 (wn - 1)
    have h0 : 0 ≤ dotE ent r q + 2 ^ (wn - 1) := by linarith
    have : ((dotE ent r q + 2 ^ (wn - 1)).toNat : ℤ) < 2 ^ wn := by
      rw [Int.toNat_of_nonneg h0, hH]; linarith
    exact_mod_cast this
  have hcol2 : dColB ent wn n q = ∑ r ∈ Finset.range n, (dotE ent r q + 2 ^ (wn - 1)).toNat * 2 ^ (wn * r) := by
    have := sum_digits_eq wn (fun r => (dotE ent r q + 2 ^ (wn - 1)).toNat) n
    rw [hcol, hzs, List.map_map]
    exact this.symm
  have key : slotAt wn (∑ r ∈ Finset.range n, (dotE ent r q + 2 ^ (wn - 1)).toNat * 2 ^ (wn * r)) p =
      (dotE ent p q + 2 ^ (wn - 1)).toNat :=
    slot_digits wn (by omega) (fun r => (dotE ent r q + 2 ^ (wn - 1)).toNat) n p hdig hp
  rw [hcol2, key]
  have h0 : 0 ≤ dotE ent p q + 2 ^ (wn - 1) := by
    have := abs_lt.mp (hd p hp); linarith
  exact Int.toNat_of_nonneg h0

/-! ## The accumulators -/

theorem accPM_cast (s : Bool) (m Up Un : ℕ) (a : ℕ × ℕ) :
    ((accPM s m Up Un a).1 : ℤ) - (accPM s m Up Un a).2 = ((a.1 : ℤ) - a.2) + ival (s, m) * ((Up : ℤ) - Un) := by
  unfold accPM ival
  cases s
  · simp only [cond_false, Bool.false_eq_true, if_false]
    push_cast [show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl, show ∀ a b : ℕ, Nat.mul a b = a * b from fun _ _ => rfl]
    ring
  · simp only [cond_true, if_true]
    push_cast [show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl, show ∀ a b : ℕ, Nat.mul a b = a * b from fun _ _ => rfl]
    ring

/-- The `(pos, neg)` recursion of `accN` as an integer sum. -/
theorem accRec_cast (base : ℕ × ℕ) (sm : ℕ → Bool × ℕ) (U : ℕ → ℕ × ℕ) : ∀ j,
    ((Nat.rec (motive := fun _ => ℕ × ℕ) base (fun u ih => accPM (sm u).1 (sm u).2 (U u).1 (U u).2 ih) j).1 : ℤ) -
      (Nat.rec (motive := fun _ => ℕ × ℕ) base (fun u ih => accPM (sm u).1 (sm u).2 (U u).1 (U u).2 ih) j).2 =
      ((base.1 : ℤ) - base.2) + ∑ u ∈ Finset.range j, ival (sm u) * (((U u).1 : ℤ) - (U u).2)
  | 0 => by simp
  | j + 1 => by
    rw [Finset.sum_range_succ, ← add_assoc, ← accRec_cast base sm U j]
    exact accPM_cast _ _ _ _ _

theorem base_cast (sm : Bool × ℕ) (sh : ℕ) :
    (((cond sm.1 (0, Nat.shiftLeft sm.2 sh) (Nat.shiftLeft sm.2 sh, 0) : ℕ × ℕ).1 : ℤ) -
      (cond sm.1 (0, Nat.shiftLeft sm.2 sh) (Nat.shiftLeft sm.2 sh, 0) : ℕ × ℕ).2) = ival sm * 2 ^ sh := by
  obtain ⟨s, m⟩ := sm
  unfold ival
  rw [shl_eq]
  cases s <;> simp

/-! ## The narrow slot bounds -/

/-- The narrow conditions of `w0OkN` (beyond `w0Ok`). -/
structure NarrowCond (d : CellData) (bi : ℕ) : Prop where
  wf : (d.layout bi).2.1 ≤ wnOf d bi
  mx : mxK d bi < wnOf d bi
  df : d.order bi * 4 ^ ((d.layout bi).2.1 - 1) < 2 ^ (wnOf d bi - 1)
  dm : d.order bi * 4 ^ mxK d bi < 2 ^ (wnOf d bi - 1)

theorem w0OkN_cond (d : CellData) (c : Ctx) (bi : ℕ) (h : w0OkN d c bi = true) :
    w0Ok d c bi = true ∧ NarrowCond d bi := by
  unfold w0OkN at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h0, h1, h2, ?_, ?_⟩
  · rw [shl_eq, one_mul] at h3; exact h3
  · rw [shl_eq, one_mul] at h4; exact h4

theorem wnOf_pos (d : CellData) (bi : ℕ) : 1 ≤ wnOf d bi := by
  unfold wnOf; show 1 ≤ 2 * _ + 10; omega

theorem four_pow (x : ℕ) : ((2 : ℤ) ^ x) ^ 2 = 4 ^ x := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem facE_hb (d : CellData) (bi u : ℕ) (hn : NarrowCond d bi) :
    ∀ p l, l ≤ p → p < d.order bi →
      (facEnt d bi u p l).2 * 2 ^ (wnOf d bi * p) ≤ 2 ^ (wnOf d bi * d.order bi) := by
  intro p l _ hp
  have h1 := facEnt_mag d bi u p l
  have h2 : 2 ^ ((d.layout bi).2.1 - 1) ≤ 2 ^ wnOf d bi := Nat.pow_le_pow_right (by norm_num) (by
    have := hn.wf; omega)
  calc (facEnt d bi u p l).2 * 2 ^ (wnOf d bi * p) ≤ 2 ^ wnOf d bi * 2 ^ (wnOf d bi * p) :=
        Nat.mul_le_mul_right _ (h1.le.trans h2)
    _ = 2 ^ (wnOf d bi * (p + 1)) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (wnOf d bi * d.order bi) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hp)

theorem metE_hb (d : CellData) (bi : ℕ) (hn : NarrowCond d bi) :
    ∀ p l, l ≤ p → p < d.order bi →
      (metEnt d bi p l).2 * 2 ^ (wnOf d bi * p) ≤ 2 ^ (wnOf d bi * d.order bi) := by
  intro p l hl hp
  have h1 := metEnt_mag d bi p l hl hp
  have h2 : 2 ^ mxK d bi ≤ 2 ^ wnOf d bi := Nat.pow_le_pow_right (by norm_num) hn.mx.le
  calc (metEnt d bi p l).2 * 2 ^ (wnOf d bi * p) ≤ 2 ^ wnOf d bi * 2 ^ (wnOf d bi * p) :=
        Nat.mul_le_mul_right _ (h1.trans h2)
    _ = 2 ^ (wnOf d bi * (p + 1)) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (wnOf d bi * d.order bi) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hp)

theorem facE_dot (d : CellData) (bi u q : ℕ) (hq : q < d.order bi) (hn : NarrowCond d bi) :
    ∀ p, p < d.order bi → |dotE (facEnt d bi u) p q| < 2 ^ (wnOf d bi - 1) := by
  intro p hp
  have h : |dotE (facEnt d bi u) p q| ≤ (d.order bi : ℤ) * (2 ^ ((d.layout bi).2.1 - 1)) ^ 2 := by
    refine dot_bound (fun r l => ival (facEnt d bi u r l)) hp hq _ (by positivity) ?_
    intro r l _ _
    rw [abs_ival]
    exact_mod_cast (facEnt_mag d bi u r l).le
  rw [four_pow] at h
  have h2 : ((d.order bi * 4 ^ ((d.layout bi).2.1 - 1) : ℕ) : ℤ) < 2 ^ (wnOf d bi - 1) := by exact_mod_cast hn.df
  push_cast at h2
  exact lt_of_le_of_lt h h2

theorem metE_dot (d : CellData) (bi q : ℕ) (hq : q < d.order bi) (hn : NarrowCond d bi) :
    ∀ p, p < d.order bi → |dotE (metEnt d bi) p q| < 2 ^ (wnOf d bi - 1) := by
  intro p hp
  have h : |dotE (metEnt d bi) p q| ≤ (d.order bi : ℤ) * (2 ^ mxK d bi) ^ 2 := by
    refine dot_bound (fun r l => ival (metEnt d bi r l)) hp hq _ (by positivity) ?_
    intro r l hl hr
    rw [abs_ival]
    exact_mod_cast metEnt_mag d bi r l hl hr
  rw [four_pow] at h
  have h2 : ((d.order bi * 4 ^ mxK d bi : ℕ) : ℤ) < 2 ^ (wnOf d bi - 1) := by exact_mod_cast hn.dm
  push_cast at h2
  exact lt_of_le_of_lt h h2

/-! ## The window of an entry -/

/-- **The accumulators of entry `(p, q)`**: `pos - neg = Σ_{k ≤ nw} czI k p · 2^(W k)` (any `p, q < n`). -/
theorem accN_cast {N S B W : ℕ} (d : CellData) (bi p q : ℕ) (hp : p < d.order bi) (hq : q < d.order bi)
    (hc : W0Cond d N S B W bi) (hn : NarrowCond d bi) :
    ((accN d (mkCtx N S B W) bi p q).1 : ℤ) - (accN d (mkCtx N S B W) bi p q).2 =
      ∑ k ∈ Finset.range (d.nw + 1), czI d (mkCtx N S B W) bi q k p * 2 ^ (W * k) := by
  have h1 := wnOf_pos d bi
  -- the decoded dots
  have hF : ∀ u, ival (sgnSlot (wnOf d bi) (dColB (facEnt d bi u) (wnOf d bi) (d.order bi) q) p) =
      dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) := by
    intro u
    rw [dotF_eq d bi u hp hq hc.perF]
    exact ival_sgnSlot _ _ _ _ (dColB_slot _ _ _ q p h1 hp (facE_hb d bi u hn) (facE_dot d bi u q hq hn))
  have hM : ival (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p) =
      dotI (d.metricRow bi p) (d.metricRow bi q) := by
    rw [dotM_eq d bi hp hq hc.perK]
    exact ival_sgnSlot _ _ _ _ (dColB_slot _ _ _ q p h1 hp (metE_hb d bi hn) (metE_dot d bi q hq hn))
  -- the recursion
  have hrec := accRec_cast
    (cond (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p).1
      (0, Nat.shiftLeft (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p).2
        (Nat.sub S (scaleM d bi)))
      (Nat.shiftLeft (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p).2
        (Nat.sub S (scaleM d bi)), 0))
    (fun u => sgnSlot (wnOf d bi) (dColB (facEnt d bi u) (wnOf d bi) (d.order bi) q) p)
    (fun u => uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))) (d.nw + 1)
  rw [base_cast, hM] at hrec
  have hacc : accN d (mkCtx N S B W) bi p q = Nat.rec (motive := fun _ => ℕ × ℕ)
      (cond (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p).1
        (0, Nat.shiftLeft (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p).2
          (Nat.sub S (scaleM d bi)))
        (Nat.shiftLeft (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p).2
          (Nat.sub S (scaleM d bi)), 0))
      (fun u ih => accPM (sgnSlot (wnOf d bi) (dColB (facEnt d bi u) (wnOf d bi) (d.order bi) q) p).1
        (sgnSlot (wnOf d bi) (dColB (facEnt d bi u) (wnOf d bi) (d.order bi) q) p).2
        (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1
        (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2 ih) (d.nw + 1) := rfl
  rw [hacc, hrec]
  -- Bernstein weights
  have hU : ∀ u ∈ Finset.range (d.nw + 1),
      (((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
        (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2) =
      ∑ k ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ ((S - (2 * d.fb + d.nw)) + W * k) := by
    intro u hu
    exact uPair_cast W d.nw u _ (by have := Finset.mem_range.mp hu; omega)
  have hsum : ∑ u ∈ Finset.range (d.nw + 1),
      ival (sgnSlot (wnOf d bi) (dColB (facEnt d bi u) (wnOf d bi) (d.order bi) q) p) *
        (((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
          (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2) =
      ∑ u ∈ Finset.range (d.nw + 1), dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) *
        ∑ k ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ ((S - (2 * d.fb + d.nw)) + W * k) :=
    Finset.sum_congr rfl (fun u hu => by rw [hF u, hU u hu])
  rw [hsum]
  -- the algebra at one row
  have hLf : 2 * d.fb + d.nw ≤ d.scaleL bi := Nat.le_max_left _ _
  have hLm : scaleM d bi ≤ d.scaleL bi := Nat.le_max_right _ _
  have halg := gram_alg 1 (d.nw + 1) W S (d.scaleL bi) (2 * d.fb + d.nw) (scaleM d bi) (by omega)
    hLf hLm hc.LS (bernI d.nw) (fun u _ => dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q))
    (fun _ => dotI (d.metricRow bi p) (d.metricRow bi q))
  simp only [Finset.sum_range_one, mul_zero, pow_zero, mul_one, add_zero] at halg
  have hcz : ∀ k, czI d (mkCtx N S B W) bi q k p = ((if k = 0 then 2 ^ (d.scaleL bi - scaleM d bi) *
      dotI (d.metricRow bi p) (d.metricRow bi q) else 0) + ∑ u ∈ Finset.range (d.nw + 1),
        bernI d.nw u k * 2 ^ (d.scaleL bi - (2 * d.fb + d.nw)) *
          dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q)) * 2 ^ (S - d.scaleL bi) := by
    intro k
    unfold czI
    rw [coefI_expand, show d.scaleL bi - 2 * d.fb - d.nw = d.scaleL bi - (2 * d.fb + d.nw) by omega]
    rfl
  simp_rw [hcz]
  rw [← halg, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- **The biased window of entry `(p, q)`** (any `p, q < n`): the digits `czI k p + 2^(W-1)`, `k ≤ nw`. -/
theorem winN_eq {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi) (hc : W0Cond d N S B W bi) (hn : NarrowCond d bi) :
    winN d (mkCtx N S B W) bi p q = Nat.ofDigits (2 ^ W) ((List.range (d.nw + 1)).map fun k =>
        (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) := by
  have hW1 := hg.W1
  set cs0 : List ℤ := (List.range (d.nw + 1)).map fun k => czI d (mkCtx N S B W) bi q k p with hcs0
  have hlen0 : cs0.length = d.nw + 1 := by simp [hcs0]
  have hcl := crude_lt d bi hc
  have hnn0 : ∀ x ∈ cs0, 0 ≤ x + 2 ^ (W - 1) := by
    intro x hx
    simp only [hcs0, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have h1 := czI_bound d bi q k p (by omega) hp hq hc
    have := abs_le.mp h1
    linarith
  have hcast := cast_ofDigits_offset (by omega : 0 < W) (2 ^ (W - 1)) cs0 hnn0
  rw [hlen0] at hcast
  have hhor : horner (2 ^ W : ℤ) cs0 = ∑ k ∈ Finset.range (d.nw + 1), czI d (mkCtx N S B W) bi q k p * 2 ^ (W * k) := by
    rw [horner_eq_sum, hlen0]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hcs0, List.getD_eq_getElem?_getD]
    simp [Finset.mem_range.mp hk, pow_mul]
  have hacc := accN_cast d bi p q hp hq hc hn
  rw [← hhor] at hacc
  have hmap : (List.range (d.nw + 1)).map (fun k => (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) =
      cs0.map (fun x => (x + 2 ^ (W - 1)).toNat) := by
    rw [hcs0, List.map_map]; rfl
  rw [hmap]
  set D := Nat.ofDigits (2 ^ W) (cs0.map fun x => (x + 2 ^ (W - 1)).toNat) with hD
  have hkey : (accN d (mkCtx N S B W) bi p q).1 + 2 ^ (W - 1) * ones W (d.nw + 1) =
      (accN d (mkCtx N S B W) bi p q).2 + D := by
    have : (((accN d (mkCtx N S B W) bi p q).1 + 2 ^ (W - 1) * ones W (d.nw + 1) : ℕ) : ℤ) =
        (((accN d (mkCtx N S B W) bi p q).2 + D : ℕ) : ℤ) := by
      push_cast
      rw [hcast]
      linarith
    exact_mod_cast this
  unfold winN
  show (accN d (mkCtx N S B W) bi p q).1 + 2 ^ (W - 1) * ones W (d.nw + 1) - (accN d (mkCtx N S B W) bi p q).2 = D
  rw [hkey, Nat.add_sub_cancel_left]

/-- The narrow window is the window of the D12 packed column (any `p, q < n`). -/
theorem winN_window {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi) (hok : w0OkN d (mkCtx N S B W) bi = true) :
    winN d (mkCtx N S B W) bi p q =
      Nat.land (Nat.shiftRight (gPackB d (mkCtx N S B W) bi q) (Nat.mul (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1)) p))
        (Nat.sub (Nat.pow 2 (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1))) 1) := by
  obtain ⟨h0, hn⟩ := w0OkN_cond d _ bi hok
  have hc := w0Cond_of d bi h0
  rw [winN_eq hg d bi p q hp hq hc hn, window_eq hg d bi p q hp hq hc]

/-- **The narrow entry TM is the D12 entry TM** (any `p, q < n`, block check passed). -/
theorem entryN_eq {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi) (hok : w0OkN d (mkCtx N S B W) bi = true) :
    entryN (mkCtx N S B W) (Nat.add d.nw 1) (winN d (mkCtx N S B W) bi p q) (w0OkN d (mkCtx N S B W) bi) =
      entryTM (mkCtx N S B W) (Nat.add d.nw 1) (gPackB d (mkCtx N S B W) bi q) p (w0Ok d (mkCtx N S B W) bi) := by
  have h0 := (w0OkN_cond d _ bi hok).1
  rw [winN_window hg d bi p q hp hq hok, hok, h0]
  rfl

theorem entryN_ok (c : Ctx) (M Wv : ℕ) (ok0 : Bool) (h : (entryN c M Wv ok0).ok = true) : ok0 = true := by
  have e : (entryN c M Wv ok0).ok = (Nat.blt (ssum c (pabs c ⟨Nat.land (Nat.add Wv (Nat.sub c.twoK
      (Nat.mul c.hW (ones c.W M)))) c.maskK, 0, 0, 0, true⟩)) c.twoB && ok0) := rfl
  rw [e, Bool.and_eq_true] at h
  exact h.2

/-- An entry TM `(p, q)` (`p, q < n`, any order) with `ok = true` encloses the literal Gram entry. -/
theorem entryN_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi)
    (hok : (entryN (mkCtx N S B W) (Nat.add d.nw 1) (winN d (mkCtx N S B W) bi p q) (w0OkN d (mkCtx N S B W) bi)).ok
      = true) :
    Encl (mkCtx N S B W) (entryN (mkCtx N S B W) (Nat.add d.nw 1) (winN d (mkCtx N S B W) bi p q)
      (w0OkN d (mkCtx N S B W) bi)) (litW d bi p q) := by
  have h0 := entryN_ok _ _ _ _ hok
  rw [entryN_eq hg d bi p q hp hq h0] at hok ⊢
  have hc := w0Cond_of d bi (w0OkN_cond d _ bi h0).1
  by_cases hpq : p ≤ q
  · refine (entryTM_sound hg d bi p q hpq hq hok).congr (fun t _ => ?_)
    unfold litW
    rw [dif_pos ⟨hp, hq⟩]
  · -- the window of column `q` at row `p > q` is the window of column `p` at row `q` (symmetric coefficients)
    have hwin : Nat.land (Nat.shiftRight (gPackB d (mkCtx N S B W) bi q)
        (Nat.mul (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1)) p))
        (Nat.sub (Nat.pow 2 (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1))) 1) =
        Nat.land (Nat.shiftRight (gPackB d (mkCtx N S B W) bi p)
        (Nat.mul (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1)) q))
        (Nat.sub (Nat.pow 2 (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1))) 1) := by
      rw [window_eq hg d bi p q hp hq hc, window_eq hg d bi q p hq hp hc]
      congr 1
      apply List.map_congr_left
      intro k _
      unfold czI
      rw [coefI_symm]
    have heq : entryTM (mkCtx N S B W) (Nat.add d.nw 1) (gPackB d (mkCtx N S B W) bi q) p (w0Ok d (mkCtx N S B W) bi) =
        entryTM (mkCtx N S B W) (Nat.add d.nw 1) (gPackB d (mkCtx N S B W) bi p) q (w0Ok d (mkCtx N S B W) bi) := by
      rw [entryTM_eq, entryTM_eq, hwin]
    rw [heq] at hok ⊢
    refine (entryTM_sound hg d bi q p (by omega) hp hok).congr (fun t _ => ?_)
    unfold litW
    rw [dif_pos ⟨hp, hq⟩]
    exact literalGram_symm d bi hc.he t _ _

/-! ## The narrow W0 table -/

theorem wTabN_lookup (d : CellData) (c : Ctx) (bi i j : ℕ) (hij : i ≤ j) (hj : j < d.order bi) :
    listAt zeroTM (listAt [] (wTabN d c bi) j) i = entryN c (Nat.add d.nw 1) (winN d c bi i j) (w0OkN d c bi) := by
  unfold wTabN
  rw [listAt_mkList _ _ hj]
  unfold wColN
  exact listAt_mkList _ _ (show i < Nat.add j 1 by show i < j + 1; omega)

theorem wTabN_lookup_ge (d : CellData) (c : Ctx) (bi i j : ℕ) (hj : d.order bi ≤ j) :
    listAt zeroTM (listAt [] (wTabN d c bi) j) i = zeroTM := by
  unfold wTabN
  rw [listAt_mkList_ge _ _ hj]
  rfl

theorem WTn_eq (d : CellData) (c : Ctx) (bi i j : ℕ) (hij : i ≤ j) :
    WTn d c bi i j = listAt zeroTM (listAt [] (wTabN d c bi) j) i := by
  unfold WTn
  rw [show Nat.ble i j = true from Nat.ble_eq.mpr hij, cond_true]

/-- **`WTn` is symmetric.** -/
theorem WTn_symm (d : CellData) (c : Ctx) (bi i j : ℕ) : WTn d c bi i j = WTn d c bi j i := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have hf : Nat.ble j i = false := by
      cases h' : Nat.ble j i
      · rfl
      · exact absurd (Nat.ble_eq.mp h') (by omega)
    rw [WTn_eq d c bi i j h.le]
    unfold WTn
    rw [hf, cond_false]
  · rw [h]
  · have hf : Nat.ble i j = false := by
      cases h' : Nat.ble i j
      · rfl
      · exact absurd (Nat.ble_eq.mp h') (by omega)
    rw [WTn_eq d c bi j i h.le]
    unfold WTn
    rw [hf, cond_false]

/-- **The narrow W0 TMs enclose the literal Gram entries** (symmetric, zero outside the block). -/
theorem WTn_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTn d (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  by_cases hij : i ≤ j
  · rw [WTn_eq d _ bi i j hij] at hok ⊢
    by_cases hj : j < d.order bi
    · rw [wTabN_lookup d _ bi i j hij hj] at hok ⊢
      exact entryN_sound hg d bi i j (lt_of_le_of_lt hij hj) hj hok
    · rw [wTabN_lookup_ge d _ bi i j (by omega)]
      refine zero_sound.congr (fun t _ => ?_)
      unfold litW
      rw [dif_neg (fun h => hj h.2)]
  · rw [WTn_symm, WTn_eq d _ bi j i (by omega)] at hok ⊢
    by_cases hi : i < d.order bi
    · rw [wTabN_lookup d _ bi j i (by omega) hi] at hok ⊢
      have h0 := entryN_ok _ _ _ _ hok
      have hc := w0Cond_of d bi (w0OkN_cond d _ bi h0).1
      refine (entryN_sound hg d bi j i (by omega) hi hok).congr (fun t _ => ?_)
      unfold litW
      rw [dif_pos ⟨by omega, hi⟩, dif_pos ⟨hi, by omega⟩]
      exact literalGram_symm d bi hc.he t _ _
    · rw [wTabN_lookup_ge d _ bi j i (by omega)]
      refine zero_sound.congr (fun t _ => ?_)
      unfold litW
      rw [dif_neg (fun h => hi h.1)]

/-- Inside the block, `ok` of an entry implies the block check. -/
theorem WTn_ok_cond (d : CellData) (c : Ctx) (bi i j : ℕ) (hi : i < d.order bi) (hj : j < d.order bi)
    (hok : (WTn d c bi i j).ok = true) : w0OkN d c bi = true := by
  by_cases hij : i ≤ j
  · rw [WTn_eq d c bi i j hij, wTabN_lookup d c bi i j hij hj] at hok
    exact entryN_ok _ _ _ _ hok
  · rw [WTn_symm, WTn_eq d c bi j i (by omega), wTabN_lookup d c bi j i (by omega) hi] at hok
    exact entryN_ok _ _ _ _ hok

/-! ## Flattened data -/

theorem mask_eq (a : ℕ) : Nat.sub (Nat.shiftLeft 1 a) 1 = Nat.sub (2 ^ a) 1 := by rw [shl_eq, one_mul]

theorem catChunks_eq (ch : ℕ → ℕ) (w per : ℕ) : ∀ nch,
    catChunks ch w per nch = ∑ c ∈ Finset.range nch, ch c % 2 ^ (w * per) * 2 ^ ((w * per) * c)
  | 0 => rfl
  | nch + 1 => by
    rw [Finset.sum_range_succ, ← catChunks_eq ch w per nch]
    show Nat.add (catChunks ch w per nch) (Nat.shiftLeft (Nat.land (ch nch)
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul w per)) 1)) (Nat.mul (Nat.mul w per) nch)) = _
    rw [mask_eq, shl_eq, land_mask_eq]
    rfl

theorem div_pow_mod (a s w : ℕ) : a / 2 ^ s % 2 ^ w = a % 2 ^ (s + w) / 2 ^ s := by
  rw [pow_add, Nat.mod_mul_right_div_self]

/-- Slot `j` of the concatenated chunks is slot `j % per` of chunk `j / per`. -/
theorem slotAt_catChunks (ch : ℕ → ℕ) (w per nch j : ℕ) (hj : j < nch * per) :
    slotAt w (catChunks ch w per nch) j = slotAt w (ch (j / per)) (j % per) := by
  have hper : 0 < per := by
    rcases Nat.eq_zero_or_pos per with h | h
    · rw [h, mul_zero] at hj; exact absurd hj (Nat.not_lt_zero _)
    · exact h
  have hc0 : j / per < nch := by rw [Nat.div_lt_iff_lt_mul hper]; exact hj
  have hr : j % per < per := Nat.mod_lt _ hper
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw; simp [slotAt_eq', Nat.mod_one]
  have hle : w * (j % per) + w ≤ w * per := by
    have : w * (j % per + 1) ≤ w * per := Nat.mul_le_mul_left _ hr
    linarith [show w * (j % per + 1) = w * (j % per) + w by ring]
  have hdvd : 2 ^ (w * (j % per) + w) ∣ 2 ^ (w * per) := pow_dvd_pow 2 hle
  have hdig : ∀ c, c < nch → ch c % 2 ^ (w * per) < 2 ^ (w * per) := fun c _ => Nat.mod_lt _ (by positivity)
  have hslot := slot_digits (w * per) (Nat.mul_pos hw hper) (fun c => ch c % 2 ^ (w * per)) nch (j / per) hdig hc0
  rw [slotAt_eq'] at hslot
  have hj2 : 2 ^ (w * j) = 2 ^ (w * per * (j / per)) * 2 ^ (w * (j % per)) := by
    rw [← pow_add]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod j per]
    ring
  rw [slotAt_eq', slotAt_eq', catChunks_eq, hj2, ← Nat.div_div_eq_div_mul]
  set A := (∑ c ∈ Finset.range nch, ch c % 2 ^ (w * per) * 2 ^ (w * per * c)) / 2 ^ (w * per * (j / per)) with hA
  calc A / 2 ^ (w * (j % per)) % 2 ^ w = A % 2 ^ (w * (j % per) + w) / 2 ^ (w * (j % per)) := div_pow_mod _ _ _
    _ = A % 2 ^ (w * per) % 2 ^ (w * (j % per) + w) / 2 ^ (w * (j % per)) := by rw [Nat.mod_mod_of_dvd _ hdvd]
    _ = ch (j / per) % 2 ^ (w * per) % 2 ^ (w * (j % per) + w) / 2 ^ (w * (j % per)) := by rw [hslot]
    _ = ch (j / per) % 2 ^ (w * (j % per) + w) / 2 ^ (w * (j % per)) := by rw [Nat.mod_mod_of_dvd _ hdvd]
    _ = ch (j / per) / 2 ^ (w * (j % per)) % 2 ^ w := (div_pow_mod _ _ _).symm

theorem fieldRun_flat (ch : ℕ → ℕ) (w per nch : ℕ) : ∀ (count i : ℕ), i + count ≤ nch * per →
    fieldRun (fun _ => catChunks ch w per nch) w (nch * per) count i = fieldRun ch w per count i
  | 0, _, _ => rfl
  | count + 1, i, h => by
    simp only [fieldRun]
    rw [fieldRun_flat ch w per nch count (i + 1) (by omega),
      Nat.mod_eq_of_lt (show i < nch * per by omega), slotAt_catChunks ch w per nch i (by omega)]

theorem flat_klowL (d : CellData) (nchK nchF : ℕ → ℕ) (bi : ℕ)
    (hK : d.order bi * (d.order bi - 1) / 2 ≤ nchK bi * (d.layout bi).1) :
    (CellData.flat d nchK nchF).klowL bi = d.klowL bi := by
  unfold CellData.klowL
  show (fieldRun (fun _ => catChunks (d.klow bi) d.kw (d.layout bi).1 (nchK bi)) d.kw
    (nchK bi * (d.layout bi).1) (d.order bi * (d.order bi - 1) / 2) 0).map sdec = _
  rw [fieldRun_flat _ _ _ _ _ 0 (by rw [zero_add]; exact hK)]

theorem flat_facL (d : CellData) (nchK nchF : ℕ → ℕ) (bi u : ℕ)
    (hF : d.order bi * (d.order bi + 1) / 2 ≤ nchF bi * (d.layout bi).2.2) :
    (CellData.flat d nchK nchF).facL bi u = d.facL bi u := by
  unfold CellData.facL
  show (fieldRun (fun _ => catChunks (d.fac bi u) (d.layout bi).2.1 (d.layout bi).2.2 (nchF bi)) (d.layout bi).2.1
    (nchF bi * (d.layout bi).2.2) (d.order bi * (d.order bi + 1) / 2) 0).map sdec = _
  rw [fieldRun_flat _ _ _ _ _ 0 (by rw [zero_add]; exact hF)]

/-- **The flattened data decode the same literal block** (when the chunks hold the fields). -/
theorem flat_block (d : CellData) (nchK nchF : ℕ → ℕ) (bi : ℕ)
    (hK : d.order bi * (d.order bi - 1) / 2 ≤ nchK bi * (d.layout bi).1)
    (hF : d.order bi * (d.order bi + 1) / 2 ≤ nchF bi * (d.layout bi).2.2) :
    (CellData.flat d nchK nchF).block bi = d.block bi := by
  have hf : (List.range (d.nw + 1)).map ((CellData.flat d nchK nchF).facL bi) = (List.range (d.nw + 1)).map (d.facL bi) :=
    List.map_congr_left (fun u _ => flat_facL d nchK nchF bi u hF)
  show Literals.Block.mk "" (d.order bi) (d.kdiagL bi) ((CellData.flat d nchK nchF).klowL bi)
      ((List.range (d.nw + 1)).map ((CellData.flat d nchK nchF).facL bi)) =
    Literals.Block.mk "" (d.order bi) (d.kdiagL bi) (d.klowL bi) ((List.range (d.nw + 1)).map (d.facL bi))
  rw [flat_klowL d nchK nchF bi hK, hf]

theorem flat_cell (d : CellData) (nchK nchF : ℕ → ℕ) : (CellData.flat d nchK nchF).cell = d.cell := rfl

theorem litGram_congr {c : Literals.Cell} {B B' : Literals.Block} (h : B = B') (t : ℝ) (i j : ℕ)
    (hi : i < B.order) (hj : j < B.order) (hi' : i < B'.order) (hj' : j < B'.order) :
    literalGram c B t ⟨i, hi⟩ ⟨j, hj⟩ = literalGram c B' t ⟨i, hi'⟩ ⟨j, hj'⟩ := by
  subst h; rfl

theorem litW_congr {d d' : CellData} (bi i j : ℕ) (ho : d'.order bi = d.order bi) (hc : d'.cell = d.cell)
    (hb : d'.block bi = d.block bi) (t : ℝ) : litW d' bi i j t = litW d bi i j t := by
  unfold litW
  by_cases h : i < d.order bi ∧ j < d.order bi
  · have h' : i < d'.order bi ∧ j < d'.order bi := by rw [ho]; exact h
    rw [dif_pos h, dif_pos h', hc]
    exact litGram_congr hb t i j _ _ _ _
  · have h' : ¬ (i < d'.order bi ∧ j < d'.order bi) := by rw [ho]; exact h
    rw [dif_neg h, dif_neg h']

theorem litW_flat (d : CellData) (nchK nchF : ℕ → ℕ) (bi i j : ℕ)
    (hK : d.order bi * (d.order bi - 1) / 2 ≤ nchK bi * (d.layout bi).1)
    (hF : d.order bi * (d.order bi + 1) / 2 ≤ nchF bi * (d.layout bi).2.2) (t : ℝ) :
    litW (CellData.flat d nchK nchF) bi i j t = litW d bi i j t :=
  litW_congr (d := d) (d' := CellData.flat d nchK nchF) bi i j rfl rfl (flat_block d nchK nchF bi hK hF) t

theorem litW_out (d : CellData) (bi i j : ℕ) (h : ¬ (i < d.order bi ∧ j < d.order bi)) (t : ℝ) :
    litW d bi i j t = 0 := by
  unfold litW
  rw [dif_neg h]

/-- **The narrow entries of the flattened data enclose the literal Gram entries of the original data.** -/
theorem WTn_sound_flat {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (nchK nchF : ℕ → ℕ) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTn (CellData.flat d nchK nchF) (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  by_cases hin : i < d.order bi ∧ j < d.order bi
  · have h0 := WTn_ok_cond (CellData.flat d nchK nchF) _ bi i j hin.1 hin.2 hok
    have hc := w0Cond_of (CellData.flat d nchK nchF) bi (w0OkN_cond _ _ bi h0).1
    have hK : d.order bi * (d.order bi - 1) / 2 ≤ nchK bi * (d.layout bi).1 := hc.perK
    have hF : d.order bi * (d.order bi + 1) / 2 ≤ nchF bi * (d.layout bi).2.2 := by
      have := hc.perF; rw [tri_eq] at this; exact this
    exact (WTn_sound hg (CellData.flat d nchK nchF) bi i j hok).congr (fun t _ => litW_flat d nchK nchF bi i j hK hF t)
  · refine (WTn_sound hg (CellData.flat d nchK nchF) bi i j hok).congr (fun t _ => ?_)
    rw [litW_out (CellData.flat d nchK nchF) bi i j hin t, litW_out d bi i j hin t]

#print axioms dColB_slot
#print axioms winN_window
#print axioms WTn_sound
#print axioms WTn_symm
#print axioms flat_block
#print axioms WTn_sound_flat

end ThomsonCompact.CoeffMap.Deg
