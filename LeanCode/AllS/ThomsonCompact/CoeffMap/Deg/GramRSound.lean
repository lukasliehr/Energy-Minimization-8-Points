import ThomsonCompact.CoeffMap.Deg.GramNSound
import ThomsonCompact.CoeffMap.Deg.GramR

/-!
# Soundness of the row-oriented narrow W0 entries (F2g)

* `facEntR_eq`: the row reader returns the entries of `facEnt` (`l ≤ p`), so the narrow columns of `facEntR` decode the
  same dot products (`dotE_congr`, `dColB_slot`);
* `accR_cast`, `winR_eq`: the biased accumulation minus the per-block bias constants is the D12 window
  (`winR_window`), hence `entryN_window_sound` (any window equal to the D12 window encloses the literal entry);
* `WTr_sound`, `WTt_sound` (and `_flat` forms for `CellData.flat`): the row-oriented lookups enclose `litW`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

/-! ## Row reads -/

theorem slotAt_row (w x a k l : ℕ) (hl : l < k) :
    slotAt w (Nat.land (Nat.shiftRight x (Nat.mul w a)) (Nat.sub (Nat.shiftLeft 1 (Nat.mul w k)) 1)) l =
      slotAt w x (a + l) := by
  have hle : w * l + w ≤ w * k := by
    have : w * (l + 1) ≤ w * k := Nat.mul_le_mul_left _ hl
    linarith [show w * (l + 1) = w * l + w by ring]
  have hdvd : 2 ^ (w * l + w) ∣ 2 ^ (w * k) := pow_dvd_pow 2 hle
  rw [slotAt_eq', slotAt_eq', mask_eq, land_mask_eq, shr_eq]
  set z := x / 2 ^ (Nat.mul w a)
  calc z % 2 ^ (Nat.mul w k) / 2 ^ (w * l) % 2 ^ w = z % 2 ^ (w * k) % 2 ^ (w * l + w) / 2 ^ (w * l) :=
        div_pow_mod _ _ _
    _ = z % 2 ^ (w * l + w) / 2 ^ (w * l) := by rw [Nat.mod_mod_of_dvd _ hdvd]
    _ = z / 2 ^ (w * l) % 2 ^ w := (div_pow_mod _ _ _).symm
    _ = x / 2 ^ (w * (a + l)) % 2 ^ w := by
        rw [Nat.div_div_eq_div_mul, ← pow_add, mul_add]; rfl

theorem facEntR_eq (d : CellData) (bi u p l : ℕ) (hl : l ≤ p) : facEntR d bi u p l = facEnt d bi u p l := by
  unfold facEntR facRowR facEnt
  rw [slotAt_row _ _ _ _ _ (by show l < p + 1; omega)]
  rfl

theorem dotE_congr (e₁ e₂ : ℕ → ℕ → Bool × ℕ) (h : ∀ p l, l ≤ p → e₁ p l = e₂ p l) (p q : ℕ) :
    dotE e₁ p q = dotE e₂ p q := by
  unfold dotE
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  split_ifs with hlp
  · rw [h q l (by omega), h p l hlp]
  · rfl

theorem facEntR_mag (d : CellData) (bi u p l : ℕ) (hl : l ≤ p) :
    (facEntR d bi u p l).2 < 2 ^ ((d.layout bi).2.1 - 1) := by
  rw [facEntR_eq d bi u p l hl]; exact facEnt_mag d bi u p l

theorem facR_hb (d : CellData) (bi u : ℕ) (hn : NarrowCond d bi) :
    ∀ p l, l ≤ p → p < d.order bi →
      (facEntR d bi u p l).2 * 2 ^ (wnOf d bi * p) ≤ 2 ^ (wnOf d bi * d.order bi) := by
  intro p l hl hp
  rw [facEntR_eq d bi u p l hl]
  exact facE_hb d bi u hn p l hl hp

theorem facR_dot (d : CellData) (bi u q : ℕ) (hq : q < d.order bi) (hn : NarrowCond d bi) :
    ∀ p, p < d.order bi → |dotE (facEntR d bi u) p q| < 2 ^ (wnOf d bi - 1) := by
  intro p hp
  rw [dotE_congr _ _ (fun p l hl => facEntR_eq d bi u p l hl)]
  exact facE_dot d bi u q hq hn p hp

/-! ## The entry identity -/

theorem uSum_cast (c : Ctx) (d : CellData) : ∀ k,
    ((uSum c d k).1 : ℤ) = ∑ u ∈ Finset.range k, ((uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) ∧
    ((uSum c d k).2 : ℤ) = ∑ u ∈ Finset.range k, ((uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).2 : ℤ)
  | 0 => by simp [uSum]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := uSum_cast c d k
    have e1 : (uSum c d (k + 1)).1 =
        (uSum c d k).1 + (uPair c.W d.nw k (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 := rfl
    have e2 : (uSum c d (k + 1)).2 =
        (uSum c d k).2 + (uPair c.W d.nw k (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).2 := rfl
    rw [e1, e2, Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add, Nat.cast_add, h1, h2]
    exact ⟨rfl, rfl⟩

theorem accR_rec_cast (base : ℕ × ℕ) (y : ℕ → ℕ) (U : ℕ → ℕ × ℕ) : ∀ j,
    ((Nat.rec (motive := fun _ => ℕ × ℕ) base
        (fun u ih => (Nat.add ih.1 (Nat.mul (y u) (U u).1), Nat.add ih.2 (Nat.mul (y u) (U u).2))) j).1 : ℤ) -
      (Nat.rec (motive := fun _ => ℕ × ℕ) base
        (fun u ih => (Nat.add ih.1 (Nat.mul (y u) (U u).1), Nat.add ih.2 (Nat.mul (y u) (U u).2))) j).2 =
      ((base.1 : ℤ) - base.2) + ∑ u ∈ Finset.range j, (y u : ℤ) * (((U u).1 : ℤ) - (U u).2)
  | 0 => by simp
  | j + 1 => by
    rw [Finset.sum_range_succ, ← add_assoc, ← accR_rec_cast base y U j]
    show (((Nat.add _ (Nat.mul (y j) (U j).1) : ℕ)) : ℤ) - ((Nat.add _ (Nat.mul (y j) (U j).2) : ℕ) : ℤ) = _
    push_cast [show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl, show ∀ a b : ℕ, Nat.mul a b = a * b from fun _ _ => rfl]
    ring

/-- **The biased window of entry `(p, q)`** (row-oriented reader): the digits `czI k p + 2^(W-1)`. -/
theorem winR_eq {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi) (hc : W0Cond d N S B W bi) (hn : NarrowCond d bi) :
    winR d (mkCtx N S B W) bi p q = Nat.ofDigits (2 ^ W) ((List.range (d.nw + 1)).map fun k =>
        (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) := by
  have hW1 := hg.W1
  have h1 := wnOf_pos d bi
  set β : ℤ := 2 ^ (wnOf d bi - 1) with hβ
  -- the biased slots
  have hF : ∀ u, (slotAt (wnOf d bi) (dColB (facEntR d bi u) (wnOf d bi) (d.order bi) q) p : ℤ) =
      dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) + β := by
    intro u
    rw [dColB_slot _ _ _ q p h1 hp (facR_hb d bi u hn) (facR_dot d bi u q hq hn),
      dotE_congr _ _ (fun p l hl => facEntR_eq d bi u p l hl), dotF_eq d bi u hp hq hc.perF]
    rfl
  have hM : (slotAt (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p : ℤ) =
      dotI (d.metricRow bi p) (d.metricRow bi q) + β := by
    rw [dColB_slot _ _ _ q p h1 hp (metE_hb d bi hn) (metE_dot d bi q hq hn), dotM_eq d bi hp hq hc.perK]
    rfl
  -- the accumulators
  have hrec := accR_rec_cast
    (Nat.shiftLeft (slotAt (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p) (Nat.sub S (scaleM d bi)), 0)
    (fun u => slotAt (wnOf d bi) (dColB (facEntR d bi u) (wnOf d bi) (d.order bi) q) p)
    (fun u => uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))) (d.nw + 1)
  have hacc : accR d (mkCtx N S B W) bi p q = Nat.rec (motive := fun _ => ℕ × ℕ)
      (Nat.shiftLeft (slotAt (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p) (Nat.sub S (scaleM d bi)), 0)
      (fun u ih => (Nat.add ih.1 (Nat.mul (slotAt (wnOf d bi) (dColB (facEntR d bi u) (wnOf d bi) (d.order bi) q) p)
          (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1),
        Nat.add ih.2 (Nat.mul (slotAt (wnOf d bi) (dColB (facEntR d bi u) (wnOf d bi) (d.order bi) q) p)
          (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2))) (d.nw + 1) := rfl
  have hU : ∀ u ∈ Finset.range (d.nw + 1),
      (((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
        (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2) =
      ∑ k ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ ((S - (2 * d.fb + d.nw)) + W * k) := by
    intro u hu
    exact uPair_cast W d.nw u _ (by have := Finset.mem_range.mp hu; omega)
  -- the D12 entry algebra (as in `accN_cast`)
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
  have hZ : ∑ k ∈ Finset.range (d.nw + 1), czI d (mkCtx N S B W) bi q k p * 2 ^ (W * k) =
      ∑ u ∈ Finset.range (d.nw + 1), dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) *
        ((((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
          (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2)) +
      dotI (d.metricRow bi p) (d.metricRow bi q) * 2 ^ (S - scaleM d bi) := by
    simp_rw [hcz]
    rw [← halg]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [hU u hu]
    ring
  -- the biased sum
  have hsumU := uSum_cast (mkCtx N S B W) d (d.nw + 1)
  simp only [mk_W, mk_S] at hsumU
  have hkey : ((accR d (mkCtx N S B W) bi p q).1 : ℤ) - (accR d (mkCtx N S B W) bi p q).2 =
      ∑ k ∈ Finset.range (d.nw + 1), czI d (mkCtx N S B W) bi q k p * 2 ^ (W * k) +
        β * (((uSum (mkCtx N S B W) d (d.nw + 1)).1 : ℤ) - (uSum (mkCtx N S B W) d (d.nw + 1)).2 +
          2 ^ (S - scaleM d bi)) := by
    rw [hacc, hrec, hZ, hsumU.1, hsumU.2]
    simp only [Nat.cast_zero, sub_zero]
    have e2 : ((2 ^ Nat.sub S (scaleM d bi) : ℕ) : ℤ) = 2 ^ (S - scaleM d bi) := by simp
    rw [shl_eq, Nat.cast_mul, hM, e2]
    have hsplit : ∀ u ∈ Finset.range (d.nw + 1),
        (slotAt (wnOf d bi) (dColB (facEntR d bi u) (wnOf d bi) (d.order bi) q) p : ℤ) *
          (((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
            (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2) =
        dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) *
          ((((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
            (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2)) +
        β * (((uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
            (uPair W d.nw u (Nat.sub S (Nat.add (Nat.mul 2 d.fb) d.nw))).2) := by
      intro u _
      rw [hF u]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  -- the digits
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
  have hmap : (List.range (d.nw + 1)).map (fun k => (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) =
      cs0.map (fun x => (x + 2 ^ (W - 1)).toNat) := by
    rw [hcs0, List.map_map]; rfl
  rw [hmap]
  set D := Nat.ofDigits (2 ^ W) (cs0.map fun x => (x + 2 ^ (W - 1)).toNat) with hD
  have hβn : ((2 ^ (wnOf d bi - 1) : ℕ) : ℤ) = β := by push_cast; rfl
  have hfin : (accR d (mkCtx N S B W) bi p q).1 + 2 ^ (W - 1) * ones W (d.nw + 1) +
        2 ^ (wnOf d bi - 1) * (uSum (mkCtx N S B W) d (d.nw + 1)).2 =
      ((accR d (mkCtx N S B W) bi p q).2 + 2 ^ (wnOf d bi - 1) * ((uSum (mkCtx N S B W) d (d.nw + 1)).1 +
        2 ^ (S - scaleM d bi))) + D := by
    have : (((accR d (mkCtx N S B W) bi p q).1 + 2 ^ (W - 1) * ones W (d.nw + 1) +
        2 ^ (wnOf d bi - 1) * (uSum (mkCtx N S B W) d (d.nw + 1)).2 : ℕ) : ℤ) =
        ((((accR d (mkCtx N S B W) bi p q).2 + 2 ^ (wnOf d bi - 1) * ((uSum (mkCtx N S B W) d (d.nw + 1)).1 +
          2 ^ (S - scaleM d bi))) + D : ℕ) : ℤ) := by
      push_cast
      rw [hcast, hhor]
      rw [← hβn] at hkey
      push_cast at hkey
      linear_combination hkey
    exact_mod_cast this
  unfold winR
  simp only [shl_eq, one_mul]
  show (accR d (mkCtx N S B W) bi p q).1 + 2 ^ (W - 1) * ones W (d.nw + 1) +
      2 ^ (wnOf d bi - 1) * (uSum (mkCtx N S B W) d (d.nw + 1)).2 -
    ((accR d (mkCtx N S B W) bi p q).2 + 2 ^ (wnOf d bi - 1) * ((uSum (mkCtx N S B W) d (d.nw + 1)).1 +
      2 ^ (S - scaleM d bi))) = D
  rw [hfin, Nat.add_sub_cancel_left]

/-! ## Entries from a D12 window -/

/-- An entry TM whose window is the D12 window of column `q` at row `p` (any `p, q < n`) encloses the literal entry. -/
theorem entryN_window_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q Wv : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi)
    (hwin : w0OkN d (mkCtx N S B W) bi = true → Wv = Nat.ofDigits (2 ^ W) ((List.range (d.nw + 1)).map fun k =>
        (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat))
    (hok : (entryN (mkCtx N S B W) (Nat.add d.nw 1) Wv (w0OkN d (mkCtx N S B W) bi)).ok = true) :
    Encl (mkCtx N S B W) (entryN (mkCtx N S B W) (Nat.add d.nw 1) Wv (w0OkN d (mkCtx N S B W) bi)) (litW d bi p q) := by
  have h0 := entryN_ok _ _ _ _ hok
  have hc := w0Cond_of d bi (w0OkN_cond d _ bi h0).1
  have hW := hwin h0
  have heq : entryN (mkCtx N S B W) (Nat.add d.nw 1) Wv (w0OkN d (mkCtx N S B W) bi) =
      entryN (mkCtx N S B W) (Nat.add d.nw 1) (winN d (mkCtx N S B W) bi p q) (w0OkN d (mkCtx N S B W) bi) := by
    rw [hW, winN_eq hg d bi p q hp hq hc (w0OkN_cond d _ bi h0).2]
  rw [heq] at hok ⊢
  exact entryN_sound hg d bi p q hp hq hok

theorem winR_window {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi) (hok : w0OkN d (mkCtx N S B W) bi = true) :
    winR d (mkCtx N S B W) bi p q = Nat.ofDigits (2 ^ W) ((List.range (d.nw + 1)).map fun k =>
        (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) := by
  obtain ⟨h0, hn⟩ := w0OkN_cond d _ bi hok
  exact winR_eq hg d bi p q hp hq (w0Cond_of d bi h0) hn

/-! ## The row-oriented tables -/

theorem WTr_eq (d : CellData) (c : Ctx) (bi i j : ℕ) (hi : i < d.order bi) (hj : j < d.order bi) :
    WTr d c bi i j = entryN c (Nat.add d.nw 1) (winR d c bi j i) (w0OkN d c bi) := by
  unfold WTr wTabR
  rw [listAt_mkList _ _ hi]
  unfold wRowR
  exact listAt_mkList _ _ hj

theorem WTr_out (d : CellData) (c : Ctx) (bi i j : ℕ) (h : ¬ (i < d.order bi ∧ j < d.order bi)) :
    WTr d c bi i j = zeroTM := by
  unfold WTr wTabR
  by_cases hi : i < d.order bi
  · rw [listAt_mkList _ _ hi]
    unfold wRowR
    exact listAt_mkList_ge _ _ (by omega)
  · rw [listAt_mkList_ge _ _ (by omega)]; rfl

/-- **The row-oriented W0 TMs enclose the literal Gram entries** (zero outside the block). -/
theorem WTr_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTr d (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  by_cases hin : i < d.order bi ∧ j < d.order bi
  · rw [WTr_eq d _ bi i j hin.1 hin.2] at hok ⊢
    have h0 := entryN_ok _ _ _ _ hok
    have hc := w0Cond_of d bi (w0OkN_cond d _ bi h0).1
    refine (entryN_window_sound hg d bi j i _ hin.2 hin.1 (fun h => winR_window hg d bi j i hin.2 hin.1 h)
      hok).congr (fun t _ => ?_)
    unfold litW
    rw [dif_pos ⟨hin.2, hin.1⟩, dif_pos hin]
    exact literalGram_symm d bi hc.he t _ _
  · rw [WTr_out d _ bi i j hin]
    exact zero_sound.congr (fun t _ => by rw [litW_out d bi i j hin t])

theorem WTr_ok_cond (d : CellData) (c : Ctx) (bi i j : ℕ) (hi : i < d.order bi) (hj : j < d.order bi)
    (hok : (WTr d c bi i j).ok = true) : w0OkN d c bi = true := by
  rw [WTr_eq d c bi i j hi hj] at hok
  exact entryN_ok _ _ _ _ hok

/-- The row-oriented entries of the flattened data enclose the literal entries of the original data. -/
theorem WTr_sound_flat {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (nchK nchF : ℕ → ℕ) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTr (CellData.flat d nchK nchF) (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  by_cases hin : i < d.order bi ∧ j < d.order bi
  · have h0 := WTr_ok_cond (CellData.flat d nchK nchF) _ bi i j hin.1 hin.2 hok
    have hc := w0Cond_of (CellData.flat d nchK nchF) bi (w0OkN_cond _ _ bi h0).1
    have hK : d.order bi * (d.order bi - 1) / 2 ≤ nchK bi * (d.layout bi).1 := hc.perK
    have hF : d.order bi * (d.order bi + 1) / 2 ≤ nchF bi * (d.layout bi).2.2 := by
      have := hc.perF; rw [tri_eq] at this; exact this
    exact (WTr_sound hg (CellData.flat d nchK nchF) bi i j hok).congr (fun t _ => litW_flat d nchK nchF bi i j hK hF t)
  · refine (WTr_sound hg (CellData.flat d nchK nchF) bi i j hok).congr (fun t _ => ?_)
    rw [litW_out (CellData.flat d nchK nchF) bi i j hin t, litW_out d bi i j hin t]

theorem litW_symm' (d : CellData) (bi i j : ℕ) (t : ℝ) (he : ∀ hi : i < d.order bi ∧ j < d.order bi,
    d.floorExp ≤ 2 * (d.mb bi : ℤ)) : litW d bi i j t = litW d bi j i t := by
  unfold litW
  by_cases h : i < d.order bi ∧ j < d.order bi
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
    exact literalGram_symm d bi (he h) t _ _
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]

/-- The transposed lookup encloses the literal entries. -/
theorem WTt_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTt d (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  have h := WTr_sound hg d bi j i hok
  by_cases hin : i < d.order bi ∧ j < d.order bi
  · have h0 := WTr_ok_cond d _ bi j i hin.2 hin.1 hok
    have hc := w0Cond_of d bi (w0OkN_cond d _ bi h0).1
    exact h.congr (fun t _ => litW_symm' d bi j i t (fun _ => hc.he))
  · exact h.congr (fun t _ => by rw [litW_out d bi j i (fun h' => hin ⟨h'.2, h'.1⟩) t, litW_out d bi i j hin t])

theorem WTt_sound_flat {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (nchK nchF : ℕ → ℕ) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTt (CellData.flat d nchK nchF) (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  have h := WTr_sound_flat hg d nchK nchF bi j i hok
  by_cases hin : i < d.order bi ∧ j < d.order bi
  · have h0 := WTr_ok_cond (CellData.flat d nchK nchF) _ bi j i hin.2 hin.1 hok
    have hc := w0Cond_of (CellData.flat d nchK nchF) bi (w0OkN_cond _ _ bi h0).1
    have hc' : d.floorExp ≤ 2 * (d.mb bi : ℤ) := hc.he
    exact h.congr (fun t _ => litW_symm' d bi j i t (fun _ => hc'))
  · exact h.congr (fun t _ => by rw [litW_out d bi j i (fun h' => hin ⟨h'.2, h'.1⟩) t, litW_out d bi i j hin t])

#print axioms winR_eq
#print axioms WTr_sound
#print axioms WTr_sound_flat
#print axioms WTt_sound_flat

end ThomsonCompact.CoeffMap.Deg
