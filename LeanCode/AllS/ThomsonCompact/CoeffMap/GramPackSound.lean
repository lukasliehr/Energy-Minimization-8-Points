import ThomsonCompact.CoeffMap.PackLemmas
import ThomsonCompact.CoeffMap.GramSound

/-!
# Soundness of the packed W0 entries (F2c)

For `w0Ok d c bi = true` (single chunks, `L ≤ S`, `nw ≤ N`, `e ≤ 2 mb`, entries below `2^sw`, a-priori bound):

* `ival_facEnt`, `ival_metEnt`: the kernel's entry readers decode `facL` / `metricRow` (`CellCodec`).
* `gPack_cast`: the packed column `G_q` is `Σ_{p<n} Σ_{k<M} czI k p · 2^(W (k + M p))` modulo `2^(W M n)`,
  `czI k p = coefI bi k p q · 2^(S-L)` (Kronecker identity of the factor/metric Gram columns and `U_u`).
* `czI_bound`: `|czI k p| ≤ crudeB` (slot widths, binomial bounds), so the biased decode has no borrows.
* `entryTM_sound`: entry `(p, q)` encloses the literal Gram entry exactly (error `0`), via `w0_entry`.
* `WTp_sound`: every `WTp d c bi i j` with `ok = true` encloses the (symmetric, zero-padded) literal entry.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open scoped BigOperators

/-! ## Triangular indices -/

theorem nshr (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k
theorem nshl (x k : ℕ) : Nat.shiftLeft x k = x * 2 ^ k := Nat.shiftLeft_eq x k
theorem nshr_one (x : ℕ) : Nat.shiftRight x 1 = x / 2 := by rw [nshr, pow_one]

theorem tri_eq (p : ℕ) : tri p = p * (p + 1) / 2 := by
  unfold tri
  rw [nshr]
  rfl

theorem tri_succ (p : ℕ) : (p + 1) * (p + 1 + 1) / 2 = p * (p + 1) / 2 + (p + 1) := by
  rw [show (p + 1) * (p + 1 + 1) = p * (p + 1) + (p + 1) * 2 by ring, Nat.add_mul_div_right _ _ (by norm_num)]

theorem tri_mono {p q : ℕ} (h : p ≤ q) : p * (p + 1) / 2 ≤ q * (q + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem tri_lt {l p n : ℕ} (hl : l ≤ p) (hp : p < n) : p * (p + 1) / 2 + l < n * (n + 1) / 2 := by
  have h1 := tri_succ p
  have h2 := tri_mono (show p + 1 ≤ n by omega)
  omega

theorem tri'_lt {l p n : ℕ} (hl : l < p) (hp : p < n) : p * (p - 1) / 2 + l < n * (n - 1) / 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show (r + 1) * r = r * (r + 1) by ring, show (m + 1) * m = m * (m + 1) by ring]
  exact tri_lt (by omega) (by omega)

/-! ## Slots and decoded fields -/

theorem slotAt_lt (w x i : ℕ) : slotAt w x i < 2 ^ w := by
  unfold slotAt
  have h : Nat.sub (Nat.shiftLeft 1 w) 1 = 2 ^ w - 1 := by
    rw [show Nat.shiftLeft 1 w = 1 <<< w from rfl, Nat.shiftLeft_eq, one_mul]
    rfl
  rw [h]
  exact lt_of_le_of_lt Nat.and_le_right (by have := Nat.two_pow_pos w; omega)

theorem fieldRun_getD (ch : ℕ → ℕ) (w per : ℕ) : ∀ (count i j : ℕ), j < count →
    (fieldRun ch w per count i).getD j 0 = slotAt w (ch ((i + j) / per)) ((i + j) % per)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => by simp [fieldRun]
  | count + 1, i, j + 1, h => by
    rw [fieldRun, List.getD_cons_succ, fieldRun_getD ch w per count (i + 1) j (by omega),
      show i + 1 + j = i + (j + 1) by ring]

theorem sdec_zero : sdec 0 = 0 := by decide

theorem fieldRun_getD0 (ch : ℕ → ℕ) (w per count j : ℕ) (hj : j < count) (hper : count ≤ per) :
    ((fieldRun ch w per count 0).map sdec).getD j 0 = sdec (slotAt w (ch 0) j) := by
  rw [getD_map_of_zero sdec 0 0 sdec_zero, fieldRun_getD ch w per count 0 j hj, zero_add,
    Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem ival_facEnt (d : CellData) (bi u p l : ℕ) (hl : l ≤ p) (hp : p < d.order bi)
    (hper : tri (d.order bi) ≤ (d.layout bi).2.2) :
    ival (facEnt d bi u p l) = (d.facL bi u).getD (p * (p + 1) / 2 + l) 0 := by
  unfold facEnt CellData.facL
  rw [ival_smSlot, fieldRun_getD0 _ _ _ _ _ (tri_lt hl hp) (by rw [← tri_eq]; exact hper), tri_eq]
  rfl

theorem facEnt_mag (d : CellData) (bi u p l : ℕ) : (facEnt d bi u p l).2 < 2 ^ ((d.layout bi).2.1 - 1) := by
  unfold facEnt smSlot
  have h := slotAt_lt (d.layout bi).2.1 (d.fac bi u 0) (Nat.add (tri p) l)
  dsimp only
  rw [nshr, pow_one]
  rcases Nat.eq_zero_or_pos (d.layout bi).2.1 with h0 | h0
  · rw [h0] at h ⊢; simp at h; simp [h]
  · rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ, Nat.sub_add_cancel h0]
    exact h

theorem klowL_getD (d : CellData) (bi i : ℕ) (hi : i < d.order bi * (d.order bi - 1) / 2)
    (hper : d.order bi * (d.order bi - 1) / 2 ≤ (d.layout bi).1) :
    (d.klowL bi).getD i 0 = sdec (slotAt d.kw (d.klow bi 0) i) := by
  unfold CellData.klowL
  exact fieldRun_getD0 _ _ _ _ _ hi hper

theorem kdiagL_getD (d : CellData) (bi r : ℕ) (hr : r < d.order bi) :
    (d.kdiagL bi).getD r 0 = Int.subNatNat (slotAt 9 (d.kdiag bi) r) 128 := by
  unfold CellData.kdiagL
  simp [List.getD_eq_getElem?_getD, hr]

theorem mb_diag (d : CellData) (bi r : ℕ) (hr : r < d.order bi) : 128 ≤ d.mb bi + slotAt 9 (d.kdiag bi) r := by
  have h := (mb_ge d bi).2 ((d.kdiagL bi).getD r 0) (by
    rw [List.getD_eq_getElem?_getD]
    have hl : r < (d.kdiagL bi).length := by simp [CellData.kdiagL, hr]
    simp only [List.getElem?_eq_getElem hl, Option.getD_some]
    exact List.getElem_mem hl)
  rw [kdiagL_getD d bi r hr, Int.subNatNat_eq_coe] at h
  omega

theorem ival_shift (z s : ℕ) :
    ival (Nat.beq (Nat.land z 1) 1, Nat.shiftLeft (Nat.shiftRight z 1) s) = sdec z * 2 ^ s := by
  rw [nshl]
  unfold ival sdec
  dsimp only
  by_cases h : Nat.land z 1 = 1
  · have hb : Nat.beq (Nat.land z 1) 1 = true := by rw [h]; rfl
    rw [if_pos hb, if_pos h, Int.ofNat_eq_natCast]
    push_cast
    ring
  · have hb : Nat.beq (Nat.land z 1) 1 = false := by
      cases hb' : Nat.beq (Nat.land z 1) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb') h
    rw [if_neg (by rw [hb]; exact Bool.false_ne_true), if_neg h, Int.ofNat_eq_natCast]
    push_cast
    ring

theorem ival_metEnt (d : CellData) (bi p l : ℕ) (hl : l ≤ p) (hp : p < d.order bi)
    (hper : d.order bi * (d.order bi - 1) / 2 ≤ (d.layout bi).1) :
    ival (metEnt d bi p l) = (d.metricRow bi p).getD l 0 := by
  rw [metricRow_getD]
  unfold metEnt
  by_cases hlp : l < p
  · have hidx : Nat.add (Nat.shiftRight (Nat.mul p (Nat.sub p 1)) 1) l = p * (p - 1) / 2 + l := by
      rw [nshr]
      rfl
    rw [show Nat.blt l p = true from Nat.blt_eq.mpr hlp, cond_true, if_pos hlp,
      klowL_getD d bi _ (tri'_lt hlp hp) hper, hidx]
    exact ival_shift _ _
  · have hlp' : l = p := by omega
    subst hlp'
    have hf : Nat.blt l l = false := by
      cases h' : Nat.blt l l
      · rfl
      · exact absurd (Nat.blt_eq.mp h') (lt_irrefl l)
    rw [hf, cond_false, if_neg (lt_irrefl l), if_pos rfl, kdiagL_getD d bi l hp]
    have h128 := mb_diag d bi l hp
    have hv : ival (false, Nat.shiftLeft 1 (Nat.sub (Nat.add (d.mb bi) (slotAt 9 (d.kdiag bi) l)) 128)) =
        ((2 ^ (d.mb bi + slotAt 9 (d.kdiag bi) l - 128) : ℕ) : ℤ) := by
      unfold ival
      dsimp only
      rw [if_neg Bool.false_ne_true, nshl, one_mul]
      rfl
    rw [hv, Int.subNatNat_eq_coe]
    have he : Int.toNat ((d.mb bi : ℤ) + ((slotAt 9 (d.kdiag bi) l : ℕ) - ((128 : ℕ) : ℤ))) =
        d.mb bi + slotAt 9 (d.kdiag bi) l - 128 := by omega
    rw [he]
    push_cast
    rfl

/-! ## Dot products -/

theorem dot_rows (f : ℕ → ℕ → ℤ) (rp rq : List ℤ) {n p q : ℕ} (hp : p < n) (hq : q < n)
    (hlp : rp.length ≤ n) (hrp : ∀ l, rp.getD l 0 = if l ≤ p then f p l else 0)
    (hrq : ∀ l, rq.getD l 0 = if l ≤ q then f q l else 0) :
    dotI rp rq = ∑ l ∈ Finset.range (q + 1), if l ≤ p then f q l * f p l else 0 := by
  rw [dotI_eq_sum rp rq n hlp, sum_range_extend _ (show q + 1 ≤ n by omega)]
  apply Finset.sum_congr rfl
  intro l _
  rw [hrp, hrq]
  by_cases h1 : l ≤ p <;> by_cases h2 : l ≤ q
  · rw [if_pos h1, if_pos h2, if_pos (by omega), if_pos h1]; ring
  · rw [if_pos h1, if_neg h2, if_neg (by omega)]; ring
  · rw [if_neg h1, if_pos h2, if_pos (by omega), if_neg h1]; ring
  · rw [if_neg h1, if_neg h2, if_neg (by omega)]; ring

theorem dotI_comm : ∀ xs ys : List ℤ, dotI xs ys = dotI ys xs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp only [dotI, dotI_comm xs ys, mul_comm]

theorem coefI_symm (d : CellData) (bi k i j : ℕ) : d.coefI bi k i j = d.coefI bi k j i := by
  unfold CellData.coefI
  rw [dotI_comm (d.metricRow bi i)]
  congr 2
  apply List.map_congr_left
  intro u _
  rw [dotI_comm (lowerRow (d.facL bi u) i)]

/-- The factor Gram entry as a dot product of the kernel's entries. -/
theorem dotF_eq (d : CellData) (bi u : ℕ) {p q : ℕ} (hp : p < d.order bi) (hq : q < d.order bi)
    (hper : tri (d.order bi) ≤ (d.layout bi).2.2) :
    dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) =
      ∑ l ∈ Finset.range (q + 1), if l ≤ p then ival (facEnt d bi u q l) * ival (facEnt d bi u p l) else 0 := by
  apply dot_rows (fun r l => ival (facEnt d bi u r l)) _ _ hp hq ((length_lowerRow _ _).trans (by omega))
  · intro l
    rw [getD_lowerRow]
    split_ifs with h
    · rw [ival_facEnt d bi u p l h hp hper]
    · rfl
  · intro l
    rw [getD_lowerRow]
    split_ifs with h
    · rw [ival_facEnt d bi u q l h hq hper]
    · rfl

theorem dotM_eq (d : CellData) (bi : ℕ) {p q : ℕ} (hp : p < d.order bi) (hq : q < d.order bi)
    (hper : d.order bi * (d.order bi - 1) / 2 ≤ (d.layout bi).1) :
    dotI (d.metricRow bi p) (d.metricRow bi q) =
      ∑ l ∈ Finset.range (q + 1), if l ≤ p then ival (metEnt d bi q l) * ival (metEnt d bi p l) else 0 := by
  have hlen : ∀ r, (d.metricRow bi r).length = r + 1 := by intro r; simp [CellData.metricRow]
  have hrow : ∀ r, r < d.order bi → ∀ l, (d.metricRow bi r).getD l 0 = if l ≤ r then ival (metEnt d bi r l) else 0 := by
    intro r hr l
    split_ifs with h
    · rw [ival_metEnt d bi r l h hr hper]
    · rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
  exact dot_rows (fun r l => ival (metEnt d bi r l)) _ _ hp hq (by rw [hlen]; omega) (hrow p hp) (hrow q hq)

/-! ## Bernstein weights -/

theorem bern8_ok : ((List.range 9).all fun u => (List.range 9).all fun k =>
    smSlot (slotAt 16 bern8 (Nat.add (Nat.mul 9 u) k)) == (decide (bernI 8 u k < 0), (bernI 8 u k).natAbs)) = true := by
  decide +kernel

theorem ival_sign (b : ℤ) : ival (decide (b < 0), b.natAbs) = b := by
  unfold ival
  by_cases h : b < 0
  · simp only [h, decide_true, if_true]
    rw [Int.ofNat_natAbs_of_nonpos h.le]
    ring
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    exact Int.natAbs_of_nonneg (not_lt.mp h)

theorem ival_bernE (nw u k : ℕ) (hu : u ≤ nw) (hk : k ≤ nw) : ival (bernE nw u k) = bernI nw u k := by
  unfold bernE
  by_cases h8 : nw = 8
  · subst h8
    have h := bern8_ok
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    rw [show Nat.beq 8 8 = true from rfl, cond_true, h u (by omega) k (by omega), ival_sign]
  · have hb : Nat.beq nw 8 = false := by
      cases hb' : Nat.beq nw 8
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb') h8
    rw [hb, cond_false, ival_sign]

theorem uAcc_cast (W nw u sh : ℕ) : ∀ j,
    ((uAcc W nw u sh j).1 : ℤ) - ((uAcc W nw u sh j).2 : ℤ) =
      ∑ k ∈ Finset.range j, ival (bernE nw u k) * 2 ^ (sh + W * k)
  | 0 => by simp [uAcc]
  | j + 1 => by
    rw [Finset.sum_range_succ, ← uAcc_cast W nw u sh j]
    show ((cond (bernE nw u j).1 ((uAcc W nw u sh j).1,
        Nat.add (Nat.shiftLeft (bernE nw u j).2 (Nat.add sh (Nat.mul W j))) (uAcc W nw u sh j).2)
      (Nat.add (Nat.shiftLeft (bernE nw u j).2 (Nat.add sh (Nat.mul W j))) (uAcc W nw u sh j).1,
        (uAcc W nw u sh j).2)).1 : ℤ) - ((cond (bernE nw u j).1 ((uAcc W nw u sh j).1,
        Nat.add (Nat.shiftLeft (bernE nw u j).2 (Nat.add sh (Nat.mul W j))) (uAcc W nw u sh j).2)
      (Nat.add (Nat.shiftLeft (bernE nw u j).2 (Nat.add sh (Nat.mul W j))) (uAcc W nw u sh j).1,
        (uAcc W nw u sh j).2)).2 : ℤ) = _
    have hs : Nat.shiftLeft (bernE nw u j).2 (Nat.add sh (Nat.mul W j)) = (bernE nw u j).2 * 2 ^ (sh + W * j) :=
      Nat.shiftLeft_eq _ _
    rw [hs]
    unfold ival
    cases h : (bernE nw u j).1
    · simp only [cond_false, Bool.false_eq_true, if_false]
      push_cast [show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl]
      ring
    · simp only [cond_true, if_true]
      push_cast [show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl]
      ring

theorem uPair_cast (W nw u sh : ℕ) (hu : u ≤ nw) :
    ((uPair W nw u sh).1 : ℤ) - ((uPair W nw u sh).2 : ℤ) =
      ∑ k ∈ Finset.range (nw + 1), bernI nw u k * 2 ^ (sh + W * k) := by
  unfold uPair
  rw [show Nat.add nw 1 = nw + 1 from rfl, uAcc_cast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ival_bernE nw u k hu (by have := Finset.mem_range.mp hk; omega)]

/-! ## The Gram column identity -/

/-- TM-scale Gram coefficient `coefI · 2^(S-L)` of entry `(p, q)`, power `k`. -/
def czI (d : CellData) (c : Ctx) (bi q k p : ℕ) : ℤ := d.coefI bi k p q * 2 ^ (c.S - d.scaleL bi)

theorem coefI_expand (d : CellData) (bi k i j : ℕ) :
    d.coefI bi k i j = (if k = 0 then 2 ^ (d.scaleL bi - scaleM d bi) * dotI (d.metricRow bi i) (d.metricRow bi j)
      else 0) + ∑ u ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
        dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j) := by
  unfold CellData.coefI
  rw [show ((List.range (d.nw + 1)).map fun u => bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
      dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j)).foldr (· + ·) 0 =
      ((List.range (d.nw + 1)).map fun u => bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
      dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j)).sum from rfl, list_sum_range]
  rfl

/-- The algebra of the Kronecker identity (`M = nw + 1` factors and powers, `n` rows). -/
theorem gram_alg (n M W S L Lf Lm : ℕ) (hM : 0 < M) (hLf : Lf ≤ L) (hLm : Lm ≤ L) (hL : L ≤ S)
    (b : ℕ → ℕ → ℤ) (dF : ℕ → ℕ → ℤ) (dM : ℕ → ℤ) :
    ∑ u ∈ Finset.range M, (∑ k ∈ Finset.range M, b u k * 2 ^ ((S - Lf) + W * k)) *
        (∑ p ∈ Finset.range n, dF u p * 2 ^ (W * M * p)) +
      (∑ p ∈ Finset.range n, dM p * 2 ^ (W * M * p)) * 2 ^ (S - Lm) =
    ∑ p ∈ Finset.range n, ∑ k ∈ Finset.range M, ((if k = 0 then 2 ^ (L - Lm) * dM p else 0) +
        ∑ u ∈ Finset.range M, b u k * 2 ^ (L - Lf) * dF u p) * 2 ^ (S - L) * 2 ^ (W * (k + M * p)) := by
  have hA : ∀ p, ∑ k ∈ Finset.range M, (if k = 0 then 2 ^ (L - Lm) * dM p else 0) * 2 ^ (S - L) *
      2 ^ (W * (k + M * p)) = dM p * 2 ^ (W * M * p) * 2 ^ (S - Lm) := by
    intro p
    rw [Finset.sum_eq_single 0]
    · rw [if_pos rfl, zero_add, show W * (M * p) = W * M * p by ring,
        show (2 : ℤ) ^ (S - Lm) = 2 ^ (L - Lm) * 2 ^ (S - L) by rw [← pow_add]; congr 1; omega]
      ring
    · intro k _ hk
      rw [if_neg hk]
      ring
    · intro h
      exact absurd (Finset.mem_range.mpr hM) h
  have hB : ∀ p k, (∑ u ∈ Finset.range M, b u k * 2 ^ (L - Lf) * dF u p) * 2 ^ (S - L) * 2 ^ (W * (k + M * p)) =
      ∑ u ∈ Finset.range M, b u k * 2 ^ ((S - Lf) + W * k) * (dF u p * 2 ^ (W * M * p)) := by
    intro p k
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [show (2 : ℤ) ^ ((S - Lf) + W * k) = 2 ^ (L - Lf) * 2 ^ (S - L) * 2 ^ (W * k) by
        rw [← pow_add, ← pow_add]; congr 1; omega,
      show W * (k + M * p) = W * k + W * M * p by ring, pow_add]
    ring
  have hR : ∀ p, ∑ k ∈ Finset.range M, ((if k = 0 then 2 ^ (L - Lm) * dM p else 0) +
      ∑ u ∈ Finset.range M, b u k * 2 ^ (L - Lf) * dF u p) * 2 ^ (S - L) * 2 ^ (W * (k + M * p)) =
      dM p * 2 ^ (W * M * p) * 2 ^ (S - Lm) +
        ∑ k ∈ Finset.range M, ∑ u ∈ Finset.range M, b u k * 2 ^ ((S - Lf) + W * k) * (dF u p * 2 ^ (W * M * p)) := by
    intro p
    rw [← hA p, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hB p k]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hR p), Finset.sum_add_distrib, add_comm, Finset.sum_mul]
  congr 1
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm), Finset.sum_comm]
  exact Finset.sum_congr rfl (fun u _ => Finset.sum_comm)

theorem gAcc_cast (d : CellData) (c : Ctx) (bi q : ℕ) (K : ℕ) (htw : (geo d c bi).2.2.2 = 2 ^ K) : ∀ j,
    ((gAcc d c bi q j : ℕ) : ZMod (2 ^ K)) =
      ∑ u ∈ Finset.range j, (((uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).1 : ℤ) -
          ((uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).2 : ℤ) : ZMod (2 ^ K)) *
        (dPack (facEnt d bi u) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q : ZMod (2 ^ K))
  | 0 => by simp [gAcc]
  | j + 1 => by
    rw [Finset.sum_range_succ, ← gAcc_cast d c bi q K htw j]
    show ((Nat.add (Nat.add
      (Nat.mul (uPair c.W d.nw j (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).1
        (dPack (facEnt d bi j) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q))
      (Nat.mul (uPair c.W d.nw j (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).2
        (Nat.sub (geo d c bi).2.2.2
          (dPack (facEnt d bi j) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q))))
      (gAcc d c bi q j) : ℕ) : ZMod (2 ^ K)) = _
    have hlt : dPack (facEnt d bi j) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q ≤ 2 ^ K := by
      unfold dPack; rw [htw]; exact (land_mask_lt _ _).le
    rw [htw] at hlt ⊢
    simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul]
    rw [natCast_sub_pow hlt]
    push_cast
    ring

/-! ## The block check -/

/-- The conditions of `w0Ok` (with `c = mkCtx N S B W`, `sw = W (nw + 1)`). -/
structure W0Cond (d : CellData) (N S B W bi : ℕ) : Prop where
  perF : tri (d.order bi) ≤ (d.layout bi).2.2
  perK : d.order bi * (d.order bi - 1) / 2 ≤ (d.layout bi).1
  LS : d.scaleL bi ≤ S
  nwN : d.nw ≤ N
  he : d.floorExp ≤ 2 * (d.mb bi : ℤ)
  wf : (d.layout bi).2.1 ≤ W * (d.nw + 1)
  mx : mxK d bi < W * (d.nw + 1)
  crude : (N + 1) * crudeB d (mkCtx N S B W) bi < 2 ^ (W - 1)

theorem w0Cond_of {N S B W : ℕ} (d : CellData) (bi : ℕ) (h : w0Ok d (mkCtx N S B W) bi = true) :
    W0Cond d N S B W bi := by
  unfold w0Ok at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, by rw [← nshr_one]; exact h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Entry magnitudes -/

theorem smaxAcc_ge (d : CellData) (bi : ℕ) : ∀ k r, r < k → slotAt 9 (d.kdiag bi) r ≤ smaxAcc d bi k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, r, h => by
    show slotAt 9 (d.kdiag bi) r ≤ Nat.max (smaxAcc d bi k) (slotAt 9 (d.kdiag bi) k)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact (smaxAcc_ge d bi k r h').trans (Nat.le_max_left _ _)
    · rw [h']; exact Nat.le_max_right _ _

theorem metEnt_mag (d : CellData) (bi p l : ℕ) (hl : l ≤ p) (hp : p < d.order bi) :
    (metEnt d bi p l).2 ≤ 2 ^ mxK d bi := by
  unfold metEnt mxK
  by_cases hlp : l < p
  · rw [show Nat.blt l p = true from Nat.blt_eq.mpr hlp, cond_true]
    dsimp only
    rw [nshl, nshr, pow_one]
    have hz := slotAt_lt d.kw (d.klow bi 0) (Nat.add (Nat.shiftRight (Nat.mul p (Nat.sub p 1)) 1) l)
    have h1 : slotAt d.kw (d.klow bi 0) (Nat.add (Nat.shiftRight (Nat.mul p (Nat.sub p 1)) 1) l) / 2 ≤
        2 ^ (d.kw - 1) := by
      have h2 : 2 ^ d.kw ≤ 2 ^ (d.kw - 1) * 2 := by
        rcases Nat.eq_zero_or_pos d.kw with h0 | h0
        · rw [h0]; norm_num
        · rw [← pow_succ, Nat.sub_add_cancel h0]
      omega
    calc slotAt d.kw (d.klow bi 0) (Nat.add (Nat.shiftRight (Nat.mul p (Nat.sub p 1)) 1) l) / 2 * 2 ^ (d.mb bi - d.mbits)
        ≤ 2 ^ (d.kw - 1) * 2 ^ (d.mb bi - d.mbits) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (d.kw - 1 + (d.mb bi - d.mbits)) := by rw [pow_add]
      _ ≤ 2 ^ (Nat.max (Nat.add (Nat.sub d.kw 1) (Nat.sub (d.mb bi) d.mbits))
            (Nat.sub (Nat.add (d.mb bi) (smaxK d bi)) 128)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _)
  · have hf : Nat.blt l p = false := by
      cases h' : Nat.blt l p
      · rfl
      · exact absurd (Nat.blt_eq.mp h') hlp
    rw [hf, cond_false]
    dsimp only
    rw [nshl, one_mul]
    have hs := smaxAcc_ge d bi (d.order bi) p hp
    apply Nat.pow_le_pow_right (by norm_num)
    refine le_trans ?_ (Nat.le_max_right _ _)
    show d.mb bi + slotAt 9 (d.kdiag bi) p - 128 ≤ d.mb bi + smaxAcc d bi (d.order bi) - 128
    omega

/-! ## The packed column as an integer polynomial -/

theorem geo_eq (d : CellData) (W N S B bi : ℕ) : geo d (mkCtx N S B W) bi =
    (d.order bi, d.nw + 1, W * (d.nw + 1), 2 ^ (W * (d.nw + 1) * d.order bi)) := rfl

theorem fac_hb {N S B W : ℕ} (d : CellData) (bi u : ℕ) (hc : W0Cond d N S B W bi) :
    ∀ p l, l ≤ p → p < d.order bi →
      (facEnt d bi u p l).2 * 2 ^ (W * (d.nw + 1) * p) ≤ 2 ^ (W * (d.nw + 1) * d.order bi) := by
  intro p l _ hp
  have h1 := facEnt_mag d bi u p l
  have h2 : 2 ^ ((d.layout bi).2.1 - 1) ≤ 2 ^ (W * (d.nw + 1)) := Nat.pow_le_pow_right (by norm_num) (by
    have := hc.wf; omega)
  calc (facEnt d bi u p l).2 * 2 ^ (W * (d.nw + 1) * p) ≤ 2 ^ (W * (d.nw + 1)) * 2 ^ (W * (d.nw + 1) * p) :=
        Nat.mul_le_mul_right _ (h1.le.trans h2)
    _ = 2 ^ (W * (d.nw + 1) * (p + 1)) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (W * (d.nw + 1) * d.order bi) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hp)

theorem met_hb {N S B W : ℕ} (d : CellData) (bi : ℕ) (hc : W0Cond d N S B W bi) :
    ∀ p l, l ≤ p → p < d.order bi →
      (metEnt d bi p l).2 * 2 ^ (W * (d.nw + 1) * p) ≤ 2 ^ (W * (d.nw + 1) * d.order bi) := by
  intro p l hl hp
  have h1 := metEnt_mag d bi p l hl hp
  have h2 : 2 ^ mxK d bi ≤ 2 ^ (W * (d.nw + 1)) := Nat.pow_le_pow_right (by norm_num) hc.mx.le
  calc (metEnt d bi p l).2 * 2 ^ (W * (d.nw + 1) * p) ≤ 2 ^ (W * (d.nw + 1)) * 2 ^ (W * (d.nw + 1) * p) :=
        Nat.mul_le_mul_right _ (h1.trans h2)
    _ = 2 ^ (W * (d.nw + 1) * (p + 1)) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (W * (d.nw + 1) * d.order bi) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hp)

/-- **The packed Gram column is the integer polynomial of the TM-scale coefficients** (modulo `2^(W M n)`). -/
theorem gPack_cast {N S B W : ℕ} (d : CellData) (bi q : ℕ) (hq : q < d.order bi) (hc : W0Cond d N S B W bi) :
    ((gPack d (mkCtx N S B W) bi q : ℕ) : ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) =
      ((∑ p ∈ Finset.range (d.order bi), ∑ k ∈ Finset.range (d.nw + 1),
        czI d (mkCtx N S B W) bi q k p * 2 ^ (W * (k + (d.nw + 1) * p)) : ℤ) : ZMod _) := by
  have htw : (geo d (mkCtx N S B W) bi).2.2.2 = 2 ^ (W * (d.nw + 1) * d.order bi) := rfl
  unfold gPack
  rw [htw, natCast_land_mask, show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl, Nat.cast_add, nshl,
    Nat.cast_mul, gAcc_cast d (mkCtx N S B W) bi q _ htw]
  dsimp only [geo]
  simp only [mk_W, mk_S, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq]
  rw [dPack_cast _ _ _ _ q (met_hb d bi hc)]
  simp_rw [dPack_cast _ _ _ _ q (fac_hb d bi _ hc)]
  have hU : ∀ u ∈ Finset.range (d.nw + 1),
      ((((uPair W d.nw u (S - (2 * d.fb + d.nw))).1 : ℤ) : ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) -
        (((uPair W d.nw u (S - (2 * d.fb + d.nw))).2 : ℤ) : ZMod (2 ^ (W * (d.nw + 1) * d.order bi)))) =
      (((∑ k ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ ((S - (2 * d.fb + d.nw)) + W * k) : ℤ)) :
        ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) := by
    intro u hu
    rw [← Int.cast_sub, uPair_cast W d.nw u _ (by have := Finset.mem_range.mp hu; omega)]
  have hdF : ∀ u, ∀ p ∈ Finset.range (d.order bi),
      (((∑ l ∈ Finset.range (q + 1), if l ≤ p then ival (facEnt d bi u q l) * ival (facEnt d bi u p l) else 0 : ℤ)) :
        ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) =
        ((dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q) : ℤ) : ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) := by
    intro u p hp
    rw [dotF_eq d bi u (Finset.mem_range.mp hp) hq hc.perF]
  have hdM : ∀ p ∈ Finset.range (d.order bi),
      (((∑ l ∈ Finset.range (q + 1), if l ≤ p then ival (metEnt d bi q l) * ival (metEnt d bi p l) else 0 : ℤ)) :
        ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) =
        ((dotI (d.metricRow bi p) (d.metricRow bi q) : ℤ) : ZMod (2 ^ (W * (d.nw + 1) * d.order bi))) := by
    intro p hp
    rw [dotM_eq d bi (Finset.mem_range.mp hp) hq hc.perK]
  rw [Finset.sum_congr rfl (fun u hu => congrArg₂ (· * ·) (hU u hu)
    (Finset.sum_congr rfl (fun p hp => congrArg₂ (· * ·) (hdF u p hp) rfl)))]
  rw [Finset.sum_congr rfl (fun p hp => congrArg₂ (· * ·) (hdM p hp) rfl)]
  have hLf : 2 * d.fb + d.nw ≤ d.scaleL bi := Nat.le_max_left _ _
  have hLm : scaleM d bi ≤ d.scaleL bi := Nat.le_max_right _ _
  have halg := gram_alg (d.order bi) (d.nw + 1) W S (d.scaleL bi) (2 * d.fb + d.nw) (scaleM d bi) (by omega)
    hLf hLm hc.LS (bernI d.nw) (fun u p => dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q))
    (fun p => dotI (d.metricRow bi p) (d.metricRow bi q))
  have hcz : ∀ k p, czI d (mkCtx N S B W) bi q k p = ((if k = 0 then 2 ^ (d.scaleL bi - scaleM d bi) *
      dotI (d.metricRow bi p) (d.metricRow bi q) else 0) + ∑ u ∈ Finset.range (d.nw + 1),
        bernI d.nw u k * 2 ^ (d.scaleL bi - (2 * d.fb + d.nw)) *
          dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q)) * 2 ^ (S - d.scaleL bi) := by
    intro k p
    unfold czI
    rw [coefI_expand, show d.scaleL bi - 2 * d.fb - d.nw = d.scaleL bi - (2 * d.fb + d.nw) by omega]
    rfl
  simp_rw [hcz]
  rw [← halg]
  push_cast
  ring

/-! ## The a-priori slot bound -/

theorem chooseI_le (n k : ℕ) : (chooseI n k : ℤ) ≤ 2 ^ n := by
  rw [chooseI_eq]
  exact_mod_cast Nat.choose_le_two_pow n k

theorem bernI_bound (nw u k : ℕ) (hu : u ≤ nw) : |bernI nw u k| ≤ (nw + 1) * 4 ^ nw := by
  unfold bernI
  rw [show ((List.range (Nat.min u k + 1)).map fun j => (if (k - j) % 2 = 0 then (1 : ℤ) else -1) *
      (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ)).foldr (· + ·) 0 =
      ((List.range (Nat.min u k + 1)).map fun j => (if (k - j) % 2 = 0 then (1 : ℤ) else -1) *
      (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ)).sum from rfl, list_sum_range, abs_mul]
  have h1 : |(chooseI nw u : ℤ)| ≤ 2 ^ nw := by
    rw [abs_of_nonneg (by positivity)]
    exact chooseI_le nw u
  have h2 : |∑ j ∈ Finset.range (Nat.min u k + 1), (if (k - j) % 2 = 0 then (1 : ℤ) else -1) *
      (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ)| ≤ (nw + 1) * 2 ^ nw := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range (Nat.min u k + 1), |(if (k - j) % 2 = 0 then (1 : ℤ) else -1) *
        (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ)| ≤ 2 ^ nw := by
      intro j _
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ chooseI u j by positivity),
        abs_of_nonneg (show (0 : ℤ) ≤ chooseI (nw - u) (k - j) by positivity),
        show |(if (k - j) % 2 = 0 then (1 : ℤ) else -1)| = 1 by split_ifs <;> simp, one_mul]
      calc (chooseI u j : ℤ) * chooseI (nw - u) (k - j) ≤ 2 ^ u * 2 ^ (nw - u) :=
            mul_le_mul (chooseI_le u j) (chooseI_le _ _) (by positivity) (by positivity)
        _ = 2 ^ nw := by rw [← pow_add]; congr 1; omega
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ((Nat.min u k + 1 : ℕ) : ℤ) ≤ nw + 1 := by
      have : Nat.min u k ≤ nw := (Nat.min_le_left u k).trans hu
      exact_mod_cast (show Nat.min u k + 1 ≤ nw + 1 by omega)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  calc |(chooseI nw u : ℤ)| * _ ≤ 2 ^ nw * ((nw + 1) * 2 ^ nw) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (nw + 1) * 4 ^ nw := by
        rw [show (4 : ℤ) ^ nw = 2 ^ nw * 2 ^ nw by rw [← mul_pow]; norm_num]
        ring

theorem dot_bound (f : ℕ → ℕ → ℤ) {n p q : ℕ} (hp : p < n) (hq : q < n) (Bx : ℤ) (hB0 : 0 ≤ Bx)
    (hB : ∀ r l, l ≤ r → r < n → |f r l| ≤ Bx) :
    |∑ l ∈ Finset.range (q + 1), if l ≤ p then f q l * f p l else 0| ≤ n * Bx ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ l ∈ Finset.range (q + 1), |(if l ≤ p then f q l * f p l else 0)| ≤ Bx ^ 2 := by
    intro l hl
    have hl' := Finset.mem_range.mp hl
    split_ifs with h
    · rw [abs_mul, sq]
      exact mul_le_mul (hB q l (by omega) hq) (hB p l h hp) (abs_nonneg _) hB0
    · simp only [abs_zero]
      positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show q + 1 ≤ n by omega)) (by positivity)

theorem crudeB_eq {N S B W : ℕ} (d : CellData) (bi : ℕ) :
    (crudeB d (mkCtx N S B W) bi : ℤ) =
      (d.nw + 1) * (d.nw + 1) * 4 ^ d.nw * (d.order bi * 4 ^ ((d.layout bi).2.1 - 1)) *
          2 ^ (S - (2 * d.fb + d.nw)) +
        d.order bi * 4 ^ mxK d bi * 2 ^ (S - scaleM d bi) := by
  unfold crudeB
  simp only [nshl, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq, mk_S]
  push_cast
  ring

/-- **A-priori bound of every slot of the packed column.** -/
theorem czI_bound {N S B W : ℕ} (d : CellData) (bi q k p : ℕ) (hk : k ≤ d.nw) (hp : p < d.order bi)
    (hq : q < d.order bi) (hc : W0Cond d N S B W bi) :
    |czI d (mkCtx N S B W) bi q k p| ≤ crudeB d (mkCtx N S B W) bi := by
  have hLf : 2 * d.fb + d.nw ≤ d.scaleL bi := Nat.le_max_left _ _
  have hLm : scaleM d bi ≤ d.scaleL bi := Nat.le_max_right _ _
  have hL := hc.LS
  have hdF : ∀ u, |dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q)| ≤
      d.order bi * (2 ^ ((d.layout bi).2.1 - 1)) ^ 2 := by
    intro u
    rw [dotF_eq d bi u hp hq hc.perF]
    refine dot_bound (fun r l => ival (facEnt d bi u r l)) hp hq _ (by positivity) ?_
    intro r l _ _
    rw [abs_ival]
    exact_mod_cast (facEnt_mag d bi u r l).le
  have hdM : |dotI (d.metricRow bi p) (d.metricRow bi q)| ≤ d.order bi * (2 ^ mxK d bi) ^ 2 := by
    rw [dotM_eq d bi hp hq hc.perK]
    refine dot_bound (fun r l => ival (metEnt d bi r l)) hp hq _ (by positivity) ?_
    intro r l hl hr
    rw [abs_ival]
    exact_mod_cast metEnt_mag d bi r l hl hr
  unfold czI
  rw [coefI_expand, crudeB_eq, abs_mul]
  simp only [mk_S]
  rw [abs_of_nonneg (show (0 : ℤ) ≤ 2 ^ (S - d.scaleL bi) by positivity)]
  have hA : |(if k = 0 then 2 ^ (d.scaleL bi - scaleM d bi) * dotI (d.metricRow bi p) (d.metricRow bi q) else 0 : ℤ)|
      ≤ 2 ^ (d.scaleL bi - scaleM d bi) * (d.order bi * (2 ^ mxK d bi) ^ 2) := by
    split_ifs
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hdM (by positivity)
    · simp only [abs_zero]
      positivity
  have hF : |∑ u ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
      dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q)| ≤
      (d.nw + 1) * ((d.nw + 1) * 4 ^ d.nw * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
        (d.order bi * (2 ^ ((d.layout bi).2.1 - 1)) ^ 2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ u ∈ Finset.range (d.nw + 1), |bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
        dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q)| ≤
        (d.nw + 1) * 4 ^ d.nw * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
          (d.order bi * (2 ^ ((d.layout bi).2.1 - 1)) ^ 2) := by
      intro u hu
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (bernI_bound d.nw u k
        (by have := Finset.mem_range.mp hu; omega)) (by positivity)) (hdF u) (abs_nonneg _) (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_refl _
  calc |(if k = 0 then 2 ^ (d.scaleL bi - scaleM d bi) * dotI (d.metricRow bi p) (d.metricRow bi q) else 0) +
        ∑ u ∈ Finset.range (d.nw + 1), bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
          dotI (lowerRow (d.facL bi u) p) (lowerRow (d.facL bi u) q)| * 2 ^ (S - d.scaleL bi)
      ≤ (2 ^ (d.scaleL bi - scaleM d bi) * (d.order bi * (2 ^ mxK d bi) ^ 2) +
          (d.nw + 1) * ((d.nw + 1) * 4 ^ d.nw * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
            (d.order bi * (2 ^ ((d.layout bi).2.1 - 1)) ^ 2))) * 2 ^ (S - d.scaleL bi) :=
        mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add hA hF)) (by positivity)
    _ = _ := by
        have e1 : (2 : ℤ) ^ (d.scaleL bi - scaleM d bi) * 2 ^ (S - d.scaleL bi) = 2 ^ (S - scaleM d bi) := by
          rw [← pow_add]; congr 1; omega
        have e2 : (2 : ℤ) ^ (d.scaleL bi - 2 * d.fb - d.nw) * 2 ^ (S - d.scaleL bi) = 2 ^ (S - (2 * d.fb + d.nw)) := by
          rw [← pow_add]; congr 1; omega
        have e3 : ∀ x : ℕ, ((2 : ℤ) ^ x) ^ 2 = 4 ^ x := fun x => by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [e3, e3]
        linear_combination (d.order bi * 4 ^ mxK d bi : ℤ) * e1 +
          ((d.nw + 1) * (d.nw + 1) * 4 ^ d.nw * (d.order bi * 4 ^ ((d.layout bi).2.1 - 1)) : ℤ) * e2

/-! ## Decoding the biased column -/

/-- The integer slots of column `q` (`k + M p ↦ czI k p`). -/
def zsL (d : CellData) (c : Ctx) (bi q : ℕ) : List ℤ :=
  (List.range ((d.nw + 1) * d.order bi)).map fun i => czI d c bi q (i % (d.nw + 1)) (i / (d.nw + 1))

theorem zsL_length (d : CellData) (c : Ctx) (bi q : ℕ) : (zsL d c bi q).length = (d.nw + 1) * d.order bi := by
  simp [zsL]

theorem idx_lt {M n k p : ℕ} (hk : k < M) (hp : p < n) : k + M * p < M * n := by
  have : M * p + M ≤ M * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left M hp
  omega

theorem horner_zsL {N S B W : ℕ} (d : CellData) (bi q : ℕ) :
    horner (2 ^ W : ℤ) (zsL d (mkCtx N S B W) bi q) = ∑ p ∈ Finset.range (d.order bi),
      ∑ k ∈ Finset.range (d.nw + 1), czI d (mkCtx N S B W) bi q k p * 2 ^ (W * (k + (d.nw + 1) * p)) := by
  rw [horner_eq_sum, zsL_length, sum_range_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hi := idx_lt hk' (Finset.mem_range.mp hp)
  rw [zsL, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk', Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hk', zero_add, ← pow_mul]

theorem zsL_bound {N S B W : ℕ} (d : CellData) (bi q : ℕ) (hq : q < d.order bi) (hc : W0Cond d N S B W bi) :
    ∀ x ∈ zsL d (mkCtx N S B W) bi q, |x| ≤ crudeB d (mkCtx N S B W) bi := by
  intro x hx
  simp only [zsL, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hM : 0 < d.nw + 1 := by omega
  exact czI_bound d bi q _ _ (by have := Nat.mod_lt i hM; omega)
    ((Nat.div_lt_iff_lt_mul hM).mpr (by rw [mul_comm]; exact hi)) hq hc

theorem crude_lt {N S B W : ℕ} (d : CellData) (bi : ℕ) (hc : W0Cond d N S B W bi) :
    (crudeB d (mkCtx N S B W) bi : ℤ) < 2 ^ (W - 1) := by
  have h := hc.crude
  have : crudeB d (mkCtx N S B W) bi < 2 ^ (W - 1) := by nlinarith
  exact_mod_cast this

/-- The biased column is the digit list of the biased slots. -/
theorem gPackB_eq {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi q : ℕ) (hq : q < d.order bi)
    (hc : W0Cond d N S B W bi) :
    gPackB d (mkCtx N S B W) bi q =
      Nat.ofDigits (2 ^ W) ((zsL d (mkCtx N S B W) bi q).map fun x => (x + 2 ^ (W - 1)).toNat) := by
  have hb : ∀ x ∈ zsL d (mkCtx N S B W) bi q, |x| < 2 ^ (W - 1) :=
    fun x hx => lt_of_le_of_lt (zsL_bound d bi q hq hc x hx) (crude_lt d bi hc)
  have hV : (gPack d (mkCtx N S B W) bi q : ℤ) % 2 ^ (W * (d.nw + 1) * d.order bi) =
      horner (2 ^ W : ℤ) (zsL d (mkCtx N S B W) bi q) % 2 ^ (W * (d.nw + 1) * d.order bi) := by
    have h := gPack_cast d bi q hq hc
    rw [← horner_zsL, ← Int.cast_natCast] at h
    have h2 := (ZMod.intCast_eq_intCast_iff' _ _ _).mp h
    push_cast at h2
    exact h2
  have hm := mod_biased hg.W1 (show W * ((d.nw + 1) * d.order bi) ≤ W * (d.nw + 1) * d.order bi by rw [mul_assoc])
    (zsL d (mkCtx N S B W) bi q) (zsL_length _ _ _ _) hb _ hV
  unfold gPackB
  rw [show (geo d (mkCtx N S B W) bi).2.2.2 = 2 ^ (W * (d.nw + 1) * d.order bi) from rfl, land_mask_eq,
    show (mkCtx N S B W).hW = 2 ^ (W - 1) from rfl, show (mkCtx N S B W).W = W from rfl,
    show Nat.mul (geo d (mkCtx N S B W) bi).2.1 (geo d (mkCtx N S B W) bi).1 = (d.nw + 1) * d.order bi from rfl]
  exact hm

/-- Window `p` of the biased column: the biased slots `czI k p + 2^(W-1)`, `k < M`. -/
theorem window_eq {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hp : p < d.order bi)
    (hq : q < d.order bi) (hc : W0Cond d N S B W bi) :
    Nat.land (Nat.shiftRight (gPackB d (mkCtx N S B W) bi q) (Nat.mul (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1)) p))
        (Nat.sub (Nat.pow 2 (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1))) 1) =
      Nat.ofDigits (2 ^ W) ((List.range (d.nw + 1)).map fun k =>
        (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) := by
  have hW0 : 0 < W := by have := hg.W1; omega
  have hb : ∀ x ∈ zsL d (mkCtx N S B W) bi q, |x| < 2 ^ (W - 1) :=
    fun x hx => lt_of_le_of_lt (zsL_bound d bi q hq hc x hx) (crude_lt d bi hc)
  have hdig : ∀ x ∈ (zsL d (mkCtx N S B W) bi q).map (fun x => (x + 2 ^ (W - 1)).toNat), x < 2 ^ W := by
    apply offset_digits_lt
    intro x hx
    have hH : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      exact pow_succ' 2 (W - 1)
    have := abs_lt.mp (hb x hx)
    constructor <;> [linarith; (rw [hH]; linarith)]
  rw [gPackB_eq hg d bi q hq hc, nshr, show Nat.sub (Nat.pow 2 (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1))) 1 =
      Nat.sub (2 ^ (W * (d.nw + 1))) 1 from rfl, land_mask_eq,
    show Nat.mul (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1)) p = W * ((d.nw + 1) * p) by
      show W * (d.nw + 1) * p = _; ring,
    (ofDigits_take_drop hW0 _ hdig ((d.nw + 1) * p)).2]
  have hdig2 : ∀ x ∈ ((zsL d (mkCtx N S B W) bi q).map (fun x => (x + 2 ^ (W - 1)).toNat)).drop ((d.nw + 1) * p),
      x < 2 ^ W := fun x hx => hdig x (List.mem_of_mem_drop hx)
  rw [(ofDigits_take_drop hW0 _ hdig2 (d.nw + 1)).1]
  congr 1
  apply List.ext_getElem
  · simp [zsL_length]
    have : (d.nw + 1) * p + (d.nw + 1) ≤ (d.nw + 1) * d.order bi := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hp
    omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range, zsL]
    have hk : k < d.nw + 1 := by simpa using h2
    rw [show (d.nw + 1) * p + k = k + (d.nw + 1) * p by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk, zero_add]

/-! ## Entry soundness -/

theorem entryTM_eq (c : Ctx) (M Gb p : ℕ) (ok0 : Bool) : entryTM c M Gb p ok0 =
    ⟨Nat.land (Nat.add (Nat.land (Nat.shiftRight Gb (Nat.mul (Nat.mul c.W M) p)) (Nat.sub (Nat.pow 2 (Nat.mul c.W M)) 1))
      (Nat.sub c.twoK (Nat.mul c.hW (ones c.W M)))) c.maskK,
     pabs c ⟨Nat.land (Nat.add (Nat.land (Nat.shiftRight Gb (Nat.mul (Nat.mul c.W M) p))
      (Nat.sub (Nat.pow 2 (Nat.mul c.W M)) 1)) (Nat.sub c.twoK (Nat.mul c.hW (ones c.W M)))) c.maskK, 0, 0, 0, true⟩,
     ssum c (pabs c ⟨Nat.land (Nat.add (Nat.land (Nat.shiftRight Gb (Nat.mul (Nat.mul c.W M) p))
      (Nat.sub (Nat.pow 2 (Nat.mul c.W M)) 1)) (Nat.sub c.twoK (Nat.mul c.hW (ones c.W M)))) c.maskK, 0, 0, 0, true⟩),
     0,
     Nat.blt (ssum c (pabs c ⟨Nat.land (Nat.add (Nat.land (Nat.shiftRight Gb (Nat.mul (Nat.mul c.W M) p))
      (Nat.sub (Nat.pow 2 (Nat.mul c.W M)) 1)) (Nat.sub c.twoK (Nat.mul c.hW (ones c.W M)))) c.maskK, 0, 0, 0, true⟩))
      c.twoB && ok0⟩ := rfl

/-- **A packed W0 entry TM with `ok = true` encloses the literal Gram entry exactly** (error `0`). -/
theorem entryTM_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi p q : ℕ) (hpq : p ≤ q)
    (hq : q < d.order bi)
    (hok : (entryTM (mkCtx N S B W) (Nat.add d.nw 1) (gPackB d (mkCtx N S B W) bi q) p
      (w0Ok d (mkCtx N S B W) bi)).ok = true) :
    Encl (mkCtx N S B W) (entryTM (mkCtx N S B W) (Nat.add d.nw 1) (gPackB d (mkCtx N S B W) bi q) p
      (w0Ok d (mkCtx N S B W) bi))
      (fun t => literalGram d.cell (d.block bi) t ⟨p, lt_of_le_of_lt hpq hq⟩ ⟨q, hq⟩) := by
  have hp : p < d.order bi := lt_of_le_of_lt hpq hq
  have hW1 := hg.W1
  rw [entryTM_eq] at hok ⊢
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨hsB, hok0⟩ := hok
  have hc := w0Cond_of d bi hok0
  have hM : d.nw + 1 ≤ N + 1 := by have := hc.nwN; omega
  -- the coefficient lists
  set cs0 : List ℤ := (List.range (d.nw + 1)).map fun k => czI d (mkCtx N S B W) bi q k p with hcs0
  set cs : List ℤ := cs0 ++ List.replicate (N + 1 - (d.nw + 1)) 0 with hcsdef
  have hlen0 : cs0.length = d.nw + 1 := by simp [hcs0]
  have hlen : cs.length = N + 1 := by simp [hcsdef, hlen0]; omega
  have hcsb : ∀ x ∈ cs, |x| ≤ crudeB d (mkCtx N S B W) bi := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [hcs0, List.mem_map, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact czI_bound d bi q k p (by omega) hp hq hc
    · rw [List.eq_of_mem_replicate hx, abs_zero]
      positivity
  have hcl := crude_lt d bi hc
  have hcs : ∀ x ∈ cs, |x| < 2 ^ (W - 1) := fun x hx => lt_of_le_of_lt (hcsb x hx) hcl
  have hnn0 : ∀ x ∈ cs0, 0 ≤ x + 2 ^ (W - 1) := by
    intro x hx
    have := abs_lt.mp (hcs x (List.mem_append_left _ hx))
    linarith
  -- the value field
  have hwin := window_eq hg d bi p q hp hq hc
  have hwin' : Nat.ofDigits (2 ^ W) ((List.range (d.nw + 1)).map fun k =>
      (czI d (mkCtx N S B W) bi q k p + 2 ^ (W - 1)).toNat) = Nat.ofDigits (2 ^ W) (cs0.map fun x => (x + 2 ^ (W - 1)).toNat) := by
    rw [hcs0, List.map_map]
    rfl
  rw [hwin'] at hwin
  have hcast := cast_ofDigits_offset (by omega : 0 < W) (2 ^ (W - 1)) cs0 hnn0
  rw [hlen0] at hcast
  have hK : W * (d.nw + 1) ≤ W * (2 * N + 1) := Nat.mul_le_mul_left _ (by omega)
  have hones : 2 ^ (W - 1) * ones W (d.nw + 1) ≤ 2 ^ (W * (2 * N + 1)) := by
    rw [← ofDigits_replicate (by omega)]
    have hd : ∀ x ∈ List.replicate (d.nw + 1) (2 ^ (W - 1)), x < 2 ^ W := by
      intro x hx
      rw [List.eq_of_mem_replicate hx]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := ofDigits_lt_pow (by omega) _ hd
    rw [List.length_replicate] at this
    exact this.le.trans (Nat.pow_le_pow_right (by norm_num) hK)
  set V := Nat.land (Nat.add (Nat.land (Nat.shiftRight (gPackB d (mkCtx N S B W) bi q)
      (Nat.mul (Nat.mul (mkCtx N S B W).W (Nat.add d.nw 1)) p)) (Nat.sub (Nat.pow 2 (Nat.mul (mkCtx N S B W).W
      (Nat.add d.nw 1))) 1)) (Nat.sub (mkCtx N S B W).twoK (Nat.mul (mkCtx N S B W).hW (ones (mkCtx N S B W).W
      (Nat.add d.nw 1))))) (mkCtx N S B W).maskK with hVdef
  have hv : (V : ℤ) = horner (2 ^ W : ℤ) cs % 2 ^ (W * (2 * N + 1)) := by
    rw [hVdef, hwin, show (mkCtx N S B W).maskK = Nat.sub (2 ^ (W * (2 * N + 1))) 1 from rfl, land_mask_eq,
      show (mkCtx N S B W).twoK = 2 ^ (W * (2 * N + 1)) from rfl, show (mkCtx N S B W).hW = 2 ^ (W - 1) from rfl,
      show (mkCtx N S B W).W = W from rfl, show Nat.add d.nw 1 = d.nw + 1 from rfl,
      show ∀ a b : ℕ, Nat.add a b = a + b from fun _ _ => rfl, show ∀ a b : ℕ, Nat.mul a b = a * b from fun _ _ => rfl,
      show ∀ a b : ℕ, Nat.sub a b = a - b from fun _ _ => rfl]
    rw [Int.natCast_mod, Nat.cast_add, Nat.cast_sub hones, hcast, hcsdef, horner_append_zeros]
    push_cast
    rw [show horner (2 ^ W : ℤ) cs0 + 2 ^ (W - 1) * (ones W (d.nw + 1) : ℤ) +
        (2 ^ (W * (2 * N + 1)) - 2 ^ (W - 1) * (ones W (d.nw + 1) : ℤ)) =
        horner (2 ^ W : ℤ) cs0 + 2 ^ (W * (2 * N + 1)) * 1 by ring, Int.add_mul_emod_self_left]
  -- exact magnitudes
  have hVmod : (V : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) cs % 2 ^ (W * (2 * N + 1)) := by
    rw [hv, Int.emod_emod]
  have hnn : ∀ x ∈ cs, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
    have hH2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      exact pow_succ' 2 (W - 1)
    intro x hx
    have := abs_lt.mp (hcs x hx)
    constructor <;> [linarith; (rw [hH2]; linarith)]
  have hbias : (V + 2 ^ (W - 1) * ones W (N + 1)) &&& (2 ^ (W * (2 * N + 1)) - 1) =
      Nat.ofDigits (2 ^ W) (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)) := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact mod_biased hW1 (Nat.mul_le_mul_left W (by omega : N + 1 ≤ 2 * N + 1)) cs hlen hcs V hVmod
  have hdig := offset_digits_lt (2 ^ (W - 1)) hnn
  have hl2 : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).length = N + 1 := by simp [hlen]
  have hmap : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).map (fun d => (d - 2 ^ (W - 1)) + (2 ^ (W - 1) - d)) =
      cs.map Int.natAbs := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    have hc' : ((2 ^ (W - 1) : ℕ) : ℤ) = 2 ^ (W - 1) := by push_cast; rfl
    have := absDigit_offset x (2 ^ (W - 1)) (by rw [hc']; exact (hnn x hx).1)
    rw [hc'] at this
    exact this
  have key := pabs_ofDigits hW1 (N + 1) _ hl2 hdig
  rw [hmap, ← hbias] at key
  have hpabs : pabs (mkCtx N S B W) ⟨V, 0, 0, 0, true⟩ = Nat.ofDigits (2 ^ W) (cs.map Int.natAbs) := by
    rw [← key]
    rfl
  have hsum : (cs.map Int.natAbs).sum ≤ (N + 1) * crudeB d (mkCtx N S B W) bi := by
    have h1 := List.sum_le_card_nsmul (cs.map Int.natAbs) (crudeB d (mkCtx N S B W) bi) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hcsb y hy
      rw [← Int.natCast_natAbs] at this
      exact_mod_cast this)
    rw [List.length_map, hlen, smul_eq_mul] at h1
    exact h1
  have hssum : ssum (mkCtx N S B W) (pabs (mkCtx N S B W) ⟨V, 0, 0, 0, true⟩) = (cs.map Int.natAbs).sum := by
    rw [hpabs]
    show Nat.ofDigits (2 ^ W) (cs.map Int.natAbs) % (2 ^ W - 1) = _
    apply ofDigits_mod_pred (by have := hg.BW; have := hg.B1; omega)
    have h1 := hc.crude
    have h2 : 2 ^ (W - 1) ≤ 2 ^ W - 1 := by
      have : 2 ^ W = 2 * 2 ^ (W - 1) := by
        conv_lhs => rw [show W = (W - 1) + 1 by omega]
        exact pow_succ' 2 (W - 1)
      have := Nat.one_le_two_pow (n := W - 1)
      omega
    omega
  -- the representation and the enclosure
  refine ⟨cs, cs.map Int.natAbs, ⟨by simp [hlen], by simp [hlen], hv, hpabs, ?_, hssum, ?_⟩, ?_⟩
  · intro k
    rw [getD_map_of_zero Int.natAbs 0 0 rfl, Int.natCast_natAbs]
  · show ssum (mkCtx N S B W) (pabs (mkCtx N S B W) ⟨V, 0, 0, 0, true⟩) < 2 ^ B
    exact hsB
  · intro t _
    show |literalGram d.cell (d.block bi) t ⟨p, hp⟩ ⟨q, hq⟩ - evalZ cs t / 2 ^ S| ≤ ((0 : ℕ) : ℝ) / 2 ^ S
    rw [w0_entry d bi hc.he t ⟨p, hp⟩ ⟨q, hq⟩]
    have hev : evalZ cs t = ∑ k ∈ Finset.range (d.nw + 1), (czI d (mkCtx N S B W) bi q k p : ℝ) * t ^ k := by
      unfold evalZ
      rw [hcsdef, List.map_append, List.map_replicate, Int.cast_zero, horner_append_zeros, horner_eq_sum]
      simp only [List.length_map, hlen0]
      apply Finset.sum_congr rfl
      intro k hk
      rw [getD_map_of_zero (Int.cast : ℤ → ℝ) 0 0 Int.cast_zero, hcs0, List.getD_eq_getElem?_getD]
      simp [Finset.mem_range.mp hk]
    rw [hev]
    unfold scalarEval
    rw [Fin.sum_univ_eq_sum_range (fun k => ((mkRat (d.coefI bi k p q) (2 ^ d.scaleL bi) : ℚ) : ℝ) * t ^ k), Finset.sum_div]
    have hterm : ∀ k ∈ Finset.range (d.nw + 1), ((mkRat (d.coefI bi k p q) (2 ^ d.scaleL bi) : ℚ) : ℝ) * t ^ k -
        (czI d (mkCtx N S B W) bi q k p : ℝ) * t ^ k / 2 ^ S = 0 := by
      intro k _
      unfold czI
      rw [Rat.mkRat_eq_div, show (mkCtx N S B W).S = S from rfl]
      push_cast
      have hL := hc.LS
      have h2 : (2 : ℝ) ^ S = 2 ^ d.scaleL bi * 2 ^ (S - d.scaleL bi) := by rw [← pow_add]; congr 1; omega
      rw [h2]
      field_simp
      ring
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero hterm, abs_zero]
    simp

/-! ## The packed W0 table -/

/-- The literal Gram entries of block `bi` on `ℕ` indices (zero outside the block). -/
noncomputable def litW (d : CellData) (bi i j : ℕ) (t : ℝ) : ℝ :=
  if h : i < d.order bi ∧ j < d.order bi then literalGram d.cell (d.block bi) t ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem literalGram_symm (d : CellData) (bi : ℕ) (he : d.floorExp ≤ 2 * (d.mb bi : ℤ)) (t : ℝ)
    (i j : Fin (d.block bi).order) : literalGram d.cell (d.block bi) t i j = literalGram d.cell (d.block bi) t j i := by
  rw [w0_entry d bi he t i j, w0_entry d bi he t j i]
  congr 1
  funext k
  rw [coefI_symm]

theorem wTab_lookup (d : CellData) (c : Ctx) (bi i j : ℕ) (hij : i ≤ j) (hj : j < d.order bi) :
    listAt zeroTM (listAt [] (wTab d c bi) j) i = entryTM c (Nat.add d.nw 1) (gPackB d c bi j) i (w0Ok d c bi) := by
  unfold wTab
  rw [listAt_mkList _ _ hj]
  unfold wCol
  exact listAt_mkList _ _ (show i < Nat.add j 1 by show i < j + 1; omega)

theorem wTab_lookup_ge (d : CellData) (c : Ctx) (bi i j : ℕ) (hj : d.order bi ≤ j) :
    listAt zeroTM (listAt [] (wTab d c bi) j) i = zeroTM := by
  unfold wTab
  rw [listAt_mkList_ge _ _ hj]
  rfl

/-- **The packed W0 TMs enclose the literal Gram entries** (symmetric, zero outside the block). -/
theorem WTp_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi i j : ℕ) :
    EnclOk (mkCtx N S B W) (WTp d (mkCtx N S B W) bi i j) (litW d bi i j) := by
  intro hok
  unfold WTp at hok ⊢
  by_cases hij : i ≤ j
  · rw [show Nat.ble i j = true from Nat.ble_eq.mpr hij, cond_true] at hok ⊢
    by_cases hj : j < d.order bi
    · rw [wTab_lookup d _ bi i j hij hj] at hok ⊢
      refine (entryTM_sound hg d bi i j hij hj hok).congr (fun t _ => ?_)
      unfold litW
      rw [dif_pos ⟨lt_of_le_of_lt hij hj, hj⟩]
    · rw [wTab_lookup_ge d _ bi i j (by omega)]
      refine zero_sound.congr (fun t _ => ?_)
      unfold litW
      rw [dif_neg (fun h => hj h.2)]
  · have hf : Nat.ble i j = false := by
      cases h' : Nat.ble i j
      · rfl
      · exact absurd (Nat.ble_eq.mp h') hij
    rw [hf, cond_false] at hok ⊢
    by_cases hi : i < d.order bi
    · rw [wTab_lookup d _ bi j i (by omega) hi] at hok ⊢
      have hc := w0Cond_of d bi (by
        rw [entryTM_eq] at hok
        simp only [Bool.and_eq_true] at hok
        exact hok.2)
      refine (entryTM_sound hg d bi j i (by omega) hi hok).congr (fun t _ => ?_)
      unfold litW
      rw [dif_pos ⟨hi, by omega⟩]
      exact literalGram_symm d bi hc.he t _ _
    · rw [wTab_lookup_ge d _ bi j i (by omega)]
      refine zero_sound.congr (fun t _ => ?_)
      unfold litW
      rw [dif_neg (fun h => hi h.1)]

#print axioms gPack_cast
#print axioms czI_bound
#print axioms entryTM_sound
#print axioms WTp_sound

end ThomsonCompact.CoeffMap
