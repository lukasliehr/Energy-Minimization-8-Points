import ThomsonCompact.Fixed.SoundLoop

/-!
# Soundness of the fixed-table kernel, part 3: one leaf (workstream F4)

`leafOk_sound`: a passing leaf (with the one-time `tabOk`) gives, for every row `r < n` and every column
`i'` of its slice,

  `Σ_{k < n} lk Γ k · lk (N column k) r · horner (2^R) (Hc k i') = [r = i'] · sQ(B)`,

where `Hc k i'` is the coefficient list of the stored `H` entry (`[]` if absent; `hcoef`), together with the
coefficient bounds of every stored `H` entry of the slice (`CoefB`).
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-- Coefficient bounds of a polynomial. -/
def CoefB (Lmax wmax : Nat) (c : List ℤ) : Prop := c.length ≤ Lmax ∧ ∀ z ∈ c, |z| ≤ 2 ^ (wmax - 1)

theorem recCoeffs_bound (x Lmax wmax : Nat) (h1 : 1 ≤ hdrW x) (h2 : hdrW x ≤ wmax) (h3 : hdrL x ≤ Lmax) :
    CoefB Lmax wmax (recCoeffs x) := by
  refine ⟨by rw [length_recCoeffs]; exact h3, fun z hz => ?_⟩
  simp only [recCoeffs, List.mem_map, List.mem_reverse] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hs' := digitsN_lt _ _ _ s hs
  have e : (2 : ℕ) ^ hdrW x = 2 * 2 ^ (hdrW x - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hle : (2 : ℤ) ^ (hdrW x - 1) ≤ 2 ^ (wmax - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hs2 : (s : ℤ) < 2 * 2 ^ (hdrW x - 1) := by exact_mod_cast (e ▸ hs')
  rw [abs_le]; constructor <;> push_cast <;> omega

theorem polysOk_spec (R Lmax wmax hi : Nat) : ∀ (n lo x : Nat), 1 ≤ polysOk Lmax wmax hi n lo x →
    Inc lo (decPolys R n x) ∧ (∀ e ∈ decPolys R n x, e.1 < hi) ∧ (∀ e ∈ decPolysC n x, CoefB Lmax wmax e.2) ∧
      polysOk Lmax wmax hi n lo x = lastNext lo (decPolys R n x) + 1
  | 0, lo, x, _ => ⟨trivial, fun e he => by simp [decPolys] at he, fun e he => by simp [decPolysC] at he, rfl⟩
  | n + 1, lo, x, h => by
    have hv : polysOk Lmax wmax hi (n + 1) lo x = Bool.rec (motive := fun _ => Nat) 0
        (polysOk Lmax wmax hi n (Nat.add (Nat.land x 4095) 1) (Nat.shiftRight x (polyLen x)))
        (Nat.ble 1 (hdrW x) && Nat.ble (hdrW x) wmax && Nat.ble (hdrL x) Lmax &&
          Nat.ble lo (Nat.land x 4095) && Nat.blt (Nat.land x 4095) hi) := rfl
    have hd : decPolys R (n + 1) x = (Nat.land x 4095, polyVal R x) :: decPolys R n (Nat.shiftRight x (polyLen x)) :=
      rfl
    have hdc : decPolysC (n + 1) x = (Nat.land x 4095, recCoeffs x) :: decPolysC n (Nat.shiftRight x (polyLen x)) :=
      rfl
    rw [hd, hdc]
    cases hc : (Nat.ble 1 (hdrW x) && Nat.ble (hdrW x) wmax && Nat.ble (hdrL x) Lmax &&
          Nat.ble lo (Nat.land x 4095) && Nat.blt (Nat.land x 4095) hi)
    · rw [hv, hc] at h; exact absurd (show 1 ≤ 0 from h) (by omega)
    · rw [hv, hc] at h ⊢
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
      obtain ⟨i1, i2, i3, i4⟩ := polysOk_spec R Lmax wmax hi n _ _ h
      refine ⟨Inc.cons (Nat.le_of_ble_eq_true c4) (by simpa [nat_add] using i1), fun e he => ?_, fun e he => ?_,
        by simpa [lastNext, nat_add] using i4⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact Nat.blt_eq.mp c5
        · exact i2 e he
      · rcases List.mem_cons.mp he with rfl | he
        · exact recCoeffs_bound x Lmax wmax (Nat.le_of_ble_eq_true c1) (Nat.le_of_ble_eq_true c2)
            (Nat.le_of_ble_eq_true c3)
        · exact i3 e he

theorem polyVecOk_pos (Lmax wmax hi : Nat) (ch : Nat → Nat) : ∀ (n c lo1 : Nat),
    1 ≤ polyVecOk Lmax wmax hi ch n c lo1 → 1 ≤ lo1
  | 0, _, _, h => h
  | n + 1, c, lo1, h => by
    have hv : polyVecOk Lmax wmax hi ch (n + 1) c lo1 = Bool.rec (motive := fun _ => Nat) 0
        (polyVecOk Lmax wmax hi ch n (Nat.add c 1)
          (polysOk Lmax wmax hi (Nat.land (ch c) 255) (Nat.sub lo1 1) (Nat.shiftRight (ch c) 8)))
        (Nat.ble 1 lo1) := rfl
    cases hc : Nat.ble 1 lo1
    · rw [hv, hc] at h; exact absurd (show 1 ≤ 0 from h) (by omega)
    · exact Nat.le_of_ble_eq_true hc

theorem polyVecOk_spec (R Lmax wmax hi : Nat) (ch : Nat → Nat) : ∀ (n c lo1 : Nat),
    1 ≤ polyVecOk Lmax wmax hi ch n c lo1 →
    Inc (lo1 - 1) (decPolyVec R ch n c) ∧ (∀ e ∈ decPolyVec R ch n c, e.1 < hi) ∧
      ∀ e ∈ decPolyVecC ch n c, CoefB Lmax wmax e.2
  | 0, _, _, _ => ⟨trivial, fun e he => by simp [decPolyVec] at he, fun e he => by simp [decPolyVecC] at he⟩
  | n + 1, c, lo1, h => by
    have hv : polyVecOk Lmax wmax hi ch (n + 1) c lo1 = Bool.rec (motive := fun _ => Nat) 0
        (polyVecOk Lmax wmax hi ch n (Nat.add c 1)
          (polysOk Lmax wmax hi (Nat.land (ch c) 255) (Nat.sub lo1 1) (Nat.shiftRight (ch c) 8)))
        (Nat.ble 1 lo1) := rfl
    have hd : decPolyVec R ch (n + 1) c = decPolys R (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++
        decPolyVec R ch n (Nat.add c 1) := rfl
    have hdc : decPolyVecC ch (n + 1) c = decPolysC (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++
        decPolyVecC ch n (c + 1) := rfl
    have hlo := polyVecOk_pos Lmax wmax hi ch (n + 1) c lo1 h
    rw [hv, show Nat.ble 1 lo1 = true from Nat.ble_eq.mpr hlo] at h
    have hin := polyVecOk_pos Lmax wmax hi ch n _ _ h
    obtain ⟨a1, a2, a3, a4⟩ := polysOk_spec R Lmax wmax hi _ _ _ hin
    obtain ⟨b1, b2, b3⟩ := polyVecOk_spec R Lmax wmax hi ch n _ _ h
    rw [hd, hdc]
    refine ⟨Inc.append (by simpa [nat_sub] using a1) (by rw [a4] at b1; simpa [nat_sub] using b1),
      fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact a2 e he
      · exact b2 e he
    · rcases List.mem_append.mp he with he | he
      · exact a3 e he
      · exact b3 e (by simpa [nat_add] using he)

/-- Coefficient-list decode of the `H` slice row `k`. -/
def hrowC (S : Slice) (k : Nat) : List (Nat × List ℤ) := decPolyVecC (S.hc k) (S.hn k) 0

theorem sliceHdrOk_spec (T : Tab) (S : Slice) (h : sliceHdrOk T S = true) : ∀ k, k < T.n →
    Inc S.i0 (hrow T S k) ∧ (∀ e ∈ hrow T S k, e.1 < S.i0 + S.len) ∧ ∀ e ∈ hrowC S k, CoefB S.LH S.wH e.2 := by
  have key : ∀ m, Nat.rec (motive := fun _ => Bool) true
      (fun k ih => ih && Nat.ble 1 (polyVecOk S.LH S.wH (Nat.add S.i0 S.len) (S.hc k) (S.hn k) 0 (Nat.add S.i0 1))) m
      = true → ∀ k, k < m →
        Inc S.i0 (hrow T S k) ∧ (∀ e ∈ hrow T S k, e.1 < S.i0 + S.len) ∧ ∀ e ∈ hrowC S k, CoefB S.LH S.wH e.2 := by
    intro m
    induction m with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ m ih =>
      intro hm k hk
      have hm' : (Nat.rec (motive := fun _ => Bool) true
          (fun k ih => ih && Nat.ble 1 (polyVecOk S.LH S.wH (Nat.add S.i0 S.len) (S.hc k) (S.hn k) 0
            (Nat.add S.i0 1))) m &&
          Nat.ble 1 (polyVecOk S.LH S.wH (Nat.add S.i0 S.len) (S.hc m) (S.hn m) 0 (Nat.add S.i0 1))) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih hm'.1 k hk
      · obtain ⟨a, b, c⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ (Nat.le_of_ble_eq_true hm'.2)
        have e : Nat.add S.i0 1 - 1 = S.i0 := by rw [nat_add]; omega
        rw [e] at a
        exact ⟨a, fun x hx => by have := b x hx; rw [nat_add] at this; exact this, c⟩
  exact key T.n h

/-! ## Lists to sums -/

theorem list_sum_lk {n : Nat} (F : Nat → ℤ) : ∀ {lo : Nat} (l : List (Nat × Bool × Nat)), Inc lo l →
    (∀ e ∈ l, e.1 < n) → (l.map fun g => sv g.2 * F g.1).sum = ∑ k ∈ Finset.range n, lk l k * F k
  | _, [], _, _ => by simp
  | lo, e :: es, h, hn => by
    rw [List.map_cons, List.sum_cons, list_sum_lk F es h.tail (fun x hx => hn x (by simp [hx]))]
    simp only [lk_cons, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (hn e (by simp)))]

/-- Coefficient list of index `i` in a decoded coefficient vector (`[]` if absent). -/
def lookC (l : List (Nat × List ℤ)) (i : Nat) : List ℤ := ((l.find? fun e => e.1 = i).map Prod.snd).getD []

theorem lk_eq_horner (R : Nat) (hR : 0 < R) (l : List (Nat × Bool × Nat)) (lc : List (Nat × List ℤ))
    (hmap : l.map (fun e => (e.1, sv e.2)) = lc.map (fun e => (e.1, horner ((2 : ℤ) ^ R) e.2))) :
    ∀ {lo : Nat}, Inc lo l → ∀ i, lk l i = horner ((2 : ℤ) ^ R) (lookC lc i) := by
  induction l generalizing lc with
  | nil =>
    intro lo _ i
    cases lc with
    | nil => simp [lookC]
    | cons _ _ => simp at hmap
  | cons e es ih =>
    intro lo hinc i
    cases lc with
    | nil => simp at hmap
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hmap
      obtain ⟨⟨h1, h2⟩, h3⟩ := hmap
      rw [lk_cons]
      by_cases hi : e.1 = i
      · rw [if_pos hi, lk_of_lt hinc.tail (by omega), add_zero, h2]
        simp [lookC, ← h1, hi]
      · rw [if_neg hi, zero_add, ih cs h3 hinc.tail i]
        simp [lookC, List.find?_cons, ← h1, hi]

theorem lookC_mem {l : List (Nat × List ℤ)} {i : Nat} {P : List ℤ → Prop} (hP : P []) (h : ∀ e ∈ l, P e.2) :
    P (lookC l i) := by
  unfold lookC
  cases hf : l.find? (fun e => e.1 = i) with
  | none => exact hP
  | some e => exact h e (List.mem_of_find?_eq_some hf)

/-- Stored `H` entry `(k, i')` of slice `S` as a coefficient list. -/
def hcoef (S : Slice) (k i : Nat) : List ℤ := lookC (hrowC S k) i

/-- **One leaf.** -/
theorem leafOk_sound (T : Tab) (S : Slice) (hR : 0 < T.R) (hT : tabOk T = true) (hL : leafOk T S = true) :
    (∀ k i, k < T.n → CoefB S.LH S.wH (hcoef S k i)) ∧
    ∀ r p, r < T.n → p < S.len →
      ∑ k ∈ Finset.range T.n, lk (decValVec T.gc T.gn 0) k * (lk (ncol T k) r * horner ((2 : ℤ) ^ T.R)
        (hcoef S k (S.i0 + p))) = if r = S.i0 + p then (T.sq : ℤ) else 0 := by
  have hL' : (sliceHdrOk T S && rowsOk T.sq (colsGo T S (decValVec T.gc T.gn 0) (rep (rep (0, 0) S.len) T.n)) S.i0)
      = true := hL
  rw [Bool.and_eq_true] at hL'
  obtain ⟨⟨g1, g2⟩, hN⟩ := tabOk_spec T hT
  have hH := sliceHdrOk_spec T S hL'.1
  refine ⟨fun k i hk => lookC_mem ⟨by simp, by simp⟩ (hH k hk).2.2, fun r p hr hp => ?_⟩
  set gl := decValVec T.gc T.gn 0
  set Y0 := rep (rep ((0 : Nat), (0 : Nat)) S.len) T.n
  have hY0 : Shape S.len Y0 := fun r hr => by simp [Y0, rep_eq] at hr ⊢; simp [hr]
  have hY0l : Y0.length = T.n := by simp [Y0, rep_eq]
  have hg : ∀ g ∈ gl, Inc 0 (ncol T g.1) ∧ Inc S.i0 (hrow T S g.1) := fun g hg =>
    ⟨(hN g.1 (g2 g hg)).1, (hH g.1 (g2 g hg)).1⟩
  obtain ⟨c1, c2, c3⟩ := colsGo_get T S S.len gl Y0 hg hY0
  have hrow' := rowsAux_get T.sq S.i0 _ 0 hL'.2 r (by rw [c1, hY0l]; exact hr)
  have hv := sliceOk_get _ _ _ _ hrow' p (by rw [c2 r (by rw [c1, hY0l]; exact hr)]; exact hp)
  rw [c3 r p (by rw [hY0l]; exact hr) hp] at hv
  have h0 : ival ((Y0.getD r []).getD p (0, 0)) = 0 := by simp [Y0, rep_eq, hr, hp, ival]
  rw [h0, zero_add, zero_add] at hv
  have hsum : (gl.map fun g => sv g.2 * lk (ncol T g.1) r * lk (hrow T S g.1) (S.i0 + p)).sum =
      (gl.map fun g => sv g.2 * (fun k => lk (ncol T k) r * lk (hrow T S k) (S.i0 + p)) g.1).sum := by
    congr 1; apply List.map_congr_left; intro g _; simp only [mul_assoc]
  rw [← hv, hsum]
  symm
  refine (list_sum_lk (n := T.n) (fun k => lk (ncol T k) r * lk (hrow T S k) (S.i0 + p)) gl g1 g2).trans ?_
  apply Finset.sum_congr rfl
  intro k hk
  show lk gl k * (lk (ncol T k) r * lk (hrow T S k) (S.i0 + p)) = _
  rw [lk_eq_horner T.R hR (hrow T S k) (hrowC S k) (decPolyVec_sv T.R hR _ _ _) (hH k (Finset.mem_range.mp hk)).1]
  rfl

#print axioms leafOk_sound

end ThomsonCompact.Fixed
