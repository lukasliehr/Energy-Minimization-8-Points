import ThomsonCompact.Fixed.SoundT
import ThomsonCompact.Fixed.KernelSem

/-!
# Soundness of the one-time semantic checks (workstream F4)

* `rtagOk_spec`: distinct retained tag codes, none flagged non-retained (the hypotheses of `table_poly`);
* `dcOk_spec`: `Δc_k = S_{b,r} S_{b,c} rden_b`;
* `denOk_sound`: `den_d(t) cof_d(t) = ρ_d δ_{b_d}(t)` for all real `t`;
* `rfOk_sound`: `num(t) scD S δ_b(t) = κ(t) scN den(t)` for all real `t` and every scalar κ entry;
* `facOk_sound`: `Q(t) = ± Π f_r(t)^{e_r}` for all real `t`.
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-! ## Signed values -/

theorem seq_sv (x y : Bool × Nat) (h : seq x y = true) : sv x = sv y := by
  obtain ⟨s1, m1⟩ := x
  obtain ⟨s2, m2⟩ := y
  unfold seq at h
  cases s1 <;> cases s2 <;> simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true] at h <;>
    simp only [sv, Bool.false_eq_true, ↓reduceIte]
  · rw [Nat.eq_of_beq_eq_true h]
  · simp only [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2]; simp
  · simp only [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2]; simp
  · rw [Nat.eq_of_beq_eq_true h]

theorem sv_smulS (x y : Bool × Nat) : sv (smulS x y) = sv x * sv y := by
  unfold smulS; rw [nat_mul, sv_xor]

theorem sv_spow (x : Bool × Nat) : ∀ e, sv (spow x e) = sv x ^ e := by
  intro e
  obtain ⟨s, m⟩ := x
  unfold spow sv
  simp only [Nat.pow_eq]
  rcases Nat.even_or_odd e with he | he
  · have h1 : Nat.land e 1 = 0 := by
      rw [nat_land, Nat.and_one_is_mod]; exact Nat.even_iff.mp he
    rw [h1]
    cases s <;> simp [he.neg_pow]
  · have h1 : Nat.land e 1 = 1 := by
      rw [nat_land, Nat.and_one_is_mod]; exact Nat.odd_iff.mp he
    rw [h1]
    cases s <;> simp [he.neg_pow]

theorem recOk_coefB (Lm wm x : Nat) (h : recOk Lm wm x = true) : CoefB Lm wm (recCoeffs x) := by
  unfold recOk at h
  simp only [Bool.and_eq_true] at h
  exact recCoeffs_bound x Lm wm (Nat.le_of_ble_eq_true h.1.1) (Nat.le_of_ble_eq_true h.1.2) (Nat.le_of_ble_eq_true h.2)

/-! ## A two-sided lift -/

theorem lift_eq (R : ℕ) (hR : 0 < R) (P1 P2 : List ℤ) (h : horner ((2 : ℤ) ^ R) P1 = horner ((2 : ℤ) ^ R) P2)
    (hb : 2 * (l1 P1 + l1 P2) < 2 ^ R) (t : ℝ) : evalZ P1 t = evalZ P2 t := by
  have h0 : horner ((2 ^ R : ℕ) : ℤ) (addL P1 (scaleL (-1) P2)) = 0 := by
    rw [hornerZ_addL, hornerZ_scaleL]; push_cast; rw [h]; ring
  have hl : l1 (addL P1 (scaleL (-1) P2)) ≤ l1 P1 + l1 P2 := by
    refine (l1_addL _ _).trans (le_of_eq ?_)
    rw [l1_scaleL]; simp
  have := lift (2 ^ R) (Nat.one_lt_two_pow (by omega)) _ (lt_of_le_of_lt (Nat.mul_le_mul_left 2 hl) hb) h0 t
  rw [evalZ_addL, evalZ_scaleL] at this
  push_cast at this
  linarith

theorem sv_polyVal' (R x : Nat) (hR : 0 < R) : sv (polyVal R x) = horner ((2 : ℤ) ^ R) (recCoeffs x) :=
  sv_polyVal R x hR

/-! ## Retained tags -/

theorem rtagOk_spec (L : LTab) (n : Nat) (h : rtagOk L n = true) :
    (∀ i, i < n → notRetained L.D (L.rtag i) = false) ∧
      ∀ i j, i < n → j < n → L.rtag i = L.rtag j → i = j := by
  have inner : ∀ i m, Nat.rec (motive := fun _ => Bool) true
      (fun j ih2 => ih2 && not (Nat.beq (L.rtag j) (L.rtag i))) m = true → ∀ j, j < m → L.rtag j ≠ L.rtag i := by
    intro i m
    induction m with
    | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero j)
    | succ m ih =>
      intro hm j hj
      have hm' : (Nat.rec (motive := fun _ => Bool) true
          (fun j ih2 => ih2 && not (Nat.beq (L.rtag j) (L.rtag i))) m &&
          not (Nat.beq (L.rtag m) (L.rtag i))) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih hm'.1 j hj
      · intro he
        have := hm'.2
        rw [he, Nat.beq_refl] at this
        exact Bool.false_ne_true this
  have outer : ∀ m, rtagOk L m = true → (∀ i, i < m → notRetained L.D (L.rtag i) = false) ∧
      ∀ i j, j < i → i < m → L.rtag j ≠ L.rtag i := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i j _ hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ m ih =>
      intro hm
      have hm' : (rtagOk L m && not (notRetained L.D (L.rtag m)) &&
          Nat.rec (motive := fun _ => Bool) true (fun j ih2 => ih2 && not (Nat.beq (L.rtag j) (L.rtag m))) m)
          = true := hm
      simp only [Bool.and_eq_true] at hm'
      obtain ⟨⟨h1, h2⟩, h3⟩ := hm'
      obtain ⟨i1, i2⟩ := ih h1
      refine ⟨fun i hi => ?_, fun i j hji hi => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact i1 i hi
        · simpa using h2
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact i2 i j hji hi
        · exact inner i i h3 j hji
  obtain ⟨o1, o2⟩ := outer n h
  refine ⟨o1, fun i j hi hj he => ?_⟩
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact absurd he (o2 j i hij hj)
  · rfl
  · exact absurd he.symm (o2 i j hij hi)

/-! ## Δc -/

theorem dcOk_spec (G : GTab) (L : LTab) (S : STab) (n : Nat) (h : dcOk G L S n = true) :
    ∀ k, k < n → dcG G k = S.sc (oBlk L k) (oRow L k) * S.sc (oBlk L k) (oCol L k) * S.rd (oBlk L k) := by
  have key : ∀ m, dcOk G L S m = true → ∀ k, k < m →
      dcG G k = S.sc (oBlk L k) (oRow L k) * S.sc (oBlk L k) (oCol L k) * S.rd (oBlk L k) := by
    intro m
    induction m with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ m ih =>
      intro hm k hk
      have hm' : (dcOk G L S m && Nat.beq (fld (G.inf m) 256 64)
          (Nat.mul (Nat.mul (S.sc (Nat.land (L.oinfo m) 255) (Nat.land (Nat.shiftRight (L.oinfo m) 8) 255))
            (S.sc (Nat.land (L.oinfo m) 255) (Nat.land (Nat.shiftRight (L.oinfo m) 16) 255)))
            (S.rd (Nat.land (L.oinfo m) 255)))) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih hm'.1 k hk
      · exact Nat.eq_of_beq_eq_true hm'.2
  exact key n h

/-! ## Denominator cofactors -/

/-- `δ_b` coefficient lists. -/
def blkC (G : GTab) (b : Nat) : List ℤ := lookC (decPolyVecC G.blc G.bln 0) b

/-- `ρ_d` as an integer. -/
def rhoZ (S : STab) (d : Nat) : ℤ := sv (Nat.beq (Nat.land (S.rrho d) 1) 1, Nat.shiftRight (S.rrho d) 1)

theorem blk_val (T : Tab) (G : GTab) (hR : 0 < T.R) (hG : gLinkOk T G = true) (b : Nat) :
    sv (lookV b (decPolyVec T.R G.blc G.bln 0)) = horner ((2 : ℤ) ^ T.R) (blkC G b) ∧ CoefB G.LB G.wB (blkC G b) := by
  obtain ⟨-, -, -, p4, -⟩ := gLinkOk_parts T G hG
  obtain ⟨b1, -, b3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ p4
  refine ⟨?_, lookC_mem ⟨by simp, by simp⟩ b3⟩
  rw [lookV_sv _ b1]; exact lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) b1 _

theorem denOk_sound (T : Tab) (G : GTab) (S : STab) (hR : 0 < T.R) (hG : gLinkOk T G = true)
    (h : denOk T.R G S = true) : ∀ d, d < S.nden →
      1 ≤ S.rdsc d ∧ rhoZ S d ≠ 0 ∧ CoefB S.LD S.wD (recCoeffs (S.rden d)) ∧ ∀ t : ℝ,
        evalZ (recCoeffs (S.rden d)) t * evalZ (recCoeffs (S.rcof d)) t = (rhoZ S d : ℝ) * evalZ (blkC G (S.rblk d)) t := by
  have key : ∀ m, Nat.rec (motive := fun _ => Bool) true (fun d ih => ih &&
      recOk S.LD S.wD (S.rden d) && recOk S.LC S.wC (S.rcof d) && Nat.ble 1 (S.rdsc d) &&
      Nat.ble 1 (Nat.shiftRight (S.rrho d) 1) &&
      seq (smulS (polyVal T.R (S.rden d)) (polyVal T.R (S.rcof d)))
        (smulS (Nat.beq (Nat.land (S.rrho d) 1) 1, Nat.shiftRight (S.rrho d) 1)
          (lookV (S.rblk d) (decPolyVec T.R G.blc G.bln 0))) &&
      Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (recBound S.LD S.wD) (recBound S.LC S.wC))
        (Nat.mul (Nat.shiftRight (S.rrho d) 1) (recBound G.LB G.wB)))) (Nat.shiftLeft 1 T.R)) m = true →
      ∀ d, d < m → recOk S.LD S.wD (S.rden d) = true ∧ recOk S.LC S.wC (S.rcof d) = true ∧ 1 ≤ S.rdsc d ∧
        1 ≤ Nat.shiftRight (S.rrho d) 1 ∧
        seq (smulS (polyVal T.R (S.rden d)) (polyVal T.R (S.rcof d)))
          (smulS (Nat.beq (Nat.land (S.rrho d) 1) 1, Nat.shiftRight (S.rrho d) 1)
            (lookV (S.rblk d) (decPolyVec T.R G.blc G.bln 0))) = true ∧
        2 * (recBound S.LD S.wD * recBound S.LC S.wC + Nat.shiftRight (S.rrho d) 1 * recBound G.LB G.wB) < 2 ^ T.R := by
    intro m
    induction m with
    | zero => intro _ d hd; exact absurd hd (Nat.not_lt_zero d)
    | succ m ih =>
      intro hm d hd
      simp only [Bool.and_eq_true] at hm
      obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
      · exact ih h0 d hd
      · refine ⟨h1, h2, Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4, h5, ?_⟩
        have := Nat.blt_eq.mp h6
        rw [show Nat.shiftLeft 1 T.R = 2 ^ T.R from Nat.one_shiftLeft _] at this
        exact this
  intro d hd
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := key S.nden h d hd
  obtain ⟨bv, bc⟩ := blk_val T G hR hG (S.rblk d)
  have cD := recOk_coefB _ _ _ k1
  have cC := recOk_coefB _ _ _ k2
  have hm : ((Nat.shiftRight (S.rrho d) 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp k4)
  refine ⟨k3, ?_, cD, fun t => ?_⟩
  · unfold rhoZ sv
    split_ifs
    · exact neg_ne_zero.mpr hm
    · exact hm
  have hs := seq_sv _ _ k5
  rw [sv_smulS, sv_smulS, sv_polyVal T.R _ hR, sv_polyVal T.R _ hR, bv] at hs
  have hrad : horner ((2 : ℤ) ^ T.R) (convL (recCoeffs (S.rden d)) (recCoeffs (S.rcof d))) =
      horner ((2 : ℤ) ^ T.R) (scaleL (rhoZ S d) (blkC G (S.rblk d))) := by
    rw [hornerZ_convL, hornerZ_scaleL, hs]; rfl
  have hb : 2 * (l1 (convL (recCoeffs (S.rden d)) (recCoeffs (S.rcof d))) + l1 (scaleL (rhoZ S d) (blkC G (S.rblk d))))
      < 2 ^ T.R := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add ((l1_convL _ _).trans
      (Nat.mul_le_mul (l1_le_of_coefB cD) (l1_le_of_coefB cC))) ?_)) k6
    rw [l1_scaleL]
    refine Nat.mul_le_mul (le_of_eq ?_) (l1_le_of_coefB bc)
    unfold rhoZ sv
    split_ifs
    · rw [Int.natAbs_neg, Int.natAbs_natCast]
    · rw [Int.natAbs_natCast]
  have := lift_eq T.R hR _ _ hrad hb t
  rw [evalZ_convL, evalZ_scaleL] at this
  exact this

/-! ## RF records against κ -/

/-- The κ entry `(b, j, u)` (coefficients; `[]` if absent). -/
def kapE (L : LTab) (b j u : Nat) : List ℤ := lookC (kapC L b j) u

theorem rfEnt_sound (T : Tab) (G : GTab) (L : LTab) (S : STab) (LK wK mK b j u : Nat) (hR : 0 < T.R)
    (hG : gLinkOk T G = true) (hK : 1 ≤ polyVecOk LK wK mK (L.kc b j) (L.kn b j) 0 1)
    (hden : ∀ d, d < S.nden → CoefB S.LD S.wD (recCoeffs (S.rden d)))
    (h : rfEntOk T.R G L S LK wK b j u = true) :
    1 ≤ S.rsc (S.col b j u) ∧ 1 ≤ S.sc b j ∧ S.rdi (S.col b j u) < S.nden ∧ ∀ t : ℝ,
      evalZ (recCoeffs (S.rnum (S.col b j u))) t * ((S.rdsc (S.rdi (S.col b j u)) * S.sc b j : ℕ) : ℝ) *
          evalZ (blkC G b) t =
        evalZ (kapE L b j u) t * (S.rsc (S.col b j u) : ℝ) * evalZ (recCoeffs (S.rden (S.rdi (S.col b j u)))) t := by
  have h' : (recOk S.LN S.wN (S.rnum (S.col b j u)) && Nat.ble 1 (S.rsc (S.col b j u)) && Nat.ble 1 (S.sc b j) &&
      Nat.blt (S.rdi (S.col b j u)) S.nden &&
      seq (smulS (smulS (polyVal T.R (S.rnum (S.col b j u))) (false, Nat.mul (S.rdsc (S.rdi (S.col b j u))) (S.sc b j)))
          (lookV b (decPolyVec T.R G.blc G.bln 0)))
        (smulS (smulS (lookV u (decPolyVec T.R (L.kc b j) (L.kn b j) 0)) (false, S.rsc (S.col b j u)))
          (polyVal T.R (S.rden (S.rdi (S.col b j u))))) &&
      Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (Nat.mul (S.rdsc (S.rdi (S.col b j u))) (S.sc b j))
          (Nat.mul (recBound S.LN S.wN) (recBound G.LB G.wB)))
        (Nat.mul (S.rsc (S.col b j u)) (Nat.mul (recBound LK wK) (recBound S.LD S.wD))))) (Nat.shiftLeft 1 T.R))
      = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h'
  have hd : S.rdi (S.col b j u) < S.nden := Nat.blt_eq.mp h4
  refine ⟨Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3, hd, fun t => ?_⟩
  obtain ⟨bv, bc⟩ := blk_val T G hR hG b
  obtain ⟨k1, -, k3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ hK
  have kv : sv (lookV u (decPolyVec T.R (L.kc b j) (L.kn b j) 0)) = horner ((2 : ℤ) ^ T.R) (kapE L b j u) := by
    rw [lookV_sv _ k1]; exact lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) k1 _
  have kc : CoefB LK wK (kapE L b j u) := lookC_mem ⟨by simp, by simp⟩ k3
  have nc := recOk_coefB _ _ _ h1
  have dc := hden _ hd
  have hs := seq_sv _ _ h5
  simp only [sv_smulS, sv_polyVal T.R _ hR, bv, kv] at hs
  have hrad : horner ((2 : ℤ) ^ T.R) (scaleL ((S.rdsc (S.rdi (S.col b j u)) * S.sc b j : ℕ) : ℤ)
      (convL (recCoeffs (S.rnum (S.col b j u))) (blkC G b))) =
      horner ((2 : ℤ) ^ T.R) (scaleL (S.rsc (S.col b j u) : ℤ)
        (convL (kapE L b j u) (recCoeffs (S.rden (S.rdi (S.col b j u)))))) := by
    rw [hornerZ_scaleL, hornerZ_scaleL, hornerZ_convL, hornerZ_convL]
    have e1 : sv (false, Nat.mul (S.rdsc (S.rdi (S.col b j u))) (S.sc b j)) =
        ((S.rdsc (S.rdi (S.col b j u)) * S.sc b j : ℕ) : ℤ) := rfl
    have e2 : sv (false, S.rsc (S.col b j u)) = (S.rsc (S.col b j u) : ℤ) := rfl
    rw [e1, e2] at hs
    linear_combination hs
  have hb : 2 * (l1 (scaleL ((S.rdsc (S.rdi (S.col b j u)) * S.sc b j : ℕ) : ℤ)
      (convL (recCoeffs (S.rnum (S.col b j u))) (blkC G b))) +
      l1 (scaleL (S.rsc (S.col b j u) : ℤ) (convL (kapE L b j u) (recCoeffs (S.rden (S.rdi (S.col b j u))))))) <
      2 ^ T.R := by
    have b1 : l1 (scaleL ((S.rdsc (S.rdi (S.col b j u)) * S.sc b j : ℕ) : ℤ)
        (convL (recCoeffs (S.rnum (S.col b j u))) (blkC G b))) ≤
        (S.rdsc (S.rdi (S.col b j u)) * S.sc b j) * (recBound S.LN S.wN * recBound G.LB G.wB) := by
      rw [l1_scaleL, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ ((l1_convL _ _).trans (Nat.mul_le_mul (l1_le_of_coefB nc) (l1_le_of_coefB bc)))
    have b2 : l1 (scaleL (S.rsc (S.col b j u) : ℤ) (convL (kapE L b j u) (recCoeffs (S.rden (S.rdi (S.col b j u)))))) ≤
        S.rsc (S.col b j u) * (recBound LK wK * recBound S.LD S.wD) := by
      rw [l1_scaleL, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ ((l1_convL _ _).trans (Nat.mul_le_mul (l1_le_of_coefB kc) (l1_le_of_coefB dc)))
    have b3 := Nat.blt_eq.mp h6
    rw [show Nat.shiftLeft 1 T.R = 2 ^ T.R from Nat.one_shiftLeft _] at b3
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add b1 b2)) b3
  have := lift_eq T.R hR _ _ hrad hb t
  rw [evalZ_scaleL, evalZ_scaleL, evalZ_convL, evalZ_convL] at this
  push_cast at this ⊢
  linear_combination this

theorem rfOk_spec (R : Nat) (G : GTab) (L : LTab) (S : STab) (LK wK b : Nat) (h : rfOk R G L S LK wK b = true) :
    ∀ j u, j < S.ncol b → u < S.nraw b → rfEntOk R G L S LK wK b j u = true := by
  have inner : ∀ j m, Nat.rec (motive := fun _ => Bool) true (fun u ih2 => ih2 && rfEntOk R G L S LK wK b j u) m = true →
      ∀ u, u < m → rfEntOk R G L S LK wK b j u = true := by
    intro j m
    induction m with
    | zero => intro _ u hu; exact absurd hu (Nat.not_lt_zero u)
    | succ m ih =>
      intro hm u hu
      have hm' : (Nat.rec (motive := fun _ => Bool) true (fun u ih2 => ih2 && rfEntOk R G L S LK wK b j u) m &&
          rfEntOk R G L S LK wK b j m) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact ih hm'.1 u hu
      · exact hm'.2
  have outer : ∀ m, Nat.rec (motive := fun _ => Bool) true (fun j ih => ih &&
      Nat.rec (motive := fun _ => Bool) true (fun u ih2 => ih2 && rfEntOk R G L S LK wK b j u) (S.nraw b)) m = true →
      ∀ j u, j < m → u < S.nraw b → rfEntOk R G L S LK wK b j u = true := by
    intro m
    induction m with
    | zero => intro _ j u hj; exact absurd hj (Nat.not_lt_zero j)
    | succ m ih =>
      intro hm j u hj hu
      have hm' : (Nat.rec (motive := fun _ => Bool) true (fun j ih => ih &&
          Nat.rec (motive := fun _ => Bool) true (fun u ih2 => ih2 && rfEntOk R G L S LK wK b j u) (S.nraw b)) m &&
          Nat.rec (motive := fun _ => Bool) true (fun u ih2 => ih2 && rfEntOk R G L S LK wK b m u) (S.nraw b)) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih hm'.1 j u hj hu
      · exact inner j _ hm'.2 u hu
  exact outer (S.ncol b) h

/-! ## The factorization of Q -/

/-- `f^e`. -/
def powL (f : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | e + 1 => convL (powL f e) f

theorem horner_powL (B : ℤ) (f : List ℤ) : ∀ e, horner B (powL f e) = horner B f ^ e
  | 0 => by simp [powL]
  | e + 1 => by rw [powL, hornerZ_convL, horner_powL B f e, pow_succ]

theorem evalZ_powL (f : List ℤ) (t : ℝ) : ∀ e, evalZ (powL f e) t = evalZ f t ^ e
  | 0 => by simp [powL, evalZ]
  | e + 1 => by rw [powL, evalZ_convL, evalZ_powL f t e, pow_succ]

theorem l1_powL (f : List ℤ) : ∀ e, l1 (powL f e) ≤ l1 f ^ e
  | 0 => by simp [powL, l1]
  | e + 1 => by
    rw [powL, pow_succ]
    exact (l1_convL _ _).trans (Nat.mul_le_mul_right _ (l1_powL f e))

/-- `Π_{r < m} f_r^{e_r}`. -/
def prodF (S : STab) : ℕ → List ℤ
  | 0 => [1]
  | r + 1 => convL (prodF S r) (powL (recCoeffs (S.fac r)) (S.fexp r))

theorem facOk_sound (T : Tab) (G : GTab) (S : STab) (hR : 0 < T.R) (hG : gLinkOk T G = true)
    (h : facOk T.R G S = true) (t : ℝ) :
    evalZ (qC G) t = (if S.fsgn then -1 else 1) * evalZ (prodF S S.nfac) t := by
  have h' : (Nat.rec (motive := fun _ => Bool) true
      (fun r ih => ih && Nat.ble 1 (Nat.land (Nat.shiftRight (S.fac r) 20) 255)) S.nfac &&
      seq (lookV 0 (decPolyVec T.R G.qc G.qn 0))
        (xor S.fsgn (Nat.rec (motive := fun _ => Bool × Nat) (false, 1)
          (fun r acc => smulS acc (spow (polyVal T.R (S.fac r)) (S.fexp r))) S.nfac).1,
         (Nat.rec (motive := fun _ => Bool × Nat) (false, 1)
          (fun r acc => smulS acc (spow (polyVal T.R (S.fac r)) (S.fexp r))) S.nfac).2) &&
      Nat.blt (Nat.mul 2 (Nat.add (recBound G.LQ G.wQ)
        (Nat.rec (motive := fun _ => Nat) 1 (fun r acc => Nat.mul acc (Nat.pow (ownBound (S.fac r)) (S.fexp r)))
          S.nfac))) (Nat.shiftLeft 1 T.R)) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  -- the headers
  have hw : ∀ m, Nat.rec (motive := fun _ => Bool) true
      (fun r ih => ih && Nat.ble 1 (Nat.land (Nat.shiftRight (S.fac r) 20) 255)) m = true →
      ∀ r, r < m → 1 ≤ Nat.land (Nat.shiftRight (S.fac r) 20) 255 := by
    intro m
    induction m with
    | zero => intro _ r hr; exact absurd hr (Nat.not_lt_zero r)
    | succ m ih =>
      intro hm r hr
      have hm' : (Nat.rec (motive := fun _ => Bool) true
          (fun r ih => ih && Nat.ble 1 (Nat.land (Nat.shiftRight (S.fac r) 20) 255)) m &&
          Nat.ble 1 (Nat.land (Nat.shiftRight (S.fac m) 20) 255)) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact ih hm'.1 r hr
      · exact Nat.le_of_ble_eq_true hm'.2
  have hw' := hw S.nfac h1
  -- the radix value and the bound of the product
  have hval : ∀ m, m ≤ S.nfac → sv (Nat.rec (motive := fun _ => Bool × Nat) (false, 1)
      (fun r acc => smulS acc (spow (polyVal T.R (S.fac r)) (S.fexp r))) m) = horner ((2 : ℤ) ^ T.R) (prodF S m) ∧
      l1 (prodF S m) ≤ Nat.rec (motive := fun _ => Nat) 1
        (fun r acc => Nat.mul acc (Nat.pow (ownBound (S.fac r)) (S.fexp r))) m := by
    intro m
    induction m with
    | zero => intro _; simp [prodF, sv, l1]
    | succ m ih =>
      intro hm
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hc : CoefB (Nat.land (Nat.shiftRight (S.fac m) 12) 255) (Nat.land (Nat.shiftRight (S.fac m) 20) 255)
          (recCoeffs (S.fac m)) := recCoeffs_bound _ _ _ (hw' m (by omega)) le_rfl le_rfl
      refine ⟨?_, ?_⟩
      · show sv (smulS _ (spow (polyVal T.R (S.fac m)) (S.fexp m))) = horner _ (convL (prodF S m) _)
        rw [sv_smulS, sv_spow, sv_polyVal T.R _ hR, i1, hornerZ_convL, horner_powL]
      · show l1 (convL (prodF S m) _) ≤ Nat.mul _ (Nat.pow (ownBound (S.fac m)) (S.fexp m))
        rw [nat_mul, Nat.pow_eq]
        exact (l1_convL _ _).trans (Nat.mul_le_mul i2 ((l1_powL _ _).trans (Nat.pow_le_pow_left
          (l1_le_of_coefB hc) _)))
  obtain ⟨v1, v2⟩ := hval S.nfac le_rfl
  obtain ⟨-, -, -, qB, -⟩ := gLinkOk_sound T G hR hG
  obtain ⟨-, -, -, -, -, -, -, -, -⟩ := gLinkOk_parts T G hG
  obtain ⟨q1, -, q3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ (gLinkOk_parts T G hG).2.1
  have hQv : sv (lookV 0 (decPolyVec T.R G.qc G.qn 0)) = horner ((2 : ℤ) ^ T.R) (qC G) := by
    rw [lookV_sv _ q1]; exact lk_eq_horner T.R hR _ _ (decPolyVec_sv T.R hR _ _ _) q1 0
  have hs := seq_sv _ _ h2
  rw [hQv] at hs
  have hsgn : sv (xor S.fsgn (Nat.rec (motive := fun _ => Bool × Nat) (false, 1)
      (fun r acc => smulS acc (spow (polyVal T.R (S.fac r)) (S.fexp r))) S.nfac).1,
      (Nat.rec (motive := fun _ => Bool × Nat) (false, 1)
      (fun r acc => smulS acc (spow (polyVal T.R (S.fac r)) (S.fexp r))) S.nfac).2) =
      (if S.fsgn then -1 else 1) * sv (Nat.rec (motive := fun _ => Bool × Nat) (false, 1)
      (fun r acc => smulS acc (spow (polyVal T.R (S.fac r)) (S.fexp r))) S.nfac) := by
    rw [show (if S.fsgn then (-1 : ℤ) else 1) = sv (S.fsgn, 1) by cases S.fsgn <;> rfl, ← sv_smulS]
    unfold smulS; simp
  rw [hsgn, v1] at hs
  have hrad : horner ((2 : ℤ) ^ T.R) (qC G) =
      horner ((2 : ℤ) ^ T.R) (scaleL (if S.fsgn then -1 else 1) (prodF S S.nfac)) := by
    rw [hornerZ_scaleL]; exact hs
  have hb : 2 * (l1 (qC G) + l1 (scaleL (if S.fsgn then -1 else 1) (prodF S S.nfac))) < 2 ^ T.R := by
    rw [l1_scaleL]
    have e : (if S.fsgn then (-1 : ℤ) else 1).natAbs = 1 := by split_ifs <;> rfl
    rw [e, one_mul]
    refine lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add (l1_le_of_coefB qB) v2)) ?_
    have := Nat.blt_eq.mp h3
    rw [show Nat.shiftLeft 1 T.R = 2 ^ T.R from Nat.one_shiftLeft _] at this
    exact this
  have := lift_eq T.R hR _ _ hrad hb t
  rw [evalZ_scaleL] at this
  push_cast at this
  exact this

#print axioms rtagOk_spec
#print axioms denOk_sound
#print axioms rfEnt_sound
#print axioms facOk_sound

end ThomsonCompact.Fixed
