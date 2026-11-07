import ThomsonCompact.Packed.Export
import ThomsonCompact.Packed.Core2

/-!
# Soundness of `refresh`, `hornerQ` and division (`invN`, `divN`, `divW`)
-/

namespace ThomsonCompact.Packed
open Nat

variable {N S B W : ℕ}

/-! ## Generic enclosure facts -/

theorem Encl.congr {c : Ctx} {T : TM} {f g : ℝ → ℝ} (h : Encl c T f)
    (hfg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t = g t) : Encl c T g := by
  obtain ⟨cs, al, hR, hf⟩ := h
  exact ⟨cs, al, hR, fun t ht => by rw [← hfg t ht]; exact hf t ht⟩

/-- the enclosure depends only on the fields `v a s e` (not on `ok`) -/
theorem Encl.of_fields {c : Ctx} {T T' : TM} {f : ℝ → ℝ} (h : Encl c T f) (hv : T'.v = T.v)
    (ha : T'.a = T.a) (hs : T'.s = T.s) (he : T'.e = T.e) : Encl c T' f := by
  obtain ⟨cs, al, hR, hf⟩ := h
  refine ⟨cs, al, ⟨hR.lcs, hR.lal, by rw [hv]; exact hR.hv, by rw [ha]; exact hR.ha, hR.dom,
    by rw [hs]; exact hR.hs, by rw [hs]; exact hR.sB⟩, fun t ht => by rw [he]; exact hf t ht⟩

/-- `T` is a valid packed TM (its polynomial is well defined) -/
def RepOK (c : Ctx) (T : TM) : Prop := ∃ cs al, Rep c T cs al

theorem Encl.repOK {c : Ctx} {T : TM} {f : ℝ → ℝ} (h : Encl c T f) : RepOK c T :=
  let ⟨cs, al, hR, _⟩ := h; ⟨cs, al, hR⟩

theorem RepOK.encl {c : Ctx} {T : TM} (h : RepOK c T) : ∃ f, Encl c T f :=
  let ⟨_, _, hR⟩ := h; ⟨_, Encl.self hR⟩

theorem widen_sound {c : Ctx} {T : TM} {f g : ℝ → ℝ} (δ : ℕ) (h : Encl c T f)
    (hfg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |g t - f t| ≤ (δ : ℝ) / 2 ^ c.S) : Encl c (widen T δ) g := by
  obtain ⟨cs, al, hR, hf⟩ := h
  refine ⟨cs, al, ⟨hR.lcs, hR.lal, hR.hv, hR.ha, hR.dom, hR.hs, hR.sB⟩, fun t ht => ?_⟩
  have h1 := hf t ht
  have h2 := hfg t ht
  show |g t - evalZ cs t / 2 ^ c.S| ≤ ((T.e + δ : ℕ) : ℝ) / 2 ^ c.S
  push_cast
  calc |g t - evalZ cs t / 2 ^ c.S| ≤ |g t - f t| + |f t - evalZ cs t / 2 ^ c.S| := abs_sub_le _ _ _
    _ ≤ (δ : ℝ) / 2 ^ c.S + (T.e : ℝ) / 2 ^ c.S := add_le_add h2 h1
    _ = ((T.e : ℝ) + δ) / 2 ^ c.S := by ring

theorem polyOnly_rep {c : Ctx} {T : TM} {cs : List ℤ} {al : List ℕ} (h : Rep c T cs al) :
    Rep c (polyOnly T) cs al := ⟨h.lcs, h.lal, h.hv, h.ha, h.dom, h.hs, h.sB⟩

theorem horner_replicate_zero {R : Type*} [CommSemiring R] (t : R) (n : ℕ) :
    horner t (List.replicate n 0) = 0 := by
  simpa using horner_append_zeros t [] n

theorem zero_sound : Encl (mkCtx N S B W) zeroTM (fun _ => 0) := by
  refine ⟨List.replicate (N + 1) 0, List.replicate (N + 1) 0, ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show ((0 : ℕ) : ℤ) = _
    simp [horner_replicate_zero]
  · show 0 = Nat.ofDigits _ _
    rw [Nat.ofDigits_replicate_zero]
  · intro k; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> simp
  · show 0 = _; simp
  · show 0 < 2 ^ B; positivity
  · intro t _
    simp [evalZ, List.map_replicate, horner_replicate_zero, zeroTM]

/-- a rational `±n/d` -/
noncomputable def qval (a : Bool × ℕ × ℕ) : ℝ := if a.1 then -((a.2.1 : ℝ) / a.2.2) else (a.2.1 : ℝ) / a.2.2

theorem ratMag_err (a : Bool × ℕ × ℕ) :
    |qval a - (if a.1 then -((ratMag (mkCtx N S B W) a.2.1 a.2.2 : ℕ) : ℝ) else
      ((ratMag (mkCtx N S B W) a.2.1 a.2.2 : ℕ) : ℝ)) / 2 ^ S| ≤ ((1 : ℕ) : ℝ) / 2 ^ S := by
  obtain ⟨ng, n, d⟩ := a
  have hD : (0 : ℝ) < 2 ^ S := by positivity
  have key : |(n : ℝ) / d - ((ratMag (mkCtx N S B W) n d : ℕ) : ℝ) / 2 ^ S| ≤ 1 / 2 ^ S := by
    show |(n : ℝ) / d - (((n * 2 ^ S) / d : ℕ) : ℝ) / 2 ^ S| ≤ 1 / 2 ^ S
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have h1 : (n * 2 ^ S) / d * d ≤ n * 2 ^ S := Nat.div_mul_le_self _ _
      have h2 : n * 2 ^ S < ((n * 2 ^ S) / d + 1) * d := by
        rw [Nat.add_mul, one_mul]; exact Nat.lt_div_mul_add hd
      generalize (n * 2 ^ S) / d = q at h1 h2 ⊢
      have h1' : (q : ℝ) * d ≤ n * 2 ^ S := by exact_mod_cast h1
      have h2' : (n : ℝ) * 2 ^ S ≤ (q + 1) * d := by exact_mod_cast h2.le
      have l1 : (q : ℝ) / 2 ^ S ≤ n / d := by rw [div_le_div_iff₀ hD hd']; linarith
      have l2 : (n : ℝ) / d ≤ (q + 1) / 2 ^ S := by rw [div_le_div_iff₀ hd' hD]; linarith
      have l3 : ((q : ℝ) + 1) / 2 ^ S = q / 2 ^ S + 1 / 2 ^ S := add_div _ _ _
      have l4 : (0 : ℝ) < 1 / 2 ^ S := by positivity
      rw [abs_le]; constructor <;> linarith
  push_cast
  cases ng
  · simpa [qval] using key
  · simp only [qval, if_true]
    rw [show -((n : ℝ) / d) - -((ratMag (mkCtx N S B W) n d : ℕ) : ℝ) / 2 ^ S =
      -((n : ℝ) / d - ((ratMag (mkCtx N S B W) n d : ℕ) : ℝ) / 2 ^ S) by ring, abs_neg]
    exact key

theorem constTM_sound (hg : Good N S B W) (ng : Bool) (mag dq : ℕ) (κ : ℝ)
    (hκ : |κ - (if ng then -(mag : ℝ) else mag) / 2 ^ S| ≤ (dq : ℝ) / 2 ^ S)
    (hok : (constTM (mkCtx N S B W) ng mag dq).ok = true) :
    Encl (mkCtx N S B W) (constTM (mkCtx N S B W) ng mag dq) (fun _ => κ) :=
  (addC_sound zero_sound ng mag dq κ hκ hok hg).congr (fun t _ => by simp)

/-! ## `ok` propagation -/

theorem add_ok {c : Ctx} {A B : TM} (h : (add c A B).ok = true) : A.ok = true ∧ B.ok = true := by
  have e : (add c A B).ok = (A.ok && B.ok && Nat.blt (A.s + B.s) c.twoB) := rfl
  rw [e] at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem mul_ok {c : Ctx} {A B : TM} (h : (mul c A B).ok = true) : A.ok = true ∧ B.ok = true := by
  have e : (mul c A B).ok = (A.ok && B.ok && Nat.blt (mul c A B).s c.twoB) := rfl
  rw [e] at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem addC_ok {c : Ctx} {ng : Bool} {mag dq : ℕ} {A : TM} (h : (addC c ng mag dq A).ok = true) :
    A.ok = true := by
  have e : (addC c ng mag dq A).ok = (A.ok && Nat.blt (A.s + mag) c.twoB) := rfl
  rw [e] at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem smul_ok {c : Ctx} {ng : Bool} {q dq : ℕ} {A : TM} (h : (smul c ng q dq A).ok = true) :
    A.ok = true := by
  have e : (smul c ng q dq A).ok = (A.ok && Nat.blt q c.twoB && Nat.blt (smul c ng q dq A).s c.twoB) := rfl
  rw [e] at h; simp only [Bool.and_eq_true] at h; exact h.1.1

theorem recip_ok {c : Ctx} {Q R : TM} (h : (recip c Q R).ok = true) :
    R.ok = true ∧ (mul c R Q).ok = true := by
  have e : (recip c Q R).ok = (R.ok && (addC c false c.twoS 0 (neg c (mul c R Q))).ok &&
      Nat.blt (2 * rangeX c (addC c false c.twoS 0 (neg c (mul c R Q)))) c.twoS) := rfl
  rw [e] at h; simp only [Bool.and_eq_true] at h
  have h3 : (neg c (mul c R Q)).ok = true := addC_ok h.1.2
  exact ⟨h.1.1, h3⟩

/-! ## refresh -/

theorem refresh_sound (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f) :
    Encl (mkCtx N S B W) (refresh (mkCtx N S B W) A) f := by
  obtain ⟨cs, al, hR, hf⟩ := hA
  have hlen : cs.length = N + 1 := hR.lcs
  have hrefresh : refresh (mkCtx N S B W) A =
      ⟨A.v, Nat.ofDigits (2 ^ W) (cs.map Int.natAbs), (cs.map Int.natAbs).sum, A.e, A.ok⟩ := by
    show (⟨A.v, pabs (mkCtx N S B W) A, ssum (mkCtx N S B W) (pabs (mkCtx N S B W) A), A.e, A.ok⟩ : TM) = _
    rw [hR.ssum_pabs hg, hR.pabs_eq hg]
  have hdom : Dom cs (cs.map Int.natAbs) := by
    intro k
    rw [getD_map_of_zero Int.natAbs 0 0 rfl, Int.abs_eq_natAbs]
  rw [hrefresh]
  refine ⟨cs, cs.map Int.natAbs, ⟨hR.lcs, by simp [hlen], hR.hv, rfl, hdom, rfl, ?_⟩, hf⟩
  have h1 := hR.sum_natAbs_le
  have h2 := hR.sB
  show (cs.map Int.natAbs).sum < 2 ^ B
  simp only [mk_B] at h2
  omega

/-! ## Fixed polynomials at a TM -/

/-- `Σⱼ qval(aⱼ) yʲ` in Horner form -/
noncomputable def evalQ : List (Bool × ℕ × ℕ) → ℝ → ℝ
  | [], _ => 0
  | a :: rest, y => qval a + y * evalQ rest y

theorem hornerQ_sound (hg : Good N S B W) {G : TM} {g : ℝ → ℝ} (hG : Encl (mkCtx N S B W) G g) :
    ∀ (L : List (Bool × ℕ × ℕ)), (hornerQ (mkCtx N S B W) G L).ok = true →
      Encl (mkCtx N S B W) (hornerQ (mkCtx N S B W) G L) (fun t => evalQ L (g t))
  | [], _ => zero_sound.congr (fun t _ => by simp [evalQ])
  | [a], hok => by
    have h := constTM_sound hg a.1 (ratMag (mkCtx N S B W) a.2.1 a.2.2) 1 (qval a) (ratMag_err a) hok
    exact h.congr (fun t _ => by simp [evalQ])
  | a :: b :: rest, hok => by
    have hok1 : (mul (mkCtx N S B W) (hornerQ (mkCtx N S B W) G (b :: rest)) G).ok = true := addC_ok hok
    have hok2 := (mul_ok hok1).1
    have ih := hornerQ_sound hg hG (b :: rest) hok2
    have hm := mul_sound hg ih hG hok1
    have h := addC_sound hm a.1 (ratMag (mkCtx N S B W) a.2.1 a.2.2) 1 (qval a) (ratMag_err a) hok hg
    refine h.congr (fun t _ => ?_)
    show evalQ (b :: rest) (g t) * g t + qval a = evalQ (a :: b :: rest) (g t)
    simp only [evalQ]
    ring

/-! ## Division -/

theorem constTM_rep (hg : Good N S B W) (ng : Bool) (mag dq : ℕ)
    (hok : (constTM (mkCtx N S B W) ng mag dq).ok = true) :
    RepOK (mkCtx N S B W) (constTM (mkCtx N S B W) ng mag dq) :=
  (constTM_sound hg ng mag dq ((if ng then -(mag : ℝ) else mag) / 2 ^ S)
    (by rw [sub_self, abs_zero]; positivity) hok).repOK

theorem inv0_rep (hg : Good N S B W) {D : TM} (hok : (inv0 (mkCtx N S B W) D).ok = true) :
    RepOK (mkCtx N S B W) (inv0 (mkCtx N S B W) D) :=
  constTM_rep hg (coef0 (mkCtx N S B W) D).1
    (Nat.div (Nat.mul (mkCtx N S B W).twoS (mkCtx N S B W).twoS) (coef0 (mkCtx N S B W) D).2) 0 hok

theorem newtonStep_ok {c : Ctx} {D R : TM} (h : (newtonStep c D R).ok = true) : R.ok = true :=
  (add_ok (show (add c R _).ok = true from h)).1

theorem newtonStep_rep (hg : Good N S B W) {D R : TM} {d : ℝ → ℝ} (hD : Encl (mkCtx N S B W) D d)
    (hR : RepOK (mkCtx N S B W) R) (hok : (newtonStep (mkCtx N S B W) D R).ok = true) :
    RepOK (mkCtx N S B W) (newtonStep (mkCtx N S B W) D R) := by
  obtain ⟨r, hr⟩ := hR.encl
  have hok' : (add (mkCtx N S B W) R (mul (mkCtx N S B W) R (refresh (mkCtx N S B W)
      (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
        (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D)))))).ok = true := hok
  have h1 := add_ok hok'
  have h2 := mul_ok h1.2
  have hE : (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
      (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D))).ok = true := h2.2
  have h3 : (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D)).ok = true := addC_ok hE
  have h4 : (mul (mkCtx N S B W) R D).ok = true := h3
  have hm := mul_sound hg hr hD h4
  have hn := neg_sound hm
  have ha := addC_sound hn false (2 ^ S) 0 1 (by simp) hE hg
  have hf := refresh_sound hg ha
  have hm2 := mul_sound hg hr hf h1.2
  obtain ⟨cs, al, hrep⟩ := (add_sound hr hm2 hok').repOK
  exact ⟨cs, al, polyOnly_rep hrep⟩

theorem newton_ok {c : Ctx} {D : TM} {tol : ℕ} : ∀ (k : ℕ) (R : TM), (newton c D tol k R).ok = true → R.ok = true
  | 0, _, h => h
  | k + 1, R, h => by
    have e : newton c D tol (k + 1) R = cond (Nat.ble (Nat.mul 8 (rangeX c (addC c false c.twoS 0
        (neg c (mul c R D))))) (Nat.add (Nat.mul 9 (addC c false c.twoS 0 (neg c (mul c R D))).e)
        (Nat.mul 8 tol))) R (newton c D tol k (newtonStep c D R)) := rfl
    rw [e] at h
    cases hb : Nat.ble (Nat.mul 8 (rangeX c (addC c false c.twoS 0 (neg c (mul c R D)))))
        (Nat.add (Nat.mul 9 (addC c false c.twoS 0 (neg c (mul c R D))).e) (Nat.mul 8 tol)) <;>
      rw [hb] at h
    · exact newtonStep_ok (newton_ok k _ h)
    · exact h

theorem newton_rep (hg : Good N S B W) {D : TM} {d : ℝ → ℝ} (hD : Encl (mkCtx N S B W) D d) (tol : ℕ) :
    ∀ (k : ℕ) (R : TM), RepOK (mkCtx N S B W) R → (newton (mkCtx N S B W) D tol k R).ok = true →
      RepOK (mkCtx N S B W) (newton (mkCtx N S B W) D tol k R)
  | 0, _, hR, _ => hR
  | k + 1, R, hR, h => by
    have e : newton (mkCtx N S B W) D tol (k + 1) R = cond (Nat.ble (Nat.mul 8 (rangeX (mkCtx N S B W)
        (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0 (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D)))))
        (Nat.add (Nat.mul 9 (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
          (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D))).e) (Nat.mul 8 tol))) R
        (newton (mkCtx N S B W) D tol k (newtonStep (mkCtx N S B W) D R)) := rfl
    rw [e] at h ⊢
    cases hb : Nat.ble (Nat.mul 8 (rangeX (mkCtx N S B W)
        (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0 (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D)))))
        (Nat.add (Nat.mul 9 (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
          (neg (mkCtx N S B W) (mul (mkCtx N S B W) R D))).e) (Nat.mul 8 tol)) <;> rw [hb] at h
    · have h' : (newton (mkCtx N S B W) D tol k (newtonStep (mkCtx N S B W) D R)).ok = true := h
      have hs := newton_ok k _ h'
      exact newton_rep hg hD tol k _ (newtonStep_rep hg hD hR hs) h'
    · exact hR

/-- `1/d` by in-kernel Newton steps (any number; verified by `recip`) -/
theorem invN_sound (hg : Good N S B W) {D : TM} {d : ℝ → ℝ} (hD : Encl (mkCtx N S B W) D d) (k tol : ℕ)
    (hok : (invN (mkCtx N S B W) k tol D).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, d t ≠ 0) ∧
      Encl (mkCtx N S B W) (invN (mkCtx N S B W) k tol D) (fun t => (d t)⁻¹) := by
  have h1 := (recip_ok hok).1
  have h3 := newton_ok k _ h1
  obtain ⟨cs, al, hR⟩ := newton_rep hg hD tol k _ (inv0_rep hg h3) h1
  exact recip_sound hg hD hR hok

/-- `f/d` by in-kernel Newton steps -/
theorem divN_sound (hg : Good N S B W) {F D : TM} {f d : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f)
    (hD : Encl (mkCtx N S B W) D d) (k tol : ℕ) (hok : (divN (mkCtx N S B W) k tol F D).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, d t ≠ 0) ∧
      Encl (mkCtx N S B W) (divN (mkCtx N S B W) k tol F D) (fun t => f t / d t) := by
  have h1 := mul_ok hok
  obtain ⟨hne, hinv⟩ := invN_sound hg hD k tol h1.2
  exact ⟨hne, (mul_sound hg hF hinv hok).congr (fun t _ => by rw [div_eq_mul_inv])⟩

/-- `f/d` with a supplied witness `R` (any represented TM, e.g. from `ofPQ` data) -/
theorem divW_sound (hg : Good N S B W) {F D R : TM} {f d : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f)
    (hD : Encl (mkCtx N S B W) D d) (hR : RepOK (mkCtx N S B W) R)
    (hok : (divW (mkCtx N S B W) F D R).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, d t ≠ 0) ∧
      Encl (mkCtx N S B W) (divW (mkCtx N S B W) F D R) (fun t => f t / d t) := by
  obtain ⟨cs, al, hR'⟩ := hR
  have h1 := mul_ok hok
  obtain ⟨hne, hinv⟩ := recip_sound hg hD hR' h1.2
  exact ⟨hne, (mul_sound hg hF hinv hok).congr (fun t _ => by rw [div_eq_mul_inv])⟩

/-- **residual division**: `f/g` from any enclosure `Rc` of `1/g` (no truncation of `1/g` enters) -/
theorem divR_sound (hg : Good N S B W) {F G Rc : TM} {f g : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f)
    (hG : Encl (mkCtx N S B W) G g) (hR : Encl (mkCtx N S B W) Rc (fun t => (g t)⁻¹))
    (hg0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, g t ≠ 0) (hok : (divR (mkCtx N S B W) F G Rc).ok = true) :
    Encl (mkCtx N S B W) (divR (mkCtx N S B W) F G Rc) (fun t => f t / g t) := by
  have hokE : (divR (mkCtx N S B W) F G Rc).ok =
      ((refresh (mkCtx N S B W) (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc))).ok &&
        (add (mkCtx N S B W) (refresh (mkCtx N S B W) F) (neg (mkCtx N S B W) (mul (mkCtx N S B W) G
          (refresh (mkCtx N S B W) (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc)))))).ok &&
        Rc.ok) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hQok, hEok⟩, _⟩ := hok
  have hF'E := refresh_sound hg hF
  have hMok : (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc).ok = true := hQok
  obtain ⟨cs, al, hRep, _⟩ := mul_sound hg hF'E hR hMok
  have hQE := refresh_sound hg (Encl.self (polyOnly_rep hRep))
  have h1 := add_ok hEok
  have hGQok : (mul (mkCtx N S B W) G (refresh (mkCtx N S B W)
      (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc)))).ok = true := h1.2
  have hEE := add_sound hF'E (neg_sound (mul_sound hg hG hQE hGQok)) hEok
  have hrE := rangeX_sound hg hEE
  have hrR := rangeX_sound hg hR
  obtain ⟨cs', al', hRep', hq⟩ := hQE
  refine ⟨cs', al', ⟨hRep'.lcs, hRep'.lal, hRep'.hv, hRep'.ha, hRep'.dom, hRep'.hs, hRep'.sB⟩, fun t ht => ?_⟩
  have hD : (0 : ℝ) < 2 ^ S := by positivity
  have hq0 := hq t ht
  simp only [mk_S] at hq0 ⊢
  have hQe : (refresh (mkCtx N S B W) (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc))).e = 0 := rfl
  rw [hQe, Nat.cast_zero, zero_div] at hq0
  have hqq : evalZ cs t / 2 ^ S = evalZ cs' t / 2 ^ S := by
    have := abs_nonpos_iff.mp hq0; linarith
  have e1 := hrE t ht
  have e2 := hrR t ht
  rw [← hqq]
  have key : f t / g t - evalZ cs t / 2 ^ S = (f t + -(g t * (evalZ cs t / 2 ^ S))) * (g t)⁻¹ := by
    field_simp [hg0 t ht]
    ring
  have hc := le_cdiv S (rangeX (mkCtx N S B W) (add (mkCtx N S B W) (refresh (mkCtx N S B W) F)
    (neg (mkCtx N S B W) (mul (mkCtx N S B W) G (refresh (mkCtx N S B W)
      (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc)))))) * rangeX (mkCtx N S B W) Rc)
  rw [key, abs_mul]
  calc |f t + -(g t * (evalZ cs t / 2 ^ S))| * |(g t)⁻¹|
      ≤ ((rangeX (mkCtx N S B W) (add (mkCtx N S B W) (refresh (mkCtx N S B W) F)
          (neg (mkCtx N S B W) (mul (mkCtx N S B W) G (refresh (mkCtx N S B W)
            (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc)))))) : ℕ) : ℝ) / 2 ^ S *
        ((rangeX (mkCtx N S B W) Rc : ℕ) : ℝ) / 2 ^ S := by
        rw [mul_div_assoc]
        exact mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
    _ = (((rangeX (mkCtx N S B W) (add (mkCtx N S B W) (refresh (mkCtx N S B W) F)
          (neg (mkCtx N S B W) (mul (mkCtx N S B W) G (refresh (mkCtx N S B W)
            (polyOnly (mul (mkCtx N S B W) (refresh (mkCtx N S B W) F) Rc)))))) *
          rangeX (mkCtx N S B W) Rc : ℕ) : ℝ) / 2 ^ S) / 2 ^ S := by push_cast; ring
    _ ≤ _ := div_le_div_of_nonneg_right hc hD.le

/-- a rational function of a TM: `p(g)/q(g)` for fixed rational coefficient lists -/
theorem rfTM_sound (hg : Good N S B W) {G : TM} {g : ℝ → ℝ} (hG : Encl (mkCtx N S B W) G g) (k tol : ℕ)
    (num den : List (Bool × ℕ × ℕ)) (hok : (rfTM (mkCtx N S B W) k tol G num den).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, evalQ den (g t) ≠ 0) ∧
      Encl (mkCtx N S B W) (rfTM (mkCtx N S B W) k tol G num den)
        (fun t => evalQ num (g t) / evalQ den (g t)) := by
  have h1 := mul_ok (show (mul (mkCtx N S B W) (hornerQ (mkCtx N S B W) G num)
    (invN (mkCtx N S B W) k tol (hornerQ (mkCtx N S B W) G den))).ok = true from hok)
  have h2 := recip_ok (show (recip (mkCtx N S B W) (hornerQ (mkCtx N S B W) G den)
    (newton (mkCtx N S B W) (hornerQ (mkCtx N S B W) G den) tol k
      (inv0 (mkCtx N S B W) (hornerQ (mkCtx N S B W) G den)))).ok = true from h1.2)
  have hden_ok := (mul_ok h2.2).2
  have hN := hornerQ_sound hg hG num h1.1
  have hD := hornerQ_sound hg hG den hden_ok
  exact divN_sound hg hN hD k tol hok

/-- integer coefficient lists with a common denominator `M` -/
def qOfInt (M : ℕ) (n : ℤ) : Bool × ℕ × ℕ := (decide (n < 0), n.natAbs, M)

theorem qval_qOfInt (M : ℕ) (n : ℤ) : qval (qOfInt M n) = (n : ℝ) / M := by
  have hc : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [qval, qOfInt, decide_eq_true_eq, hc]
  split_ifs with hn
  · rw [abs_of_neg (by exact_mod_cast hn)]; ring
  · rw [abs_of_nonneg (by exact_mod_cast (not_lt.mp hn))]

theorem evalQ_qOfInt (M : ℕ) (y : ℝ) : ∀ L : List ℤ, evalQ (L.map (qOfInt M)) y = evalZ L y / M
  | [] => by simp [evalQ, evalZ]
  | n :: L => by
    have ih := evalQ_qOfInt M y L
    have e1 : evalQ ((n :: L).map (qOfInt M)) y = qval (qOfInt M n) + y * evalQ (L.map (qOfInt M)) y := rfl
    have e2 : evalZ (n :: L) y = (n : ℝ) + y * evalZ L y := rfl
    rw [e1, e2, ih, qval_qOfInt]
    ring

#print axioms refresh_sound
#print axioms hornerQ_sound
#print axioms invN_sound
#print axioms divN_sound
#print axioms divW_sound
#print axioms rfTM_sound
#print axioms divR_sound
#print axioms evalQ_qOfInt

end ThomsonCompact.Packed
