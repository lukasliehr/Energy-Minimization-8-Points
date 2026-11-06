import ThomsonNegative.Compact.Packed.Comp
import ThomsonNegative.Compact.Target.Kernel
import ThomsonNegative.Geometry.Confluent

/-!
# Soundness of the packed confluent table and the Newton → monomial conversion

Against the old definitions `confluentTable` (column recursion) and `sourceNewtonHorner`, for abstract nodes
`xs t l` (labels `l < 4`), expanded node sequence `zE t k = xs t (labels k)`, jets `J t k x`.
-/

namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed ThomsonNegative.Geometry

variable {N S B W : ℕ}

/-- `T` encloses `f` once its flag is set -/
def EOK (c : Ctx) (T : TM) (f : ℝ → ℝ) : Prop := T.ok = true → Encl c T f

theorem EOK.congr {c : Ctx} {T : TM} {f g : ℝ → ℝ} (h : EOK c T f)
    (hfg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t = g t) : EOK c T g := fun hok => (h hok).congr hfg

theorem EOK.of_encl {c : Ctx} {T : TM} {f : ℝ → ℝ} (h : Encl c T f) : EOK c T f := fun _ => h

theorem add_eok {c : Ctx} {A B' : TM} {f g : ℝ → ℝ} (hA : EOK c A f) (hB : EOK c B' g)
    (hc : c = mkCtx N S B W) : EOK c (add c A B') (fun t => f t + g t) := by
  subst hc
  intro hok
  exact add_sound (hA (add_ok hok).1) (hB (add_ok hok).2) hok

theorem neg_eok {c : Ctx} {A : TM} {f : ℝ → ℝ} (hA : EOK c A f) (hc : c = mkCtx N S B W) :
    EOK c (neg c A) (fun t => -f t) := by
  subst hc
  intro hok
  exact neg_sound (hA hok)

theorem mul_eok (hg : Good N S B W) {A B' : TM} {f g : ℝ → ℝ} (hA : EOK (mkCtx N S B W) A f)
    (hB : EOK (mkCtx N S B W) B' g) : EOK (mkCtx N S B W) (mul (mkCtx N S B W) A B') (fun t => f t * g t) := by
  intro hok
  exact mul_sound hg (hA (mul_ok hok).1) (hB (mul_ok hok).2) hok

theorem refresh_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : EOK (mkCtx N S B W) A f) :
    EOK (mkCtx N S B W) (refresh (mkCtx N S B W) A) f := fun hok => refresh_sound hg (hA hok)

theorem divR_ok {c : Ctx} {F G Rc : TM} (h : (divR c F G Rc).ok = true) :
    F.ok = true ∧ G.ok = true ∧ Rc.ok = true := by
  have e : (divR c F G Rc).ok = ((refresh c (polyOnly (mul c (refresh c F) Rc))).ok &&
      (add c (refresh c F) (neg c (mul c G (refresh c (polyOnly (mul c (refresh c F) Rc)))))).ok && Rc.ok) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  have h1 : (mul c (refresh c F) Rc).ok = true := h.1.1
  have h2 := add_ok h.1.2
  have h3 : (mul c G (refresh c (polyOnly (mul c (refresh c F) Rc)))).ok = true := h2.2
  exact ⟨(mul_ok h1).1, (mul_ok h3).1, h.2⟩

/-! ## The table -/

/-- hypotheses on the data of the table -/
structure TabCtx (c : Ctx) (Vs Hs Gs : List (List TM)) (labels : List ℕ) (zE : ℝ → ℕ → ℝ)
    (xs : ℝ → ℕ → ℝ) (J : ℝ → ℕ → ℝ → ℝ) (μ : ℕ → ℕ) : Prop where
  lab_lt : ∀ k < labels.length, labels.getD k 0 < 4
  hz : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ k < labels.length, zE t k = xs t (labels.getD k 0)
  inj : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ h l, h < 4 → l < 4 → xs t h = xs t l → h = l
  group : ∀ i j, i < j → j < labels.length → labels.getD i 0 = labels.getD j 0 → j - i < μ (labels.getD i 0)
  mu_pos : ∀ k < labels.length, 0 < μ (labels.getD k 0)
  hV : ∀ l k, l < 4 → k < μ l →
    EOK c ((Vs.getD l []).getD k zeroTM) (fun t => J t k (xs t l) / (k.factorial : ℝ))
  hH : ∀ h l, h < 4 → l < 4 → h ≠ l → EOK c ((Hs.getD h []).getD l zeroTM) (fun t => xs t h - xs t l)
  hG : ∀ h l, h < 4 → l < 4 → h ≠ l → ((Gs.getD h []).getD l zeroTM).ok = true →
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, xs t h - xs t l ≠ 0) ∧
      Encl c ((Gs.getD h []).getD l zeroTM) (fun t => (xs t h - xs t l)⁻¹)

theorem getD_eq_get {α : Type*} (L : List α) (i : ℕ) (d : α) (h : i < L.length) : L.getD i d = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem colStep_sound (hg : Good N S B W) {Vs Hs Gs : List (List TM)} {labels : List ℕ}
    {zE xs : ℝ → ℕ → ℝ} {J : ℝ → ℕ → ℝ → ℝ} {μ : ℕ → ℕ}
    (H : TabCtx (mkCtx N S B W) Vs Hs Gs labels zE xs J μ) (k : ℕ) :
    ∀ (col : List TM) (st : ℕ), st + k + col.length ≤ labels.length →
      (∀ i < col.length, EOK (mkCtx N S B W) (col.getD i zeroTM) (fun t => confluentTable (zE t) (J t) k (st + i))) →
      ∀ i, i + 1 < col.length →
        EOK (mkCtx N S B W) ((colStep (mkCtx N S B W) Vs Hs Gs k (labels.drop st) (labels.drop (st + k + 1)) col).getD i zeroTM)
          (fun t => confluentTable (zE t) (J t) (k + 1) (st + i))
  | [], _, _, _, i, hi => absurd hi (by simp)
  | [_], _, _, _, i, hi => absurd hi (by simp)
  | x :: y :: rest, st, hlen, hcol, i, hi => by
    have hlen' : st + k + (rest.length + 2) ≤ labels.length := by simpa using hlen
    have hst : st < labels.length := by omega
    have hsk : st + k + 1 < labels.length := by omega
    rw [List.drop_eq_getElem_cons hst, List.drop_eq_getElem_cons hsk]
    have e : colStep (mkCtx N S B W) Vs Hs Gs k (labels[st] :: labels.drop (st + 1))
        (labels[st + k + 1] :: labels.drop (st + k + 1 + 1)) (x :: y :: rest) =
        cond (Nat.beq labels[st + k + 1] labels[st]) ((Vs.getD labels[st] []).getD (k + 1) zeroTM)
          (divR (mkCtx N S B W) (add (mkCtx N S B W) y (neg (mkCtx N S B W) x))
            ((Hs.getD labels[st + k + 1] []).getD labels[st] zeroTM)
            ((Gs.getD labels[st + k + 1] []).getD labels[st] zeroTM)) ::
          colStep (mkCtx N S B W) Vs Hs Gs k (labels.drop (st + 1)) (labels.drop (st + k + 1 + 1)) (y :: rest) := rfl
    rw [e]
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      have hl := H.lab_lt st hst
      have hh := H.lab_lt (st + k + 1) hsk
      rw [getD_eq_get labels st 0 hst] at hl
      rw [getD_eq_get labels (st + k + 1) 0 hsk] at hh
      by_cases heq : labels[st + k + 1] = labels[st]
      · -- confluent: the jet `J (k+1)/(k+1)!` at the common node
        have hb : Nat.beq labels[st + k + 1] labels[st] = true := by rw [heq]; exact Nat.beq_refl _
        rw [hb, cond_true]
        have hgrp := H.group st (st + k + 1) (by omega) hsk
          (by rw [getD_eq_get labels st 0 hst, getD_eq_get labels (st + k + 1) 0 hsk]; exact heq.symm)
        rw [getD_eq_get labels st 0 hst] at hgrp
        have hk1 : k + 1 < μ labels[st] := by omega
        refine (H.hV labels[st] (k + 1) hl hk1).congr (fun t ht => ?_)
        have hz1 := H.hz t ht st hst
        have hz2 := H.hz t ht (st + k + 1) hsk
        rw [getD_eq_get labels st 0 hst] at hz1
        rw [getD_eq_get labels (st + k + 1) 0 hsk, heq] at hz2
        show J t (k + 1) (xs t labels[st]) / ((k + 1).factorial : ℝ) = confluentTable (zE t) (J t) (k + 1) st
        rw [confluentTable, if_pos (by rw [hz1, hz2]), hz1]
      · have hb : Nat.beq labels[st + k + 1] labels[st] = false := by
          cases h : Nat.beq labels[st + k + 1] labels[st]
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) heq
        rw [hb, cond_false]
        intro hok
        obtain ⟨hFok, _, hRok⟩ := divR_ok hok
        obtain ⟨hne, hRc⟩ := H.hG _ _ hh hl heq hRok
        have hx := hcol 0 (by simp)
        have hy := hcol 1 (by simp)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hx hy
        have hF := add_eok hy (neg_eok hx rfl) rfl hFok
        have hHh := H.hH _ _ hh hl heq (divR_ok hok).2.1
        refine (divR_sound hg hF hHh hRc hne hok).congr (fun t ht => ?_)
        have hz1 := H.hz t ht st hst
        have hz2 := H.hz t ht (st + k + 1) hsk
        rw [getD_eq_get labels st 0 hst] at hz1
        rw [getD_eq_get labels (st + k + 1) 0 hsk] at hz2
        have hneq : zE t (st + k + 1) ≠ zE t st := by
          rw [hz1, hz2]; intro h; exact heq (H.inj t ht _ _ hh hl h)
        show (confluentTable (zE t) (J t) k (st + 1) + -confluentTable (zE t) (J t) k st) /
            (xs t labels[st + k + 1] - xs t labels[st]) = confluentTable (zE t) (J t) (k + 1) st
        rw [confluentTable, if_neg hneq, hz1, hz2]
        ring
    | succ i =>
      rw [List.getD_cons_succ]
      have IH := colStep_sound hg H k (y :: rest) (st + 1) (by simp at hlen ⊢; omega)
        (fun j hj => by
          have := hcol (j + 1) (by simp at hj ⊢; omega)
          simp only [List.getD_cons_succ] at this
          exact this.congr (fun t _ => by rw [show st + (j + 1) = st + 1 + j by omega]))
        i (by simp at hi ⊢; omega)
      rw [show st + 1 + k + 1 = st + k + 1 + 1 by omega] at IH
      exact IH.congr (fun t _ => by rw [show st + 1 + i = st + (i + 1) by omega])

theorem colStep_length (c : Ctx) (Vs Hs Gs : List (List TM)) (k : ℕ) :
    ∀ (col : List TM) (ls hs : List ℕ), col.length ≤ ls.length + 1 → col.length ≤ hs.length + 1 →
      (colStep c Vs Hs Gs k ls hs col).length = col.length - 1
  | [], ls, hs, _, _ => by cases ls <;> cases hs <;> rfl
  | [_], ls, hs, _, _ => by
    cases ls <;> cases hs <;> rfl
  | x :: y :: rest, l :: ls, h :: hs, h1, h2 => by
    have := colStep_length c Vs Hs Gs k (y :: rest) ls hs (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)
    show (_ :: colStep c Vs Hs Gs k ls hs (y :: rest)).length = _
    rw [List.length_cons, this]
    simp
  | x :: y :: rest, [], _, h1, _ => by simp at h1
  | x :: y :: rest, _ :: _, [], _, h2 => by simp at h2

theorem newtonCoeffs_sound (hg : Good N S B W) {Vs Hs Gs : List (List TM)} {labels : List ℕ}
    {zE xs : ℝ → ℕ → ℝ} {J : ℝ → ℕ → ℝ → ℝ} {μ : ℕ → ℕ}
    (H : TabCtx (mkCtx N S B W) Vs Hs Gs labels zE xs J μ) :
    ∀ (r k : ℕ) (col : List TM), col.length + k = labels.length → r + k ≤ labels.length →
      (∀ i < col.length, EOK (mkCtx N S B W) (col.getD i zeroTM) (fun t => confluentTable (zE t) (J t) k i)) →
      ∀ i < r, EOK (mkCtx N S B W) ((newtonCoeffs (mkCtx N S B W) Vs Hs Gs labels r k col).getD i zeroTM)
        (fun t => confluentTable (zE t) (J t) (k + i) 0)
  | 0, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | r + 1, k, col, hlen, hr, hcol, i, hi => by
    have e : newtonCoeffs (mkCtx N S B W) Vs Hs Gs labels (r + 1) k col = col.headD zeroTM ::
        newtonCoeffs (mkCtx N S B W) Vs Hs Gs labels r (k + 1)
          (colStep (mkCtx N S B W) Vs Hs Gs k labels (labels.drop (k + 1)) col) := rfl
    rw [e]
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      have hpos : 0 < col.length := by omega
      have h0 := hcol 0 hpos
      have hh : col.headD zeroTM = col.getD 0 zeroTM := by
        cases col with
        | nil => simp at hpos
        | cons a l => rfl
      rw [hh]
      exact h0
    | succ i =>
      rw [List.getD_cons_succ]
      have hcl := colStep_length (mkCtx N S B W) Vs Hs Gs k col labels (labels.drop (k + 1))
        (by omega) (by simp; omega)
      have hcol' : ∀ j < (colStep (mkCtx N S B W) Vs Hs Gs k labels (labels.drop (k + 1)) col).length,
          EOK (mkCtx N S B W) ((colStep (mkCtx N S B W) Vs Hs Gs k labels (labels.drop (k + 1)) col).getD j zeroTM)
            (fun t => confluentTable (zE t) (J t) (k + 1) j) := by
        intro j hj
        rw [hcl] at hj
        have := colStep_sound hg H k col 0 (by omega)
          (fun i hi => (hcol i hi).congr (fun t _ => by rw [Nat.zero_add])) j (by omega)
        simp only [Nat.zero_add, List.drop_zero] at this
        exact this
      have IH := newtonCoeffs_sound hg H r (k + 1) _ (by rw [hcl]; omega) (by omega) hcol' i (by omega)
      exact IH.congr (fun t _ => by rw [show k + 1 + i = k + (i + 1) by omega])

/-! ## Newton → monomial -/

theorem coeff_horner_zero (c x : ℝ) (P : Polynomial ℝ) :
    (Polynomial.C c + (Polynomial.X - Polynomial.C x) * P).coeff 0 = c - x * P.coeff 0 := by
  simp [sub_mul, Polynomial.coeff_C]
  ring

theorem coeff_horner_succ (c x : ℝ) (P : Polynomial ℝ) (i : ℕ) :
    (Polynomial.C c + (Polynomial.X - Polynomial.C x) * P).coeff (i + 1) = P.coeff i - x * P.coeff (i + 1) := by
  simp [sub_mul, Polynomial.coeff_X_mul]

theorem timesNode_eok (hg : Good N S B W) {x p : TM} {xf pf : ℝ → ℝ} {neg1 : Bool}
    (hx : EOK (mkCtx N S B W) x xf) (hp : EOK (mkCtx N S B W) p pf)
    (hneg : neg1 = true → ∀ t ∈ Set.Icc (-1 : ℝ) 1, xf t = -1) :
    EOK (mkCtx N S B W) (timesNode (mkCtx N S B W) x neg1 p) (fun t => xf t * pf t) := by
  cases neg1
  · exact mul_eok hg hx hp
  · exact (neg_eok hp rfl).congr (fun t ht => by rw [hneg rfl t ht]; ring)

theorem hrest_sound (hg : Good N S B W) {x : TM} {xf : ℝ → ℝ} {neg1 : Bool}
    (hx : EOK (mkCtx N S B W) x xf) (hneg : neg1 = true → ∀ t ∈ Set.Icc (-1 : ℝ) 1, xf t = -1)
    (Pf : ℝ → Polynomial ℝ) :
    ∀ (L : List TM) (o : ℕ), (∀ i < L.length, EOK (mkCtx N S B W) (L.getD i zeroTM) (fun t => (Pf t).coeff (o + i))) →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, (Pf t).coeff (o + L.length) = 0) →
      (hrest (mkCtx N S B W) x neg1 L).length = L.length ∧
      ∀ i < L.length, EOK (mkCtx N S B W) ((hrest (mkCtx N S B W) x neg1 L).getD i zeroTM)
        (fun t => (Pf t).coeff (o + i) - xf t * (Pf t).coeff (o + i + 1))
  | [], _, _, _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | [p], o, hL, hz => by
    refine ⟨rfl, fun i hi => ?_⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    refine (hL 0 (by simp)).congr (fun t ht => ?_)
    have := hz t ht
    simp only [List.length_singleton] at this
    simp [this]
  | p :: q :: rest, o, hL, hz => by
    have e : hrest (mkCtx N S B W) x neg1 (p :: q :: rest) =
        refresh (mkCtx N S B W) (add (mkCtx N S B W) p (neg (mkCtx N S B W) (timesNode (mkCtx N S B W) x neg1 q))) ::
          hrest (mkCtx N S B W) x neg1 (q :: rest) := rfl
    have IH := hrest_sound hg hx hneg Pf (q :: rest) (o + 1)
      (fun i hi => by
        have := hL (i + 1) (by simp at hi ⊢; omega)
        simp only [List.getD_cons_succ] at this
        exact this.congr (fun t _ => by rw [show o + (i + 1) = o + 1 + i by omega]))
      (fun t ht => by
        have := hz t ht
        simp only [List.length_cons] at this ⊢
        rw [show o + 1 + (rest.length + 1) = o + (rest.length + 1 + 1) by omega]; exact this)
    rw [e]
    refine ⟨by simp [IH.1], fun i hi => ?_⟩
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      have hp := hL 0 (by simp)
      have hq := hL 1 (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hp hq
      refine (refresh_eok hg (add_eok hp (neg_eok (timesNode_eok hg hx hq hneg) rfl) rfl)).congr (fun t _ => ?_)
      show (Pf t).coeff (o + 0) + -(xf t * (Pf t).coeff (o + 1)) = (Pf t).coeff (o + 0) - xf t * (Pf t).coeff (o + 0 + 1)
      ring_nf
    | succ i =>
      rw [List.getD_cons_succ]
      exact (IH.2 i (by simp at hi ⊢; omega)).congr (fun t _ => by
        rw [show o + 1 + i = o + (i + 1) by omega])

theorem hstep_sound (hg : Good N S B W) {x ci : TM} {xf cf : ℝ → ℝ} {neg1 : Bool}
    (hx : EOK (mkCtx N S B W) x xf) (hneg : neg1 = true → ∀ t ∈ Set.Icc (-1 : ℝ) 1, xf t = -1)
    (hc : EOK (mkCtx N S B W) ci cf) (Pf : ℝ → Polynomial ℝ) (L : List TM)
    (hL : ∀ i < L.length, EOK (mkCtx N S B W) (L.getD i zeroTM) (fun t => (Pf t).coeff i))
    (hz : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ i, L.length ≤ i → (Pf t).coeff i = 0) :
    (hstep (mkCtx N S B W) x neg1 ci L).length = L.length + 1 ∧
    (∀ i < L.length + 1, EOK (mkCtx N S B W) ((hstep (mkCtx N S B W) x neg1 ci L).getD i zeroTM)
      (fun t => (Polynomial.C (cf t) + (Polynomial.X - Polynomial.C (xf t)) * Pf t).coeff i)) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ i, L.length + 1 ≤ i →
      (Polynomial.C (cf t) + (Polynomial.X - Polynomial.C (xf t)) * Pf t).coeff i = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · cases L with
    | nil => rfl
    | cons p ps =>
      have := (hrest_sound hg hx hneg Pf (p :: ps) 0 (fun i hi => (hL i hi).congr (fun t _ => by rw [Nat.zero_add]))
        (fun t ht => by rw [Nat.zero_add]; exact hz t ht _ le_rfl)).1
      show (_ :: hrest (mkCtx N S B W) x neg1 (p :: ps)).length = _
      rw [List.length_cons, this]
  · intro i hi
    cases L with
    | nil =>
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      refine hc.congr (fun t ht => ?_)
      show cf t = _
      rw [coeff_horner_zero, hz t ht 0 (by simp), mul_zero, sub_zero]
    | cons p ps =>
      have HR := hrest_sound hg hx hneg Pf (p :: ps) 0 (fun i hi => (hL i hi).congr (fun t _ => by rw [Nat.zero_add]))
        (fun t ht => by rw [Nat.zero_add]; exact hz t ht _ le_rfl)
      have e : hstep (mkCtx N S B W) x neg1 ci (p :: ps) =
          refresh (mkCtx N S B W) (add (mkCtx N S B W) ci (neg (mkCtx N S B W) (timesNode (mkCtx N S B W) x neg1 p))) ::
            hrest (mkCtx N S B W) x neg1 (p :: ps) := rfl
      rw [e]
      cases i with
      | zero =>
        rw [List.getD_cons_zero]
        have hp := hL 0 (by simp)
        simp only [List.getD_cons_zero] at hp
        refine (refresh_eok hg (add_eok hc (neg_eok (timesNode_eok hg hx hp hneg) rfl) rfl)).congr (fun t _ => ?_)
        rw [coeff_horner_zero]; ring
      | succ i =>
        rw [List.getD_cons_succ]
        refine (HR.2 i (by simp at hi ⊢; omega)).congr (fun t _ => ?_)
        rw [coeff_horner_succ, Nat.zero_add]
  · intro t ht i hi
    cases i with
    | zero => simp at hi
    | succ i =>
      rw [coeff_horner_succ, hz t ht i (by omega), hz t ht (i + 1) (by omega), mul_zero, sub_zero]

/-- `SNH t r st` -/
noncomputable def snh (zE : ℝ → ℕ → ℝ) (J : ℝ → ℕ → ℝ → ℝ) (t : ℝ) (r st : ℕ) : Polynomial ℝ :=
  sourceNewtonHorner (zE t) (fun i => confluentTable (zE t) (J t) i 0) r st

theorem hornerN_sound (hg : Good N S B W) {Vs Hs Gs : List (List TM)} {labels : List ℕ}
    {zE xs : ℝ → ℕ → ℝ} {J : ℝ → ℕ → ℝ → ℝ} {μ : ℕ → ℕ}
    (H : TabCtx (mkCtx N S B W) Vs Hs Gs labels zE xs J μ) {Xs : List TM}
    (hX : ∀ l < 4, EOK (mkCtx N S B W) (Xs.getD l zeroTM) (fun t => xs t l))
    (h4 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, xs t 4 = -1) (cs : List TM) (hcl : cs.length = labels.length)
    (hcs : ∀ i < labels.length, EOK (mkCtx N S B W) (cs.getD i zeroTM) (fun t => confluentTable (zE t) (J t) i 0)) :
    ∀ (r : ℕ), r ≤ labels.length →
      (hornerN (mkCtx N S B W) Xs (labels.drop (labels.length - r)) (cs.drop (labels.length - r))).length = r ∧
      (∀ i < r, EOK (mkCtx N S B W)
        ((hornerN (mkCtx N S B W) Xs (labels.drop (labels.length - r)) (cs.drop (labels.length - r))).getD i zeroTM)
        (fun t => (snh zE J t r (labels.length - r)).coeff i)) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ i, r ≤ i → (snh zE J t r (labels.length - r)).coeff i = 0)
  | 0, _ => by
    rw [Nat.sub_zero, List.drop_length, List.drop_of_length_le (by omega)]
    refine ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun t _ i _ => ?_⟩
    simp [snh, sourceNewtonHorner]
  | r + 1, hr => by
    have IH := hornerN_sound hg H hX h4 cs hcl hcs r (by omega)
    set st := labels.length - (r + 1) with hst
    have hst1 : labels.length - r = st + 1 := by omega
    rw [hst1] at IH
    have hlt : st < labels.length := by omega
    have hlt' : st < cs.length := by omega
    rw [List.drop_eq_getElem_cons hlt, List.drop_eq_getElem_cons hlt']
    have e : hornerN (mkCtx N S B W) Xs (labels[st] :: labels.drop (st + 1)) (cs[st] :: cs.drop (st + 1)) =
        hstep (mkCtx N S B W) (Xs.getD labels[st] zeroTM) (Nat.beq labels[st] 4) cs[st]
          (hornerN (mkCtx N S B W) Xs (labels.drop (st + 1)) (cs.drop (st + 1))) := rfl
    rw [e]
    have hl := H.lab_lt st hlt
    rw [getD_eq_get labels st 0 hlt] at hl
    have hneg : Nat.beq labels[st] 4 = true → ∀ t ∈ Set.Icc (-1 : ℝ) 1, xs t labels[st] = -1 := by
      intro hb t ht
      rw [Nat.eq_of_beq_eq_true hb]; exact h4 t ht
    have hci : EOK (mkCtx N S B W) cs[st] (fun t => confluentTable (zE t) (J t) st 0) := by
      have := hcs st hlt
      rwa [getD_eq_get cs st zeroTM hlt'] at this
    have HS := hstep_sound hg (hX labels[st] hl) hneg hci (fun t => snh zE J t r (st + 1)) _
      (fun i hi => IH.2.1 i (by rw [IH.1] at hi; exact hi))
      (fun t ht i hi => IH.2.2 t ht i (by rw [IH.1] at hi; exact hi))
    have hsnh : ∀ t ∈ Set.Icc (-1 : ℝ) 1, snh zE J t (r + 1) st = Polynomial.C (confluentTable (zE t) (J t) st 0) +
        (Polynomial.X - Polynomial.C (xs t labels[st])) * snh zE J t r (st + 1) := by
      intro t ht
      have hz := H.hz t ht st hlt
      rw [getD_eq_get labels st 0 hlt] at hz
      simp only [snh, sourceNewtonHorner, hz]
    rw [IH.1] at HS
    refine ⟨HS.1, fun i hi => (HS.2.1 i hi).congr (fun t ht => by rw [hsnh t ht]), fun t ht i hi => ?_⟩
    rw [hsnh t ht]
    exact HS.2.2 t ht i hi

end ThomsonNegative.Compact.Target
