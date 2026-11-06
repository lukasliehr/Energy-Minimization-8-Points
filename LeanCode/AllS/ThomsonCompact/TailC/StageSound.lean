import ThomsonCompact.TailC.StageLoops

/-!
# TailC: soundness of the packed product-collapse stage (workstream TC1)

`stage_sound`: if `(stage P ts).1 = true` and every table entry `gamD P i j` (`i, j < n`) is `< N`, the output list
is `[(γ, C_γ) | γ < N]` with the exact coefficients

  `coefC (gamD P) ts γ = Σ_terms c · Σ_{e ∈ p} Σ_{f ∈ q} [gamD e.i f.i = γ] e·f`     (in `ℤ√2`),

and every entry index of every term is `< n`. Proof: rows are `Σ_j G_ij 2^(W j)` (`rowsGo_spec`, `rv_packQ`); the
checked a-priori bound `2·bgSum < 2^(W-1)` makes the row digits exact (`decode`); the scatter is exact
(`scatAll_spec`); the fibres of `gamD` give `C_γ`, bounded by `n²·2·bgSum < 2^(W2-1)`, so the output digits are exact.
-/

namespace ThomsonCompact.TailC
open Finset

/-- Table entry `gam i j` (digit `j` of table row `i`). -/
def gamD (P : SP) (i j : ℕ) : ℕ := dig P.gw (P.gam i) j

/-- The collapsed coefficient `C_γ`. -/
def coefC (gm : ℕ → ℕ → ℕ) (ts : List Term) (γ : ℕ) : ℤ√2 :=
  (ts.map fun t => (t.2.2 : ℤ√2) * (t.1.map fun e => (t.2.1.map fun f =>
    if gm e.1 f.1 = γ then ev e * ev f else 0).sum).sum).sum

/-- The row-slot coefficient `G_ij`. -/
def coefG (ts : List Term) (i j : ℕ) : ℤ√2 :=
  (ts.map fun t => (t.2.2 : ℤ√2) * (t.1.map fun e => (t.2.1.map fun f =>
    if e.1 = i ∧ f.1 = j then ev e * ev f else 0).sum).sum).sum

/-! ## Small facts -/

theorem rv_z4 : rv z4 = 0 := rv_zero

theorem rep_length {α : Type} (x : α) : ∀ n, (rep x n).length = n
  | 0 => rfl
  | n + 1 => by show (x :: rep x n).length = n + 1; simp [rep_length x n]

theorem rep_getD {α : Type} (x : α) : ∀ (n i : ℕ), (rep x n).getD i x = x
  | 0, i => by show ([] : List α).getD i x = x; simp
  | n + 1, 0 => rfl
  | n + 1, i + 1 => by show (x :: rep x n).getD (i + 1) x = x; rw [List.getD_cons_succ, rep_getD x n i]

theorem ellL_eq : ∀ l : List Ent, ellL l = (l.map fun e => e.2.1.2 + e.2.2.2).sum
  | [] => rfl
  | e :: l => by
    show Nat.add (Nat.add e.2.1.2 e.2.2.2) (ellL l) = _
    rw [ellL_eq l]; simp [nadd]

theorem bgSum_eq : ∀ ts : List Term, bgSum ts = (ts.map fun t => t.2.2 * (ellL t.1 * ellL t.2.1)).sum
  | [] => rfl
  | t :: ts => by
    show Nat.add (Nat.mul t.2.2 (Nat.mul (ellL t.1) (ellL t.2.1))) (bgSum ts) = _
    rw [bgSum_eq ts]; simp [nadd, nmul]

/-! ## Rows -/

/-- One term's row contribution in digit form. -/
theorem term_row (W n : ℕ) (t : Term) (hq : ∀ f ∈ t.2.1, f.1 < n) (i : ℕ) :
    (t.1.map fun e => if e.1 = i then ev e * rv (packQ W t.2.2 t.2.1) else 0).sum =
      ∑ j ∈ range n, (t.2.2 : ℤ√2) * (t.1.map fun e => (t.2.1.map fun f =>
        if e.1 = i ∧ f.1 = j then ev e * ev f else 0).sum).sum * 2 ^ (W * j) := by
  obtain ⟨p, q, c⟩ := t
  simp only at hq ⊢
  -- both sides equal `Σ_e Σ_f [e.i = i] c e f 2^(W f.i)`
  have hL : (p.map fun e => if e.1 = i then ev e * rv (packQ W c q) else 0).sum =
      (p.map fun e => (q.map fun f => if e.1 = i then (c : ℤ√2) * (ev e * ev f) * 2 ^ (W * f.1) else 0).sum).sum := by
    refine lsum_congr _ _ _ (fun e _ => ?_)
    rw [rv_packQ]
    split_ifs
    · rw [lsum_mul_left]; refine lsum_congr _ _ _ (fun f _ => by ring)
    · simp
  have hR : ∑ j ∈ range n, (c : ℤ√2) * (p.map fun e => (q.map fun f =>
        if e.1 = i ∧ f.1 = j then ev e * ev f else 0).sum).sum * 2 ^ (W * j) =
      (p.map fun e => (q.map fun f => ∑ j ∈ range n,
        if e.1 = i ∧ f.1 = j then (c : ℤ√2) * (ev e * ev f) * 2 ^ (W * j) else 0).sum).sum := by
    symm
    simp only [lsum_fsum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
    refine lsum_congr _ _ _ (fun e _ => ?_)
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_right]
    refine lsum_congr _ _ _ (fun f _ => ?_)
    split_ifs <;> simp
  rw [hL, hR]
  refine lsum_congr _ _ _ (fun e _ => lsum_congr _ _ _ (fun f hf => ?_))
  by_cases he : e.1 = i
  · simp only [he, true_and, if_true]
    rw [Finset.sum_ite_eq]; simp [hq f hf]
  · simp only [he, false_and, if_false, Finset.sum_const_zero]

theorem rows_eq (W n : ℕ) (ts : List Term) (hq : ∀ t ∈ ts, ∀ f ∈ t.2.1, f.1 < n) (i : ℕ) :
    (ts.map fun t => (t.1.map fun e => if e.1 = i then ev e * rv (packQ W t.2.2 t.2.1) else 0).sum).sum =
      ∑ j ∈ range n, coefG ts i j * 2 ^ (W * j) := by
  rw [lsum_congr ts _ _ (fun t ht => term_row W n t (hq t ht) i), lsum_fsum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coefG, ← List.sum_map_mul_right]

/-! ## Bounds -/

theorem abs_re_mul_le (e f : Ent) :
    |(ev e * ev f).re| ≤ 2 * (((e.2.1.2 + e.2.2.2 : ℕ) : ℤ) * ((f.2.1.2 + f.2.2.2 : ℕ) : ℤ)) := by
  have h1 := abs_smv e.2.1; have h2 := abs_smv e.2.2; have h3 := abs_smv f.2.1; have h4 := abs_smv f.2.2
  rw [Zsqrtd.re_mul]
  simp only [ev]
  calc |smv e.2.1 * smv f.2.1 + 2 * smv e.2.2 * smv f.2.2|
      ≤ |smv e.2.1| * |smv f.2.1| + 2 * (|smv e.2.2| * |smv f.2.2|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, mul_assoc, abs_mul, abs_two, abs_mul]
    _ ≤ _ := by rw [h1, h2, h3, h4]; push_cast; nlinarith [Nat.zero_le e.2.1.2, Nat.zero_le e.2.2.2,
          Nat.zero_le f.2.1.2, Nat.zero_le f.2.2.2]

theorem abs_im_mul_le (e f : Ent) :
    |(ev e * ev f).im| ≤ 2 * (((e.2.1.2 + e.2.2.2 : ℕ) : ℤ) * ((f.2.1.2 + f.2.2.2 : ℕ) : ℤ)) := by
  have h1 := abs_smv e.2.1; have h2 := abs_smv e.2.2; have h3 := abs_smv f.2.1; have h4 := abs_smv f.2.2
  rw [Zsqrtd.im_mul]
  simp only [ev]
  calc |smv e.2.1 * smv f.2.2 + smv e.2.2 * smv f.2.1|
      ≤ |smv e.2.1| * |smv f.2.2| + |smv e.2.2| * |smv f.2.1| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
    _ ≤ _ := by rw [h1, h2, h3, h4]; push_cast; nlinarith [Nat.zero_le e.2.1.2, Nat.zero_le e.2.2.2,
          Nat.zero_le f.2.1.2, Nat.zero_le f.2.2.2]

theorem lsum_mul2 {α : Type*} (l : List α) (c d : ℤ) (f : α → ℤ) :
    (l.map fun b => c * (d * f b)).sum = c * (d * (l.map f).sum) := by
  rw [List.sum_map_mul_left, List.sum_map_mul_left]

theorem natCast_lsum {α : Type*} (l : List α) (f : α → ℕ) : (((l.map f).sum : ℕ) : ℤ) = (l.map fun a => (f a : ℤ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem abs_dsum_le {α β : Type*} (l : List α) (m : List β) (x : α → β → ℤ) (u : α → ℕ) (v : β → ℕ)
    (h : ∀ a b, |x a b| ≤ 2 * ((u a : ℤ) * v b)) :
    |(l.map fun a => (m.map fun b => x a b).sum).sum| ≤ 2 * (((l.map u).sum * (m.map v).sum : ℕ) : ℤ) := by
  refine (abs_lsum_le _ _).trans ?_
  refine (lsum_le _ _ (fun a => 2 * ((u a : ℤ) * (((m.map v).sum : ℕ) : ℤ))) (fun a _ => ?_)).trans ?_
  · refine (abs_lsum_le _ _).trans ?_
    refine (lsum_le _ _ (fun b => 2 * ((u a : ℤ) * v b)) (fun b _ => h a b)).trans (le_of_eq ?_)
    rw [lsum_mul2, natCast_lsum]
  · apply le_of_eq
    rw [Nat.cast_mul, natCast_lsum l u, ← List.sum_map_mul_right, ← List.sum_map_mul_left]

theorem abs_term_le (t : Term) (i j : ℕ) (part : ℤ√2 → ℤ) (hpart : ∀ e f, |part (ev e * ev f)| ≤
      2 * (((e.2.1.2 + e.2.2.2 : ℕ) : ℤ) * ((f.2.1.2 + f.2.2.2 : ℕ) : ℤ)))
    (hlin : ∀ (c : ℕ) (l : List Ent) (m : List Ent) (P : Ent → Ent → Prop) [∀ a b, Decidable (P a b)],
      part ((c : ℤ√2) * (l.map fun e => (m.map fun f => if P e f then ev e * ev f else 0).sum).sum) =
        c * (l.map fun e => (m.map fun f => if P e f then part (ev e * ev f) else 0).sum).sum) :
    |part ((t.2.2 : ℤ√2) * (t.1.map fun e => (t.2.1.map fun f =>
        if e.1 = i ∧ f.1 = j then ev e * ev f else 0).sum).sum)| ≤ 2 * ((t.2.2 * (ellL t.1 * ellL t.2.1) : ℕ) : ℤ) := by
  rw [hlin, abs_mul, Nat.abs_cast, ellL_eq, ellL_eq]
  have := abs_dsum_le t.1 t.2.1 (fun e f => if e.1 = i ∧ f.1 = j then part (ev e * ev f) else 0)
    (fun e => e.2.1.2 + e.2.2.2) (fun f => f.2.1.2 + f.2.2.2) (fun a b => by
      split_ifs
      · exact hpart a b
      · simp only [abs_zero]; positivity)
  calc (t.2.2 : ℤ) * |_| ≤ (t.2.2 : ℤ) * (2 * _) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by push_cast; ring

theorem re_lin (c : ℕ) (l m : List Ent) (P : Ent → Ent → Prop) [∀ a b, Decidable (P a b)] :
    ((c : ℤ√2) * (l.map fun e => (m.map fun f => if P e f then ev e * ev f else 0).sum).sum).re =
      c * (l.map fun e => (m.map fun f => if P e f then (ev e * ev f).re else 0).sum).sum := by
  rw [re_natCast_mul, re_lsum, List.map_map]
  congr 1; refine lsum_congr _ _ _ (fun e _ => ?_)
  simp only [Function.comp, re_lsum, List.map_map]
  refine lsum_congr _ _ _ (fun f _ => ?_)
  simp only [Function.comp]; split_ifs <;> simp

theorem im_lin (c : ℕ) (l m : List Ent) (P : Ent → Ent → Prop) [∀ a b, Decidable (P a b)] :
    ((c : ℤ√2) * (l.map fun e => (m.map fun f => if P e f then ev e * ev f else 0).sum).sum).im =
      c * (l.map fun e => (m.map fun f => if P e f then (ev e * ev f).im else 0).sum).sum := by
  rw [im_natCast_mul, im_lsum, List.map_map]
  congr 1; refine lsum_congr _ _ _ (fun e _ => ?_)
  simp only [Function.comp, im_lsum, List.map_map]
  refine lsum_congr _ _ _ (fun f _ => ?_)
  simp only [Function.comp]; split_ifs <;> simp

theorem coefG_bound (ts : List Term) (i j : ℕ) :
    |(coefG ts i j).re| ≤ 2 * bgSum ts ∧ |(coefG ts i j).im| ≤ 2 * bgSum ts := by
  rw [bgSum_eq]
  constructor
  · rw [coefG, re_lsum, List.map_map, natCast_lsum, ← List.sum_map_mul_left]
    refine (abs_lsum_le _ _).trans (lsum_le _ _ _ (fun t _ => ?_))
    exact (abs_term_le t i j Zsqrtd.re abs_re_mul_le (fun c l m P _ => re_lin c l m P)).trans
      (le_of_eq (by push_cast; ring))
  · rw [coefG, im_lsum, List.map_map, natCast_lsum, ← List.sum_map_mul_left]
    refine (abs_lsum_le _ _).trans (lsum_le _ _ _ (fun t _ => ?_))
    exact (abs_term_le t i j Zsqrtd.im abs_im_mul_le (fun c l m P _ => im_lin c l m P)).trans
      (le_of_eq (by push_cast; ring))

/-! ## Collapse -/

theorem coefC_eq (P : SP) (ts : List Term) (hidx : ∀ t ∈ ts, (∀ e ∈ t.1, e.1 < P.n) ∧ ∀ f ∈ t.2.1, f.1 < P.n)
    (γ : ℕ) : ∑ i ∈ range P.n, ∑ j ∈ range P.n, (if gamD P i j = γ then coefG ts i j else 0) =
      coefC (gamD P) ts γ := by
  have key : ∀ (e f : Ent) (c : ℕ), e.1 < P.n → f.1 < P.n →
      ∑ i ∈ range P.n, ∑ j ∈ range P.n,
          (if gamD P i j = γ then (if e.1 = i ∧ f.1 = j then (c : ℤ√2) * (ev e * ev f) else 0) else 0) =
        if gamD P e.1 f.1 = γ then (c : ℤ√2) * (ev e * ev f) else 0 := by
    intro e f c he hf
    rw [Finset.sum_eq_single e.1, Finset.sum_eq_single f.1]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_range.2 hf) h
    · intro i _ hi; refine Finset.sum_eq_zero (fun j _ => ?_); simp [Ne.symm hi]
    · intro h; exact absurd (Finset.mem_range.2 he) h
  have hexp : ∀ i j, (if gamD P i j = γ then coefG ts i j else 0) =
      (ts.map fun t => (t.1.map fun e => (t.2.1.map fun f =>
        if gamD P i j = γ then (if e.1 = i ∧ f.1 = j then (t.2.2 : ℤ√2) * (ev e * ev f) else 0)
          else 0).sum).sum).sum := by
    intro i j
    split_ifs with hg
    · rw [coefG]; refine lsum_congr _ _ _ (fun t _ => ?_)
      rw [lsum_mul_left]; refine lsum_congr _ _ _ (fun e _ => ?_)
      rw [lsum_mul_left]; refine lsum_congr _ _ _ (fun f _ => ?_)
      split_ifs <;> simp
    · exact (lsum_zero _ _ (fun t _ => lsum_zero _ _ (fun e _ => lsum_zero _ _ (fun f _ => rfl)))).symm
  have hexch : ∑ i ∈ range P.n, ∑ j ∈ range P.n,
      (ts.map fun t => (t.1.map fun e => (t.2.1.map fun f =>
        if gamD P i j = γ then (if e.1 = i ∧ f.1 = j then (t.2.2 : ℤ√2) * (ev e * ev f) else 0)
          else 0).sum).sum).sum =
      (ts.map fun t => (t.1.map fun e => (t.2.1.map fun f => ∑ i ∈ range P.n, ∑ j ∈ range P.n,
        if gamD P i j = γ then (if e.1 = i ∧ f.1 = j then (t.2.2 : ℤ√2) * (ev e * ev f) else 0)
          else 0).sum).sum).sum := by
    simp only [lsum_fsum_comm]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hexp i j)), hexch, coefC]
  refine lsum_congr _ _ _ (fun t ht => ?_)
  rw [lsum_mul_left]; refine lsum_congr _ _ _ (fun e he => ?_)
  rw [lsum_mul_left]; refine lsum_congr _ _ _ (fun f hf => ?_)
  rw [key e f t.2.2 ((hidx t ht).1 e he) ((hidx t ht).2 f hf)]
  split_ifs <;> simp

theorem coefC_bound (P : SP) (ts : List Term) (hidx : ∀ t ∈ ts, (∀ e ∈ t.1, e.1 < P.n) ∧ ∀ f ∈ t.2.1, f.1 < P.n)
    (γ : ℕ) : |(coefC (gamD P) ts γ).re| ≤ P.n * P.n * (2 * bgSum ts) ∧
      |(coefC (gamD P) ts γ).im| ≤ P.n * P.n * (2 * bgSum ts) := by
  rw [← coefC_eq P ts hidx γ, re_fsum, im_fsum]
  constructor
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range P.n, |(∑ j ∈ range P.n, if gamD P i j = γ then coefG ts i j else 0).re|
        ≤ ∑ i ∈ range P.n, ((P.n : ℤ) * (2 * bgSum ts)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [re_fsum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ j ∈ range P.n, |(if gamD P i j = γ then coefG ts i j else 0).re|
              ≤ ∑ j ∈ range P.n, ((2 * bgSum ts : ℕ) : ℤ) := by
                refine Finset.sum_le_sum (fun j _ => ?_)
                split_ifs
                · push_cast; exact (coefG_bound ts i j).1
                · simp
            _ = _ := by simp
      _ = _ := by simp; ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range P.n, |(∑ j ∈ range P.n, if gamD P i j = γ then coefG ts i j else 0).im|
        ≤ ∑ i ∈ range P.n, ((P.n : ℤ) * (2 * bgSum ts)) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [im_fsum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ j ∈ range P.n, |(if gamD P i j = γ then coefG ts i j else 0).im|
              ≤ ∑ j ∈ range P.n, ((2 * bgSum ts : ℕ) : ℤ) := by
                refine Finset.sum_le_sum (fun j _ => ?_)
                split_ifs
                · push_cast; exact (coefG_bound ts i j).2
                · simp
            _ = _ := by simp
      _ = _ := by simp; ring

/-! ## The stage -/

theorem stage_fst (P : SP) (ts : List Term) : (stage P ts).1 =
    ((rowsGo P.W P.n ts (rep z4 P.n)).1 && Nat.blt (Nat.mul 2 (bgSum ts)) (Nat.shiftLeft 1 (Nat.sub P.W 1)) &&
      Nat.blt (Nat.mul (Nat.mul P.n P.n) (Nat.mul 2 (bgSum ts))) (Nat.shiftLeft 1 (Nat.sub P.W2 1))) := rfl

theorem stage_snd (P : SP) (ts : List Term) : (stage P ts).2 =
    outOf P (scatAll P.W P.W2 P.gw (Nat.shiftLeft 1 (Nat.sub P.W 1)) (biasN P.W P.n) P.n P.gam
      (rowsGo P.W P.n ts (rep z4 P.n)).2 0 z4) := rfl

theorem stage_sound (P : SP) (ts : List Term) (hW : 1 ≤ P.W) (hW2 : 1 ≤ P.W2)
    (hgam : ∀ i < P.n, ∀ j < P.n, gamD P i j < P.N) (hok : (stage P ts).1 = true) :
    ((stage P ts).2.map fun e => (e.1, ev e)) = (List.range P.N).map (fun γ => (γ, coefC (gamD P) ts γ)) ∧
    ∀ t ∈ ts, (∀ e ∈ t.1, e.1 < P.n) ∧ ∀ f ∈ t.2.1, f.1 < P.n := by
  rw [stage_fst] at hok
  simp only [Bool.and_eq_true, nblt, decide_eq_true_iff, nmul, nshl, one_mul, nsub] at hok
  obtain ⟨⟨hR, hB1⟩, hB2⟩ := hok
  obtain ⟨r1, r2, r3⟩ := rowsGo_spec P.W P.n ts (rep z4 P.n) hR
  rw [rep_length] at r1 r2 r3
  refine ⟨?_, r2⟩
  set R := (rowsGo P.W P.n ts (rep z4 P.n)).2 with hRdef
  -- rows in digit form
  have hrow : ∀ i < P.n, rv (R.getD i z4) = ∑ j ∈ range P.n, coefG ts i j * 2 ^ (P.W * j) := by
    intro i hi
    rw [r3 i hi, rep_getD, rv_zero, zero_add]
    exact rows_eq P.W P.n ts (fun t ht => (r2 t ht).2) i
  -- exact row digits
  have hdec : ∀ i < P.n, ∀ j < P.n,
      (dig P.W ((R.getD i z4).1 + biasN P.W P.n - (R.getD i z4).2.1) j : ℤ) = (coefG ts i j).re + 2 ^ (P.W - 1) ∧
      (dig P.W ((R.getD i z4).2.2.1 + biasN P.W P.n - (R.getD i z4).2.2.2) j : ℤ) =
        (coefG ts i j).im + 2 ^ (P.W - 1) := by
    intro i hi j hj
    have hre := congrArg Zsqrtd.re (hrow i hi)
    have him := congrArg Zsqrtd.im (hrow i hi)
    simp only [rv, re_fsum, im_fsum, re_mul_two_pow, im_mul_two_pow] at hre him
    have hbd : ∀ j, |(coefG ts i j).re| < 2 ^ (P.W - 1) ∧ |(coefG ts i j).im| < 2 ^ (P.W - 1) := fun j =>
      ⟨lt_of_le_of_lt (coefG_bound ts i j).1 (by exact_mod_cast hB1),
        lt_of_le_of_lt (coefG_bound ts i j).2 (by exact_mod_cast hB1)⟩
    exact ⟨(decode P.W P.n hW (fun j => (coefG ts i j).re) (fun j _ => (hbd j).1) _ _ hre).2 j hj,
      (decode P.W P.n hW (fun j => (coefG ts i j).im) (fun j _ => (hbd j).2) _ _ him).2 j hj⟩
  -- the scatter
  set C := scatAll P.W P.W2 P.gw (Nat.shiftLeft 1 (Nat.sub P.W 1)) (biasN P.W P.n) P.n P.gam R 0 z4 with hCdef
  have hC : rv C = ∑ γ ∈ range P.N, coefC (gamD P) ts γ * 2 ^ (P.W2 * γ) := by
    rw [hCdef, scatAll_spec, rv_zero, zero_add, r1]
    have h1 : ∀ i ∈ range P.n, ∀ j ∈ range P.n,
        (⟨(dig P.W ((R.getD i z4).1 + biasN P.W P.n - (R.getD i z4).2.1) j : ℤ) - (Nat.shiftLeft 1 (Nat.sub P.W 1) : ℕ),
          (dig P.W ((R.getD i z4).2.2.1 + biasN P.W P.n - (R.getD i z4).2.2.2) j : ℤ) -
            (Nat.shiftLeft 1 (Nat.sub P.W 1) : ℕ)⟩ : ℤ√2) * 2 ^ (P.W2 * dig P.gw (P.gam (0 + i)) j) =
          ∑ γ ∈ range P.N, (if gamD P i j = γ then coefG ts i j else 0) * 2 ^ (P.W2 * γ) := by
      intro i hi j hj
      obtain ⟨d1, d2⟩ := hdec i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)
      rw [d1, d2, nshl, nsub, one_mul, zero_add]
      push_cast
      simp only [add_sub_cancel_right]
      have hγ := hgam i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj)
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hγ)]
      rfl
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h1 i hi j hj))]
    have h2 : ∀ γ ∈ range P.N, coefC (gamD P) ts γ * 2 ^ (P.W2 * γ) =
        ∑ i ∈ range P.n, ∑ j ∈ range P.n, (if gamD P i j = γ then coefG ts i j else 0) * 2 ^ (P.W2 * γ) := by
      intro γ _
      rw [← coefC_eq P ts r2 γ, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_mul _ _ _)
    rw [Finset.sum_congr rfl h2]
    calc _ = ∑ i ∈ range P.n, ∑ γ ∈ range P.N, ∑ j ∈ range P.n,
          (if gamD P i j = γ then coefG ts i j else 0) * 2 ^ (P.W2 * γ) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  -- the output digits
  have hre := congrArg Zsqrtd.re hC
  have him := congrArg Zsqrtd.im hC
  simp only [rv, re_fsum, im_fsum, re_mul_two_pow, im_mul_two_pow] at hre him
  have hcb : ∀ γ, |(coefC (gamD P) ts γ).re| < 2 ^ (P.W2 - 1) ∧ |(coefC (gamD P) ts γ).im| < 2 ^ (P.W2 - 1) :=
    fun γ => ⟨lt_of_le_of_lt (coefC_bound P ts r2 γ).1 (by exact_mod_cast hB2),
      lt_of_le_of_lt (coefC_bound P ts r2 γ).2 (by exact_mod_cast hB2)⟩
  have du := (decode P.W2 P.N hW2 (fun γ => (coefC (gamD P) ts γ).re) (fun γ _ => (hcb γ).1) _ _ hre).2
  have dv := (decode P.W2 P.N hW2 (fun γ => (coefC (gamD P) ts γ).im) (fun γ _ => (hcb γ).2) _ _ him).2
  rw [stage_snd, ← hCdef, outOf, decOut_spec]
  refine List.map_congr_left (fun γ hγ => ?_)
  have hγ' := List.mem_range.1 hγ
  simp only [nadd, nsub, nshl, one_mul, zero_add]
  rw [du γ hγ', dv γ hγ']
  push_cast
  simp only [add_sub_cancel_right]

end ThomsonCompact.TailC
