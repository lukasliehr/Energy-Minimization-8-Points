import ThomsonCompact.CoeffMap.Prog
import ThomsonCompact.Packed.Comp
import ThomsonCompact.CoeffMap.PackLemmas

/-!
# W0 block contributions on packed Taylor models: soundness

The kernel programs (`sumTM`, `mulOpt`, `smulQ`, `zTM`, `pTM`, `gTM`) are in the Init-only `CoeffMap.Prog`.
For one Gram block with row-sparse column matrix `K` (row `u` lists `(i, Kᵤᵢ)`; an entry is a TM or `none`,
the exact constant `1`), Gram TMs `W i j` and a sparse rational coefficient list `E = [(u, v, ±m)]` with
denominator `den`, the kernel program

  `zTM i v = Σ_{(j,e) ∈ row v} e · W i j`,  `pTM u v = Σ_{(i,e) ∈ row u} e · zTM i v`,
  `gTM = Σ_{(u,v,±m) ∈ E} (±m/den) · pTM u v`

computes `Σ_E (±m/den) (K W Kᵀ)ᵤᵥ`, i.e. `contribution a K W b t` of `CoeffMap.W0Link` once `row` and `E`
represent `blockMatrix` and `blockCoef b t` (`CoeffMap.Rep`). Rational scalars are rounded to the TM scale
with error one unit (`smul` with `dq = 1`, F1's `ratMag_err`).

`gTM_sound`: TM-valid inputs (`EnclOk`: `ok → Encl`) and `ok = true` of the result give `Encl` of the real
contraction `gF`; F1's `Encl.valid` turns it into the old `TM.Valid` (`B_valid`).
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

variable {N S B W : ℕ}

/-- `A` encloses `f` once its `ok` flag is set. -/
def EnclOk (c : Ctx) (A : TM) (f : ℝ → ℝ) : Prop := A.ok = true → Encl c A f

theorem EnclOk.congr {c : Ctx} {T : TM} {f g : ℝ → ℝ} (h : EnclOk c T f)
    (hfg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t = g t) : EnclOk c T g := fun hok => (h hok).congr hfg

theorem zero_enclOk : EnclOk (mkCtx N S B W) zeroTM (fun _ => 0) := fun _ => zero_sound

theorem sumTM_sound : ∀ {Ts : List TM} {Fs : List (ℝ → ℝ)},
    List.Forall₂ (EnclOk (mkCtx N S B W)) Ts Fs →
      EnclOk (mkCtx N S B W) (sumTM (mkCtx N S B W) Ts) (fun t => (Fs.map fun f => f t).sum)
  | [], [], List.Forall₂.nil => zero_enclOk
  | _ :: _, _ :: _, List.Forall₂.cons hA hL => by
    intro hok
    have h := add_sound (hA (add_ok hok).1) (sumTM_sound hL (add_ok hok).2) hok
    exact h.congr (fun t _ => by simp)

theorem forall₂_map {α β γ δ : Type*} {R : γ → δ → Prop} {P : α → β → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ a b, P a b → R (f a) (g b)) :
    ∀ {L : List α} {M : List β}, List.Forall₂ P L M → List.Forall₂ R (L.map f) (M.map g)
  | [], [], List.Forall₂.nil => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons hab hLM => List.Forall₂.cons (h _ _ hab) (forall₂_map h hLM)

theorem forall₂_map_same {α γ δ : Type*} {R : γ → δ → Prop} {f : α → γ} {g : α → δ} :
    ∀ (L : List α), (∀ a ∈ L, R (f a) (g a)) → List.Forall₂ R (L.map f) (L.map g)
  | [], _ => List.Forall₂.nil
  | a :: L, h => List.Forall₂.cons (h a (by simp))
      (forall₂_map_same L (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-! ## Column-matrix entries and rational scalars -/

/-- Semantics of an entry: `none` is the constant `1` on the cell, `some K` encloses `κ`. -/
def EntryOk (c : Ctx) : Option TM → (ℝ → ℝ) → Prop
  | none, κ => ∀ t ∈ Set.Icc (-1 : ℝ) 1, κ t = 1
  | some K, κ => EnclOk c K κ

theorem mulOpt_sound (hg : Good N S B W) {e : Option TM} {κ : ℝ → ℝ} {A : TM} {f : ℝ → ℝ}
    (he : EntryOk (mkCtx N S B W) e κ) (hA : EnclOk (mkCtx N S B W) A f) :
    EnclOk (mkCtx N S B W) (mulOpt (mkCtx N S B W) e A) (fun t => κ t * f t) := by
  cases e with
  | none => exact hA.congr (fun t ht => by rw [show κ t = 1 from he t ht, one_mul])
  | some K =>
    intro hok
    exact mul_sound hg (he (mul_ok hok).1) (hA (mul_ok hok).2) hok

theorem smulQ_sound (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (neg : Bool) (m den : ℕ)
    (hA : EnclOk (mkCtx N S B W) A f) :
    EnclOk (mkCtx N S B W) (smulQ (mkCtx N S B W) neg m den A) (fun t => qval (neg, m, den) * f t) := by
  intro hok
  exact smul_sound hg (hA (smul_ok hok)) neg _ 1 (qval (neg, m, den)) (ratMag_err (neg, m, den)) hok

/-! ## The block contraction -/

noncomputable def zF (Wf : Nat → Nat → ℝ → ℝ) (rowF : Nat → List (Nat × (ℝ → ℝ))) (i v : Nat) (t : ℝ) : ℝ :=
  ((rowF v).map fun q => q.2 t * Wf i q.1 t).sum

noncomputable def pF (Wf : Nat → Nat → ℝ → ℝ) (rowF : Nat → List (Nat × (ℝ → ℝ))) (u v : Nat) (t : ℝ) : ℝ :=
  ((rowF u).map fun q => q.2 t * zF Wf rowF q.1 v t).sum

noncomputable def gF (Wf : Nat → Nat → ℝ → ℝ) (rowF : Nat → List (Nat × (ℝ → ℝ)))
    (E : List (Nat × Nat × Bool × Nat)) (den : Nat) (t : ℝ) : ℝ :=
  (E.map fun e => qval (e.2.2.1, e.2.2.2, den) * pF Wf rowF e.1 e.2.1 t).sum

/-- TM rows match real rows: same indices, entries enclosed. -/
def RowOk (c : Ctx) (r : List (Nat × Option TM)) (rf : List (Nat × (ℝ → ℝ))) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ EntryOk c p.2 q.2) r rf

theorem zTM_sound (hg : Good N S B W) {WT : Nat → Nat → TM} {Wf : Nat → Nat → ℝ → ℝ}
    {row : Nat → List (Nat × Option TM)} {rowF : Nat → List (Nat × (ℝ → ℝ))}
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j)) (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
    (i v : Nat) : EnclOk (mkCtx N S B W) (zTM (mkCtx N S B W) WT row i v) (zF Wf rowF i v) := by
  have h := sumTM_sound (forall₂_map (R := EnclOk (mkCtx N S B W))
    (f := fun p => mulOpt (mkCtx N S B W) p.2 (WT i p.1)) (g := fun q t => q.2 t * Wf i q.1 t)
    (fun p q hpq => by
      rw [hpq.1]
      exact mulOpt_sound hg hpq.2 (hW i q.1)) (hrow v))
  exact h.congr (fun t _ => by simp [zF, List.map_map, Function.comp_def])

theorem pTM_sound (hg : Good N S B W) {WT : Nat → Nat → TM} {Wf : Nat → Nat → ℝ → ℝ}
    {row : Nat → List (Nat × Option TM)} {rowF : Nat → List (Nat × (ℝ → ℝ))}
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j)) (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
    (u v : Nat) : EnclOk (mkCtx N S B W) (pTM (mkCtx N S B W) WT row u v) (pF Wf rowF u v) := by
  have h := sumTM_sound (forall₂_map (R := EnclOk (mkCtx N S B W))
    (f := fun p => mulOpt (mkCtx N S B W) p.2 (zTM (mkCtx N S B W) WT row p.1 v))
    (g := fun q t => q.2 t * zF Wf rowF q.1 v t)
    (fun p q hpq => by
      rw [hpq.1]
      exact mulOpt_sound hg hpq.2 (zTM_sound hg hW hrow q.1 v)) (hrow u))
  exact h.congr (fun t _ => by simp [pF, List.map_map, Function.comp_def])

/-- **Soundness of the block contribution program**: TM-valid Gram entries and column entries give a TM-valid
contraction once the result's `ok` flag is set. -/
theorem gTM_sound (hg : Good N S B W) {WT : Nat → Nat → TM} {Wf : Nat → Nat → ℝ → ℝ}
    {row : Nat → List (Nat × Option TM)} {rowF : Nat → List (Nat × (ℝ → ℝ))}
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j)) (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
    (E : List (Nat × Nat × Bool × Nat)) (den : Nat) :
    EnclOk (mkCtx N S B W) (gTM (mkCtx N S B W) WT row E den) (gF Wf rowF E den) := by
  have h := sumTM_sound (forall₂_map_same (R := EnclOk (mkCtx N S B W))
    (f := fun e => smulQ (mkCtx N S B W) e.2.2.1 e.2.2.2 den (pTM (mkCtx N S B W) WT row e.1 e.2.1))
    (g := fun e t => qval (e.2.2.1, e.2.2.2, den) * pF Wf rowF e.1 e.2.1 t) E
    (fun e _ => smulQ_sound hg e.2.2.1 e.2.2.2 den (pTM_sound hg hW hrow e.1 e.2.1)))
  exact h.congr (fun t _ => by simp [gF, List.map_map, Function.comp_def])

#print axioms gTM_sound

/-! ## Tabled contraction (F2c) -/

theorem zLook_eq (c : Ctx) (WT : ℕ → ℕ → TM) (row : ℕ → List (ℕ × Option TM)) (n m i v : ℕ) :
    zLook c WT row (zTab c WT row n m) n m i v = zTM c WT row i v := by
  unfold zLook
  cases h : (Nat.blt i n && Nat.blt v m)
  · rfl
  · rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
    rw [cond_true, zTab, listAt_mkList _ _ h.1, listAt_mkList _ _ h.2]

theorem pivotOf_some {L : List (ℕ × Option TM)} {j : ℕ} (h : pivotOf L = some j) : L = [(j, none)] := by
  unfold pivotOf at h
  split at h
  · cases h
    rfl
  · cases h

/-- `(K W Kᵀ)ᵤᵥ` through the z table; for a pivot row `v = e_j` it is `zTM j u` (needs `W` symmetric). -/
theorem pTMz_sound (hg : Good N S B W) {WT : ℕ → ℕ → TM} {Wf : ℕ → ℕ → ℝ → ℝ}
    {row : ℕ → List (ℕ × Option TM)} {rowF : ℕ → List (ℕ × (ℝ → ℝ))}
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j)) (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
    (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t) (n m u v : ℕ) :
    EnclOk (mkCtx N S B W) (pTMz (mkCtx N S B W) WT row (zTab (mkCtx N S B W) WT row n m) n m u v)
      (pF Wf rowF u v) := by
  unfold pTMz
  cases hp : pivotOf (row v) with
  | none =>
    show EnclOk _ (sumTM _ ((row u).map fun p => mulOpt _ p.2 (zLook _ WT row (zTab _ WT row n m) n m p.1 v))) _
    simp only [zLook_eq]
    exact pTM_sound hg hW hrow u v
  | some j =>
    show EnclOk _ (zLook _ WT row (zTab _ WT row n m) n m j u) _
    rw [zLook_eq]
    have hr := hrow v
    rw [pivotOf_some hp] at hr
    generalize hrf : rowF v = rf at hr
    rcases hr with _ | ⟨⟨hj, hκ⟩, hnil⟩
    rename_i q rest
    cases hnil
    refine (zTM_sound hg hW hrow j u).congr (fun t ht => ?_)
    have hz : ∀ i, zF Wf rowF i v t = Wf i j t := by
      intro i
      unfold zF
      rw [hrf]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hκ t ht, one_mul]
      simp only at hj
      rw [hj]
    unfold zF pF
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    rw [hz, hWs _ _ t ht]

theorem pTabz_lookup (c : Ctx) (WT : ℕ → ℕ → TM) (row : ℕ → List (ℕ × Option TM)) (zt : List (List TM))
    (n m k u v : ℕ) (hu : u < k) (hv : v < k) :
    listAt zeroTM (listAt [] (pTabz c WT row zt n m k) u) v = pTMz c WT row zt n m u v := by
  unfold pTabz
  rw [listAt_mkList _ _ hu, listAt_mkList _ _ hv]

/-- **Soundness of the tabled contraction** (entries of `E` in range, `W` symmetric on the cell). -/
theorem gTMz_sound (hg : Good N S B W) {WT : ℕ → ℕ → TM} {Wf : ℕ → ℕ → ℝ → ℝ}
    {row : ℕ → List (ℕ × Option TM)} {rowF : ℕ → List (ℕ × (ℝ → ℝ))}
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j)) (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
    (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t) (n m : ℕ) (E : List (ℕ × ℕ × Bool × ℕ))
    (den : ℕ) (hE : ∀ e ∈ E, e.1 < m ∧ e.2.1 < m) :
    EnclOk (mkCtx N S B W) (gTMz (mkCtx N S B W) WT row n m E den) (gF Wf rowF E den) := by
  have h := sumTM_sound (forall₂_map_same (R := EnclOk (mkCtx N S B W))
    (f := fun e => smulQ (mkCtx N S B W) e.2.2.1 e.2.2.2 den (listAt zeroTM (listAt []
      (pTabz (mkCtx N S B W) WT row (zTab (mkCtx N S B W) WT row n m) n m m) e.1) e.2.1))
    (g := fun e t => qval (e.2.2.1, e.2.2.2, den) * pF Wf rowF e.1 e.2.1 t) E
    (fun e he => by
      rw [pTabz_lookup _ _ _ _ _ _ _ _ _ (hE e he).1 (hE e he).2]
      exact smulQ_sound hg e.2.2.1 e.2.2.2 den (pTMz_sound hg hW hrow hWs n m e.1 e.2.1)))
  exact h.congr (fun t _ => by simp [gF, List.map_map, Function.comp_def])

#print axioms gTMz_sound

end ThomsonCompact.CoeffMap
