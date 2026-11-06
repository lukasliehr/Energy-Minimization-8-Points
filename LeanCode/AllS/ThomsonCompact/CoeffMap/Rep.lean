import ThomsonCompact.CoeffMap.Contract

/-!
# Representation lemma: the TM contraction computes the block contribution (F2b b)

* `symEntries_sum`: for `P` symmetric on `[0,n)²`, the symmetric sparse list `symEntries z n` (pairs `u ≤ v`,
  doubled off-diagonal coefficients) represents the full coefficient matrix `z/den`.
* `gF_eq`: if the real rows `rowF u` represent the rows of a column matrix `K` (`hrow`), the Gram functions
  are a symmetric matrix `Wm` at `t` and `C = z/den`, then the real contraction `gF` of `CoeffMap.Contract` is
  `Σᵢⱼ Wmᵢⱼ Σᵤᵥ Kᵤᵢ Kᵥⱼ Cᵤᵥ`, which is `contribution` (`CoeffMap.W0Link`) for `K = blockMatrix`,
  `C = blockCoef`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

theorem qval_int (c : ℤ) (den : ℕ) : qval (decide (c < 0), c.natAbs, den) = (c : ℝ) / den := by
  unfold qval
  by_cases hc : c < 0
  · simp only [hc, decide_true, if_true]
    have : ((c.natAbs : ℕ) : ℝ) = -(c : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hc)]
    rw [this]; ring
  · simp only [hc, decide_false, Bool.false_eq_true, if_false]
    have : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hc))]
    rw [this]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

/-- A zero-skipping `filterMap` of signed entries sums like the dense list. -/
theorem filterMap_entries_sum (c : ℕ → ℤ) (v den : ℕ) (P : ℕ → ℕ → ℝ) : ∀ L : List ℕ,
    ((L.filterMap fun u => if c u = 0 then none else some (u, v, decide (c u < 0), (c u).natAbs)).map
        fun e => qval (e.2.2.1, e.2.2.2, den) * P e.1 e.2.1).sum =
      (L.map fun u => (c u : ℝ) / den * P u v).sum
  | [] => by simp
  | u :: L => by
    have ih := filterMap_entries_sum c v den P L
    by_cases hu : c u = 0
    · simp only [List.filterMap_cons, hu, if_true, List.map_cons, List.sum_cons, ih]
      simp
    · simp only [List.filterMap_cons, hu, if_false, List.map_cons, List.sum_cons, ih, qval_int]

theorem colEntries_sum (z : ℕ → ℕ → ℤ) (den : ℕ) (P : ℕ → ℕ → ℝ) (v : ℕ) :
    ((colEntries z v).map fun e => qval (e.2.2.1, e.2.2.2, den) * P e.1 e.2.1).sum =
      ∑ u ∈ Finset.range (v + 1), ((if u = v then z v v else z u v + z v u : ℤ) : ℝ) / den * P u v := by
  unfold colEntries
  rw [filterMap_entries_sum (fun u => if u = v then z v v else z u v + z v u) v den P, list_sum_range]

/-- **Symmetric entries represent the coefficient matrix** (for `P` symmetric on `[0,n)²`). -/
theorem symEntries_sum (z : ℕ → ℕ → ℤ) (den : ℕ) (P : ℕ → ℕ → ℝ) : ∀ n,
    (∀ u v, u < n → v < n → P u v = P v u) →
      ((symEntries z n).map fun e => qval (e.2.2.1, e.2.2.2, den) * P e.1 e.2.1).sum =
        ∑ u ∈ Finset.range n, ∑ v ∈ Finset.range n, (z u v : ℝ) / den * P u v
  | 0, _ => by simp [symEntries]
  | n + 1, hP => by
    have ih := symEntries_sum z den P n (fun u v hu hv => hP u v (by omega) (by omega))
    rw [symEntries, List.map_append, List.sum_append, ih, colEntries_sum, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [if_true]
    have h1 : ∑ u ∈ Finset.range n, ((if u = n then z n n else z u n + z n u : ℤ) : ℝ) / den * P u n =
        ∑ u ∈ Finset.range n, ((z u n : ℝ) / den * P u n + (z n u : ℝ) / den * P n u) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hun : u ≠ n := by have := Finset.mem_range.mp hu; omega
      rw [if_neg hun, hP n u (by omega) (by have := Finset.mem_range.mp hu; omega)]
      push_cast
      ring
    rw [h1, Finset.sum_add_distrib]
    have h2 : ∑ x ∈ Finset.range n, ∑ v ∈ Finset.range (n + 1), (z x v : ℝ) / den * P x v =
        ∑ x ∈ Finset.range n, ∑ v ∈ Finset.range n, (z x v : ℝ) / den * P x v +
          ∑ u ∈ Finset.range n, (z u n : ℝ) / den * P u n := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_range_succ]
    rw [h2, Finset.sum_range_succ]
    ring

/-- **The real contraction is the block contribution.** -/
theorem gF_eq {d n : ℕ} (Wf : ℕ → ℕ → ℝ → ℝ) (rowF : ℕ → List (ℕ × (ℝ → ℝ))) (z : ℕ → ℕ → ℤ) (den : ℕ)
    (K : Fin n → Fin d → ℝ) (Wm : Fin d → Fin d → ℝ) (C : Fin n → Fin n → ℝ) (t : ℝ)
    (hC : ∀ u v : Fin n, C u v = (z u v : ℝ) / den)
    (hrow : ∀ u : Fin n, ∀ F : ℕ → ℝ, ((rowF u).map fun q => q.2 t * F q.1).sum = ∑ i : Fin d, K u i * F i)
    (hW : ∀ i j : Fin d, Wf i j t = Wm i j) (hWs : ∀ i j, Wm i j = Wm j i) :
    gF Wf rowF (symEntries z n) den t = ∑ i, ∑ j, Wm i j * ∑ u, ∑ v, K u i * K v j * C u v := by
  have hp : ∀ u v : Fin n, pF Wf rowF u v t = ∑ i, ∑ j, K u i * K v j * Wm i j := by
    intro u v
    unfold pF
    rw [hrow u (fun i => zF Wf rowF i v t)]
    apply Finset.sum_congr rfl
    intro i _
    unfold zF
    rw [hrow v (fun j => Wf i j t), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hW i j]
    ring
  have hsym : ∀ u v, u < n → v < n → pF Wf rowF u v t = pF Wf rowF v u t := by
    intro u v hu hv
    have e1 := hp ⟨u, hu⟩ ⟨v, hv⟩
    have e2 := hp ⟨v, hv⟩ ⟨u, hu⟩
    simp only at e1 e2
    rw [e1, e2, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hWs j i]
    ring
  unfold gF
  rw [symEntries_sum z den (fun u v => pF Wf rowF u v t) n hsym]
  rw [← Fin.sum_univ_eq_sum_range (fun u => ∑ v ∈ Finset.range n, (z u v : ℝ) / den * pF Wf rowF u v t)]
  simp_rw [← Fin.sum_univ_eq_sum_range (fun v => (z _ v : ℝ) / den * pF Wf rowF _ v t)]
  simp_rw [hp, ← hC]
  simp_rw [Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin d × Fin d ≃ Fin d × Fin d × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl,
      fun _ => rfl⟩
  apply Fintype.sum_equiv e
  intro x
  simp only [e, Equiv.coe_fn_mk]
  ring

theorem colEntries_range (z : ℕ → ℕ → ℤ) (v : ℕ) : ∀ e ∈ colEntries z v, e.1 ≤ v ∧ e.2.1 = v := by
  intro e he
  unfold colEntries at he
  obtain ⟨u, hu, hue⟩ := List.mem_filterMap.mp he
  have hu' := List.mem_range.mp hu
  have key : ∀ (c : ℤ), (if c = 0 then none else some (u, v, decide (c < 0), c.natAbs)) = some e →
      e.1 = u ∧ e.2.1 = v := by
    intro c h
    by_cases hc : c = 0
    · simp [hc] at h
    · simp only [hc, if_false, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  have := key _ hue
  omega

theorem symEntries_range (z : ℕ → ℕ → ℤ) : ∀ n, ∀ e ∈ symEntries z n, e.1 < n ∧ e.2.1 < n
  | 0, e, he => by simp [symEntries] at he
  | n + 1, e, he => by
    rw [symEntries, List.mem_append] at he
    rcases he with he | he
    · have := symEntries_range z n e he; omega
    · have := colEntries_range z n e he; omega

theorem getD_pTab {c : ThomsonCompact.Packed.Ctx} {WT : ℕ → ℕ → TM} {row : ℕ → List (ℕ × Option TM)}
    {n u v : ℕ} (hu : u < n) (hv : v < n) :
    ((pTab c WT row n).getD u []).getD v zeroTM = pTM c WT row u v := by
  simp [pTab, List.getD_eq_getElem?_getD, hu, hv]

theorem gTMp_eq {c : ThomsonCompact.Packed.Ctx} {WT : ℕ → ℕ → TM} {row : ℕ → List (ℕ × Option TM)}
    {n : ℕ} {E : List (ℕ × ℕ × Bool × ℕ)} (den : ℕ) (hE : ∀ e ∈ E, e.1 < n ∧ e.2.1 < n) :
    gTMp c WT row n E den = gTM c WT row E den := by
  unfold gTMp gTM
  congr 1
  apply List.map_congr_left
  intro e he
  rw [getD_pTab (hE e he).1 (hE e he).2]

#print axioms symEntries_sum
#print axioms gF_eq

end ThomsonCompact.CoeffMap
