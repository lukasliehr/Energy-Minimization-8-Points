import Mathlib

/-!
Generic repeated-node Rolle theorem, adapted from read-only ThomsonV2 source.
The source-file hashes and original paths are recorded in
`analysis/root_scalar/rolle_provenance.json`. Only imports and namespace changed;
this copy compiles against the project's existing Lean 4.32/mathlib.
-/

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Analytic


/-- A continuous derivative tower on a compact interval; differentiation is
required in its interior only, so repeated endpoint zeros are allowed. -/
structure DerivativeTowerOn (f : ℕ → ℝ → ℝ) (N : ℕ) (l u : ℝ) : Prop where
  continuous : ∀ k, k ≤ N → ContinuousOn (f k) (Set.Icc l u)
  derivative : ∀ k, k < N → ∀ x ∈ Set.Ioo l u, HasDerivAt (f k) (f (k+1) x) x

/-- A sorted expanded zero multiset. Equal indices at the ends of a block
assert the zero jet of order equal to their index difference. -/
def JetZeroList (f : ℕ → ℝ → ℝ) {n : ℕ} (z : Fin n → ℝ) : Prop :=
  ∀ i j, i ≤ j → z i=z j → f (j.val-i.val) (z i)=0

theorem JetZeroList.value {f : ℕ → ℝ → ℝ} {n : ℕ} {z : Fin n → ℝ}
    (hz : JetZeroList f z) (i : Fin n) : f 0 (z i)=0 := by
  simpa using hz i i le_rfl rfl

/-- Ordinary zero jets at the counted multiplicity imply the expanded-list
condition used by repeated Rolle. -/
theorem JetZeroList.of_fiber_jets {f : ℕ → ℝ → ℝ} {n : ℕ} (z : Fin n → ℝ)
    (hmono : Monotone z)
    (hjet : ∀ i k, k < (Finset.univ.filter (fun j => z j=z i)).card → f k (z i)=0) :
    JetZeroList f z := by
  intro i j hij he
  apply hjet i (j.val-i.val)
  have hsub : Finset.Icc i j ⊆ Finset.univ.filter (fun k => z k=z i) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact le_antisymm ((hmono hk'.2).trans he.symm.le) (hmono hk'.1)
  have hc := Finset.card_le_card hsub
  have hcount : (Finset.Icc i j).card=j.val+1-i.val := by simp
  rw [hcount] at hc
  have hi : i.val ≤ j.val := hij
  omega

/-- One derivative removes exactly one zero from the expanded multiset. -/
theorem rolle_multiset_derivative_zeros (N : ℕ) (f : ℕ → ℝ → ℝ) (l u : ℝ)
    (hcont : ContinuousOn (f 0) (Set.Icc l u))
    (hder : ∀ x ∈ Set.Ioo l u, HasDerivAt (f 0) (f 1 x) x)
    (z : Fin (N+2) → ℝ) (hmono : Monotone z)
    (hmem : ∀ i, z i ∈ Set.Icc l u) (hzero : JetZeroList f z) :
    ∃ w : Fin (N+1) → ℝ, Monotone w ∧ (∀ i, w i ∈ Set.Icc l u) ∧
      JetZeroList (fun k => f (k+1)) w := by
  have hgap (i : Fin (N+1)) : ∃ x : ℝ,
      z i.castSucc ≤ x ∧ x ≤ z i.succ ∧ f 1 x=0 ∧
      (z i.castSucc < z i.succ → z i.castSucc < x ∧ x < z i.succ) := by
    have hle : i.castSucc ≤ i.succ := by
      change i.val ≤ i.val+1
      omega
    have hzle := hmono hle
    by_cases he : z i.castSucc=z i.succ
    · refine ⟨z i.castSucc,le_rfl,he.le,?_,?_⟩
      · have hh := hzero i.castSucc i.succ hle he
        have hdiff : i.succ.val-i.castSucc.val=1 := by simp
        simpa only [hdiff] using hh
      · intro hlt
        exact (hlt.ne he).elim
    · have hlt : z i.castSucc < z i.succ := lt_of_le_of_ne hzle he
      obtain ⟨x,hx,hfx⟩ := exists_hasDerivAt_eq_zero hlt
        (hcont.mono (by
          intro x hx
          exact ⟨(hmem i.castSucc).1.trans hx.1,hx.2.trans (hmem i.succ).2⟩))
        ((hzero.value i.castSucc).trans (hzero.value i.succ).symm)
        (by
          intro x hx
          exact hder x ⟨lt_of_le_of_lt (hmem i.castSucc).1 hx.1,
            lt_of_lt_of_le hx.2 (hmem i.succ).2⟩)
      exact ⟨x,hx.1.le,hx.2.le,hfx,fun _ => hx⟩
  choose w hwL hwR hw0 hwStrict using hgap
  have hbetween {i j : Fin (N+1)} (hij : i<j) : z i.succ ≤ z j.castSucc :=
    hmono (by simp only [Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at *; omega)
  have hmonoW : Monotone w := by
    intro i j hij
    rcases eq_or_lt_of_le hij with he|hlt
    · simpa [he]
    · exact (hwR i).trans ((hbetween hlt).trans (hwL j))
  have hleft (i : Fin (N+1)) (he : w i=z i.castSucc) : z i.castSucc=z i.succ := by
    by_contra hne
    have hh := (hwStrict i (lt_of_le_of_ne (hmono (by simp only [Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at *; omega)) hne)).1
    linarith
  have hright (i : Fin (N+1)) (he : w i=z i.succ) : z i.castSucc=z i.succ := by
    by_contra hne
    have hh := (hwStrict i (lt_of_le_of_ne (hmono (by simp only [Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at *; omega)) hne)).2
    linarith
  refine ⟨w,hmonoW,?_,?_⟩
  · intro i
    exact ⟨(hmem i.castSucc).1.trans (hwL i),(hwR i).trans (hmem i.succ).2⟩
  · intro i j hij he
    rcases eq_or_lt_of_le hij with heij|hlt
    · subst j
      simpa using hw0 i
    · have hchain := hbetween hlt
      have heRi : w i=z i.succ := by linarith [hwR i,hwL j]
      have heLj : w j=z j.castSucc := by linarith [hwR i,hwL j]
      have hzi := hright i heRi
      have hzj := hleft j heLj
      have hzEq : z i.castSucc=z j.succ := by linarith
      have hh := hzero i.castSucc j.succ (by simp only [Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at *; omega) hzEq
      have hdiff : j.succ.val-i.castSucc.val=(j.val-i.val)+1 := by
        simp only [Fin.val_succ,Fin.val_castSucc]
        omega
      rw [hdiff, hzi, ← heRi] at hh
      exact hh




theorem rolle_multiset_induction (N : ℕ) (f : ℕ → ℝ → ℝ) (l u : ℝ)
    (htower : DerivativeTowerOn f N l u) (z : Fin (N+1) → ℝ)
    (hmono : Monotone z) (hmem : ∀ i, z i ∈ Set.Icc l u) (hzero : JetZeroList f z) :
    ∃ ξ ∈ Set.Icc l u, f N ξ=0 := by
  induction N generalizing f with
  | zero => exact ⟨z 0,hmem 0,hzero.value 0⟩
  | succ N ih =>
    obtain ⟨w,hwmono,hwmem,hwzero⟩ := rolle_multiset_derivative_zeros N f l u
      (htower.continuous 0 (by omega)) (htower.derivative 0 (by omega)) z hmono hmem hzero
    have htower' : DerivativeTowerOn (fun k => f (k+1)) N l u := by
      constructor
      · intro k hk
        exact htower.continuous (k+1) (by omega)
      · intro k hk x hx
        exact htower.derivative (k+1) (by omega) x hx
    exact ih (fun k => f (k+1)) htower' w hwmono hwmem hwzero



open scoped BigOperators

private theorem count_ofFn_eq_fiber_card {n : ℕ} (z : Fin n → ℝ) (x : ℝ) :
    (List.ofFn z).count x=(Finset.univ.filter (fun i => z i=x)).card := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.count_cons,ih]
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_succ]
    by_cases h : z 0=x <;> simp [h,add_comm]

/-- A list-form consumer interface: count records all repeated nodes. -/
theorem rolle_multiset_list (N : ℕ) (f : ℕ → ℝ → ℝ) (l u : ℝ)
    (htower : DerivativeTowerOn f N l u) (L : List ℝ) (hlen : L.length=N+1)
    (hmono : L.SortedLE) (hmem : ∀ x ∈ L, x ∈ Set.Icc l u)
    (hjet : ∀ x ∈ L, ∀ k < L.count x, f k x=0) :
    ∃ ξ ∈ Set.Icc l u, f N ξ=0 := by
  have hz : JetZeroList f L.get := JetZeroList.of_fiber_jets L.get hmono (by
    intro i k hk
    apply hjet (L.get i) (List.get_mem _ _) k
    have hc := count_ofFn_eq_fiber_card L.get (L.get i)
    rw [List.ofFn_get] at hc
    rwa [hc])
  let z : Fin (N+1) → ℝ := fun i => L.get (Fin.cast hlen.symm i)
  apply rolle_multiset_induction N f l u htower z
  · intro i j hij
    exact hmono (show Fin.cast hlen.symm i ≤ Fin.cast hlen.symm j from hij)
  · intro i
    exact hmem _ (List.get_mem _ _)
  · intro i j hij he
    exact hz (Fin.cast hlen.symm i) (Fin.cast hlen.symm j) hij he

/-- Repeated-node Rolle, with the exact total multiplicity and all endpoint
jets represented by a multiset. No ordering assumption is required of inputs. -/
theorem rolle_multiset (N : ℕ) (f : ℕ → ℝ → ℝ) (l u : ℝ)
    (htower : DerivativeTowerOn f N l u) (Z : Multiset ℝ) (hcard : Z.card=N+1)
    (hmem : ∀ x ∈ Z, x ∈ Set.Icc l u)
    (hjet : ∀ x ∈ Z, ∀ k < Z.count x, f k x=0) :
    ∃ ξ ∈ Set.Icc l u, f N ξ=0 := by
  let L := Z.sort (· ≤ ·)
  have hlen : L.length=N+1 := by simpa [L] using hcard
  have hmono : L.SortedLE := (Multiset.pairwise_sort Z (· ≤ ·)).sortedLE
  apply rolle_multiset_list N f l u htower L hlen hmono
  · intro x hx
    exact hmem x ((Multiset.mem_sort (· ≤ ·)).mp hx)
  · intro x hx k hk
    apply hjet x ((Multiset.mem_sort (· ≤ ·)).mp hx) k
    have hc : L.count x=Z.count x := by
      rw [← Multiset.coe_count x L,Multiset.sort_eq]
    rwa [← hc]

/-- Canonical blueprint declaration, retaining the short consumer alias. -/
alias rolle_with_multiplicities := rolle_multiset

#print axioms rolle_multiset
end ThomsonNegative.Analytic
