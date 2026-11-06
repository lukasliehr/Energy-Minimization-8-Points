import AllS.Units.N_FI.N_rolle_multiset.N_induction

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

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

#check rolle_with_multiplicities
#print axioms rolle_with_multiplicities
#check rolle_multiset
#print axioms rolle_multiset
end Blueprint.Thomson.Finite
