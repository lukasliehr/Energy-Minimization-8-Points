import ThomsonNegative.Geometry.Confluent

noncomputable section
namespace ThomsonNegative.Geometry

lemma doubleNode_prior_contact (z : Fin 4 → ℝ) (hz : Function.Injective z)
    (x : ℝ) (k : ℕ) (hk : k < priorMultiplicity (doubleNode z) 8 x) :
    ∃ i : Fin 4,x=z i ∧ k < 2 := by
  classical
  have hn : 0 < ((Finset.range 8).filter (fun n => doubleNode z n=x)).card :=
    Nat.zero_lt_of_lt hk
  obtain ⟨n,hn⟩ := Finset.card_pos.mp hn
  let i : Fin 4 := ⟨(n/2)%4,Nat.mod_lt _ (by decide)⟩
  have hx : x=z i := (Finset.mem_filter.mp hn).2.symm
  refine ⟨i,hx,?_⟩
  rw [hx,doubleNode_multiplicity z hz i] at hk
  exact hk

/-- The source table depends only on the eight actual contact jets. This is
valid for arbitrary endpoint extensions of the surrounding jet functions. -/
theorem sourceNewtonHorner_double_congr (z : Fin 4 → ℝ) (hz : Function.Injective z)
    (J K : ℕ → ℝ → ℝ) (hJK : ∀ i k,k < 2 → J k (z i)=K k (z i)) :
    sourceNewtonHorner (doubleNode z) (fun i => confluentTable (doubleNode z) J i 0) 8 0 =
      sourceNewtonHorner (doubleNode z) (fun i => confluentTable (doubleNode z) K i 0) 8 0 := by
  rw [sourceNewtonHorner_eq,sourceNewtonHorner_eq]
  unfold sourceNewtonPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  rw [confluentTable_congr_jets (doubleNode z) J K 8 (doubleNode_grouped z hz)
    (fun x k hk => by
      obtain ⟨j,rfl,hk'⟩ := doubleNode_prior_contact z hz x k hk
      exact hJK j k hk') i 0 (by simpa using Finset.mem_range.mp hi)]

#print axioms sourceNewtonHorner_double_congr
end ThomsonNegative.Geometry
