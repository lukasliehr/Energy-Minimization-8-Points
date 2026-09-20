import Thomson8.SumLinearity

namespace Thomson8

theorem list_sum_flatMap {α : Type*} (xs : List α) (f : α → List ℝ) :
    (xs.flatMap f).sum=(xs.map fun i => (f i).sum).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp [List.flatMap_cons,List.sum_append,ih]

theorem sum_range_eq_fin (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Fin.sum_univ_castSucc,ih]

theorem sum_four_exchange {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ c, f i j a c) = ∑ a, ∑ c, ∑ i, ∑ j, f i j a c := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (ij : α × β) (ac : γ × δ) => f ij.1 ij.2 ac.1 ac.2))

noncomputable def distinctSumHom : (Index → Index → Index → ℝ) →+ ℝ where
  toFun := distinctSum
  map_zero' := by simp [distinctSum]
  map_add' f g := distinctSum_add f g

theorem distinctSum_fin_sum {α : Type*} [Fintype α] (f : α → Index → Index → Index → ℝ) :
    distinctSum (fun i j k => ∑ a, f a i j k) = ∑ a, distinctSum (f a) := by
  have hf : (fun i j k => ∑ a, f a i j k) = ∑ a, f a := by
    funext i j k
    simp only [Finset.sum_apply]
  rw [hf]
  exact map_sum distinctSumHom f Finset.univ

end Thomson8
