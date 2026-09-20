import Thomson8.FastRows

namespace Thomson8.Poly

noncomputable def symEvalHom (u v t : ℝ) : (ℝ → ℝ → ℝ → ℝ) →+ ℝ where
  toFun := fun f => symEval f u v t
  map_zero' := by simp [symEval]
  map_add' f g := by simp [symEval]; ring

theorem symEval_fin_sum {α : Type*} [Fintype α] (f : α → ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval (fun u v t => ∑ i, f i u v t) u v t = ∑ i, symEval (f i) u v t := by
  have hf : (fun u v t => ∑ i, f i u v t) = ∑ i, f i := by
    funext u v t
    simp only [Finset.sum_apply]
  rw [hf]
  exact map_sum (symEvalHom u v t) f Finset.univ

theorem symEval_nonneg {f : ℝ → ℝ → ℝ → ℝ} (u v t : ℝ)
    (h0 : 0≤f u v t) (h1 : 0≤f u t v) (h2 : 0≤f v u t)
    (h3 : 0≤f t u v) (h4 : 0≤f v t u) (h5 : 0≤f t v u) :
    0≤symEval f u v t := by unfold symEval; positivity

end Thomson8.Poly
