import Thomson8.Polynomial

namespace Thomson8.Poly

noncomputable def symEval (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (f u v t + f u t v + f v u t + f t u v + f v t u + f t v u)/6

theorem eval_permute (i : Fin 6) (p : Poly) (u v t : ℝ) :
    (permute i p).eval u v t =
    match i.val with
    | 0 => p.eval u v t
    | 1 => p.eval u t v
    | 2 => p.eval v u t
    | 3 => p.eval t u v
    | 4 => p.eval v t u
    | _ => p.eval t v u := by
  fin_cases i
  all_goals simp only [permute, eval_normalize]
  all_goals simp only [eval, List.map_map, Function.comp_def]
  all_goals
    congr 1
    apply List.map_congr_left
    rintro ⟨a,c⟩ _
    simp only [Exponent.eval]
    ring

theorem eval_symmetrize (p : Poly) (u v t : ℝ) :
    (symmetrize p).eval u v t = symEval p.eval u v t := by
  simp only [symmetrize, eval_scale, K.eval_ofRat, eval_sum]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  rw [eval_permute ⟨0,by decide⟩, eval_permute ⟨1,by decide⟩,
    eval_permute ⟨2,by decide⟩, eval_permute ⟨3,by decide⟩,
    eval_permute ⟨4,by decide⟩, eval_permute ⟨5,by decide⟩]
  norm_num [symEval]
  ring

end Thomson8.Poly
