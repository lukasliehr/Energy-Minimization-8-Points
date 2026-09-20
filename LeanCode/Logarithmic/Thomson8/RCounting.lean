import Thomson8.MomentMatrices
import Thomson8.Repeated
import Thomson8.SumLinearity

namespace Thomson8

open scoped InnerProductSpace

theorem symEval_swap12 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    Poly.symEval f u v t=Poly.symEval f v u t := by unfold Poly.symEval; ring

theorem symEval_swap23 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    Poly.symEval f u v t=Poly.symEval f u t v := by unfold Poly.symEval; ring

theorem repeated_triple_count (s : ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    (hs12 : ∀ u v t, s u v t=s v u t) (hs23 : ∀ u v t, s u v t=s u t v)
    (hdiag : s 1 1 1=c) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7)) =
      6*tripleSum (onTriples y s) := by
  let p : Index → Index → ℝ := fun i j => s ⟪y i,y j⟫_ℝ ⟪y i,y j⟫_ℝ 1
  have hrepeated : (fun i j : Index => onTriples y s i i j +
      onTriples y s i j i+onTriples y s j i i) = fun i j => 3*p i j := by
    funext i j
    simp only [onTriples,real_inner_self_eq_norm_sq,hy,one_pow,real_inner_comm (y j) (y i)]
    rw [hs12 1,hs23 _ 1]
    dsimp [p]
    simp only [real_inner_comm]
    ring
  have hdiagonal : (∑ i : Index, onTriples y s i i i)=8*c := by
    simp [onTriples,real_inner_self_eq_norm_sq,hy,hdiag]
  have hdecomp := tripleSum_decomposition (onTriples y s)
  rw [hrepeated,offSum_mul,hdiagonal] at hdecomp
  have hsplit : onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7) =
      fun i j k => 6*onTriples y s i j k+p i j+p i k+p j k+c/7 := rfl
  rw [hsplit,distinctSum_add,distinctSum_add,distinctSum_add,distinctSum_add,
    distinctSum_mul,distinctSum_pair,distinctSum_pair13,distinctSum_pair23,distinctSum_const]
  linarith

theorem kernelQ_diagonal (k : ℕ) : kernelQ k 1 1 1 = if k=0 then 1 else 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQ]
  | one => simp [kernelQ]
  | more k hk hk1 => simp [kernelQ]

theorem S_diagonal (k a b : ℕ) : (Block.S k a b).eval 1 1 1 = if k=0 then 1 else 0 := by
  rw [S_eval]
  simp only [Poly.symEval,one_pow,one_mul,kernelQ_diagonal]
  split_ifs <;> norm_num

theorem R_eval (k a b : ℕ) (u v t : ℝ) :
    (Block.R k a b).eval u v t =
      6*(Block.S k a b).eval u v t+(Block.S k a b).eval u u 1+
        (Block.S k a b).eval v v 1+(Block.S k a b).eval t t 1+(if k=0 then 1 else 0)/7 := by
  simp only [Block.R,Poly.eval_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Poly.eval_scale,K.eval_ofRat,Poly.eval_repeated_zero,Poly.eval_repeated_one,
    Poly.eval_repeated_two,Poly.eval_const]
  by_cases hk : k=0 <;> simp [hk] <;> ring

theorem sum_R_eq_moment (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) (a b : Fin m) :
    distinctSum (onTriples y (Block.R k a b).eval) = 6*momentMatrix m k y a b := by
  rw [momentMatrix_eq_sum_S]
  have hR : (Block.R k a b).eval = fun u v t =>
      6*(Block.S k a b).eval u v t+(Block.S k a b).eval u u 1+
        (Block.S k a b).eval v v 1+(Block.S k a b).eval t t 1+(if k=0 then 1 else 0)/7 :=
    funext fun u => funext fun v => funext fun t => R_eval _ _ _ _ _ _
  rw [hR]
  apply repeated_triple_count
  · intro u v t
    simp only [S_eval]
    apply symEval_swap12
  · intro u v t
    simp only [S_eval]
    apply symEval_swap23
  · exact S_diagonal _ _ _
  · exact hy

#print axioms sum_R_eq_moment

end Thomson8
