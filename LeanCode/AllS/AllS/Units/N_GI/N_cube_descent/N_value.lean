import AllS.Units.N_GI.N_cube_descent.N_double_active

noncomputable section
open Real Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

def cubeValue (q : Fin 3 → ℝ) : ℝ := (√(∑k,1/q k))⁻¹

theorem cube_reciprocal_sum_pos (q : Fin 3 → ℝ) (hq : ∀k,0<q k) : 0<∑k,1/q k :=
  Finset.sum_pos (fun k _ => one_div_pos.mpr (hq k)) Finset.univ_nonempty

theorem cubeValue_pos (q : Fin 3 → ℝ) (hq : ∀k,0<q k) : 0<cubeValue q :=
  inv_pos.mpr (Real.sqrt_pos.mpr (cube_reciprocal_sum_pos q hq))

theorem cubeValue_equations (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (hs : ∑k,q k=1) :
    CubeEquations (cubeValue q) q := by
  refine ⟨cubeValue_pos q hq,hq,hs,?_⟩
  rw [cubeValue,inv_pow,Real.sq_sqrt (cube_reciprocal_sum_pos q hq).le,inv_mul_cancel₀ (cube_reciprocal_sum_pos q hq).ne']

theorem cubeValue_eq (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) : cubeValue q=c := by
  have hv := cubeValue_equations q h.2.1 h.2.2.1
  have he : (cubeValue q)^2=c^2 := (mul_right_cancel₀ (cube_reciprocal_sum_pos q h.2.1).ne' (hv.2.2.2.trans h.2.2.2.symm))
  nlinarith [hv.1,h.1]

theorem cubeValue_continuousAt (q : Fin 3 → ℝ) (hq : ∀k,0<q k) : ContinuousAt cubeValue q := by
  unfold cubeValue
  apply ContinuousAt.inv₀
  · apply ContinuousAt.sqrt
    apply tendsto_finsetSum
    intro k _
    exact continuousAt_const.div (continuous_apply k).continuousAt (hq k).ne'
  · exact (Real.sqrt_pos.mpr (cube_reciprocal_sum_pos q hq)).ne'

theorem cubeValue_lt_of_sum (q q' : Fin 3 → ℝ) (hq : ∀k,0<q k) (hq' : ∀k,0<q' k)
    (hs : (∑k,1/q k)<∑k,1/q' k) : cubeValue q'<cubeValue q := by
  apply (inv_lt_inv₀ (Real.sqrt_pos.mpr (cube_reciprocal_sum_pos q' hq'))
    (Real.sqrt_pos.mpr (cube_reciprocal_sum_pos q hq))).mpr
  exact Real.sqrt_lt_sqrt (cube_reciprocal_sum_pos q hq).le hs

theorem CubeDescentCurve.reindex {c : ℝ} {q : Fin 3 → ℝ} (h : CubeDescentCurve c q)
    (e : Equiv.Perm (Fin 3)) : CubeDescentCurve c (q ∘ e) := by
  obtain ⟨γ,hγ,h0,hm⟩ := h
  refine ⟨fun t => ((γ t).1,(γ t).2 ∘ e),?_,by simp only [h0],?_⟩
  · exact hγ.fst.prodMk (continuousAt_pi.mpr (fun k => ((continuous_apply (e k)).continuousAt.comp hγ.snd)))
  · filter_upwards [hm] with t ht
    exact ⟨cube_feasible_reindex _ _ e ht.1,ht.2⟩

theorem cube_equations_unequal (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q) (hc : c<7/25) :
    ∃i j,q i<q j := by
  by_contra hn
  push_neg at hn
  have he : q=fun _ => q 0 := funext (fun k => le_antisymm (hn 0 k) (hn k 0))
  have hs := h.2.2.1
  rw [he] at hs
  have h0 : q 0=1/3 := by norm_num at hs;linarith
  have hr := h.2.2.2
  rw [he,h0] at hr
  norm_num at hr
  nlinarith [h.1]

#print axioms cubeValue_equations
end Blueprint.Thomson.Tail.Implementation
