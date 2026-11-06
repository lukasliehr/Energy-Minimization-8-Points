import AllS.Units.N_GI.N_cube_descent.N_definitions
import AllS.Units.N_GI.N_constants.N_algebra

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem packingHeight_positive_root_unique (c : ℝ) (hc : 0<c) (hp : 7*c^2+2*c-1=0) :
    c=packingHeight := by
  have ha := packingHeight_mem_Ioo.1
  have hh : (c-packingHeight)*(7*(c+packingHeight)+2)=0 := by nlinarith [packingHeight_quadratic]
  have hn : 7*(c+packingHeight)+2≠0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hn)

theorem cube_double_active_ordered (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q)
    (h0 : q 0=cubeUpper c) (h1 : q 1=cubeLower c) : c=packingHeight ∧ q 2=c := by
  obtain ⟨hc,hq,hs,hr⟩ := h
  rw [Fin.sum_univ_three,h0,h1] at hs
  have hh : (∑k,c^2/q k)=1 := by simpa only [Finset.mul_sum,mul_one_div] using hr
  rw [Fin.sum_univ_three,h0,h1,(cube_bounds_reciprocal c hc).1,
    (cube_bounds_reciprocal c hc).2] at hh
  have he : c^2/q 2=q 2 := by linarith
  have hsq : c^2=(q 2)^2 := by
    have hh := (div_eq_iff (hq 2).ne').mp he
    nlinarith
  have hq2 : q 2=c := by nlinarith [hq 2]
  rw [hq2] at hs
  have hpoly : 7*c^2+2*c-1=0 := by
    unfold cubeUpper cubeLower at hs
    have hn : 1+c≠0 := by positivity
    field_simp [hn] at hs
    nlinarith
  exact ⟨packingHeight_positive_root_unique c hc hpoly,hq2⟩

theorem fin3_equiv_pair (i j : Fin 3) (hij : i≠j) :
    ∃e : Equiv.Perm (Fin 3),e 0=i ∧ e 1=j := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨Equiv.refl _,rfl,rfl⟩
  · exact ⟨Equiv.swap 1 2,by decide,by decide⟩
  · exact ⟨Equiv.swap 0 1,by decide,by decide⟩
  · exact False.elim (hij rfl)
  · exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2),by decide,by decide⟩
  · exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2),by decide,by decide⟩
  · exact ⟨Equiv.swap 0 2,by decide,by decide⟩
  · exact False.elim (hij rfl)

theorem cube_descent_double_active (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q)
    (hc : c<7/25) (i j : Fin 3) (hi : q i=cubeUpper c) (hj : q j=cubeLower c) :
    c=packingHeight ∧ ∃k : Fin 3,k≠i ∧ k≠j ∧ q k=c := by
  have hij : i≠j := by
    intro he;subst j
    have hh := cube_bounds_strict c h.1.1 (by linarith)
    rw [←hi,←hj] at hh
    exact lt_irrefl _ hh
  obtain ⟨e,he0,he1⟩ := fin3_equiv_pair i j hij
  have h0 : (q ∘ e) 0=cubeUpper c := by rw [Function.comp_apply,he0,hi]
  have h1 : (q ∘ e) 1=cubeLower c := by rw [Function.comp_apply,he1,hj]
  obtain ⟨ha,hq⟩ := cube_double_active_ordered c (q ∘ e) (cube_equations_reindex c q e h.1) h0 h1
  refine ⟨ha,e 2,?_,?_,hq⟩
  · rw [←he0];exact e.injective.ne (by decide)
  · rw [←he1];exact e.injective.ne (by decide)

#print axioms cube_descent_double_active
end Blueprint.Thomson.Tail.Implementation
