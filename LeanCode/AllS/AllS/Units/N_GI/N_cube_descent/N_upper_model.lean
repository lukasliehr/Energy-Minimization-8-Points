import AllS.Units.N_GI.N_cube_descent.N_upper_roots

noncomputable section
open Real Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

def cubeUpperModel (c : ℝ) : Fin 3 → ℝ := ![cubeUpper c,cubeRootPlus c,cubeRootMinus c]

theorem cube_upper_equations_of_sum_product (c : ℝ) (q : Fin 3 → ℝ) (hc : 0<c)
    (hq : ∀k,0<q k) (h0 : q 0=cubeUpper c)
    (hs : q 1+q 2=cubeRootSum c) (hp : q 1*q 2=cubeRootProduct c) : CubeEquations c q := by
  refine ⟨hc,hq,?_,?_⟩
  · rw [Fin.sum_univ_three,add_assoc,h0,hs]
    unfold cubeUpper cubeRootSum
    ring
  · have hrpoly : c^2*(q 1*q 2+q 0*q 2+q 0*q 1)=q 0*q 1*q 2 := by
      calc
        _=c^2*(cubeRootProduct c+cubeUpper c*cubeRootSum c) := by rw [←hs,←hp,←h0];ring
        _=cubeUpper c*cubeRootProduct c := by
          unfold cubeUpper cubeRootSum cubeRootProduct
          have hn : 1+2*c≠0 := by positivity
          field_simp [hn]
          ring
        _=q 0*q 1*q 2 := by rw [←h0,←hp];ring
    rw [Fin.sum_univ_three]
    have hn0 := (hq 0).ne'
    have hn1 := (hq 1).ne'
    have hn2 := (hq 2).ne'
    field_simp [hn0,hn1,hn2]
    nlinarith [hrpoly]

theorem cubeUpperModel_equations (c : ℝ) (hc : 0<c) (hcub : c≤7/25) :
    CubeEquations c (cubeUpperModel c) := by
  obtain ⟨hs,hp⟩ := cube_roots_sum_product c hc hcub
  obtain ⟨hm,hpm⟩ := cube_roots_positive c hc hcub
  apply cube_upper_equations_of_sum_product c (cubeUpperModel c) hc _ rfl hs hp
  intro k
  fin_cases k
  · change 0<cubeUpper c;unfold cubeUpper;positivity
  · exact hm.trans hpm
  · exact hm

theorem cubeUpperModel_continuousAt (c : ℝ) (hc : 0<c) : ContinuousAt cubeUpperModel c := by
  apply continuousAt_pi.mpr
  intro k
  fin_cases k
  · change ContinuousAt cubeUpper c
    exact cubeUpper_continuous.continuousAt
  · change ContinuousAt cubeRootPlus c
    unfold cubeRootPlus cubeRootDiscriminant cubeRootSum cubeRootProduct
    fun_prop (disch := positivity)
  · change ContinuousAt cubeRootMinus c
    unfold cubeRootMinus cubeRootDiscriminant cubeRootSum cubeRootProduct
    fun_prop (disch := positivity)

theorem cubeUpperModel_recover (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q)
    (hc : c<7/25) (h0 : q 0=cubeUpper c) (h21 : q 2≤q 1) : cubeUpperModel c=q := by
  obtain ⟨hs,hp⟩ := cube_upper_sum_product c q h (by linarith) h0
  obtain ⟨h1,h2⟩ := cube_roots_recover c (q 1) (q 2) h.1 hc.le hs hp h21
  ext k
  fin_cases k
  · exact h0.symm
  · exact h1.symm
  · exact h2.symm

#print axioms cubeUpperModel_equations
end Blueprint.Thomson.Tail.Implementation
