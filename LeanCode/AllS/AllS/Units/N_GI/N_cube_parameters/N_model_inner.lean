import AllS.Units.N_GI.N_cube_parameters.N_sign_products

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cubeModelA_inner (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (i j : Fin 4) :
    inner ℝ (cubeModelA e q i) (cubeModelA e q j)=∑k,cubeSign i k*cubeSign j k*q k := by
  unfold cubeModelA
  rw [he.inner_sum]
  simp only [conj_trivial]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (cubeSign i k*Real.sqrt (q k))*(cubeSign j k*Real.sqrt (q k)) =
      cubeSign i k*cubeSign j k*(Real.sqrt (q k))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (hq k).le]

theorem cubeModelB_inner (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (i j : Fin 4) :
    inner ℝ (cubeModelB e c q i) (cubeModelB e c q j)=
      ∑k,cubeSign i k*cubeSign j k*(c^2/q k) := by
  unfold cubeModelB
  rw [he.inner_sum]
  simp only [conj_trivial]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (-c*cubeSign i k/Real.sqrt (q k))*(-c*cubeSign j k/Real.sqrt (q k)) =
      cubeSign i k*cubeSign j k*(c^2/(Real.sqrt (q k))^2) := by ring
    _ = _ := by rw [Real.sq_sqrt (hq k).le]

theorem cubeModel_cross_inner (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (i j : Fin 4) :
    inner ℝ (cubeModelA e q i) (cubeModelB e c q j)=
      if i=j then -3*c else c := by
  rw [real_inner_comm (cubeModelB e c q j)]
  unfold cubeModelA cubeModelB
  rw [cube_dual_candidate_inner e he (fun k => Real.sqrt (q k))
    (fun k => Real.sqrt_pos.mpr (hq k)) c j i]
  by_cases hij : i=j
  · subst j;rw [if_pos rfl,if_pos rfl];ring
  · rw [if_neg hij,if_neg (Ne.symm hij)];ring

theorem cubeModelA_off_diagonal (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (hsum : ∑k,q k=1)
    (i j : Fin 4) (hij : i≠j) :
    inner ℝ (cubeModelA e q i) (cubeModelA e q j)=2*q (cubePairAxis i j)-1 := by
  rw [cubeModelA_inner e he q hq,cubeSign_weighted_dot q i j hij,hsum]

theorem cubeModelB_off_diagonal (e : Fin 3 → Point) (he : Orthonormal ℝ e)
    (c : ℝ) (q : Fin 3 → ℝ) (hq : ∀k,0<q k) (hsum : c^2*(∑k,1/q k)=1)
    (i j : Fin 4) (hij : i≠j) :
    inner ℝ (cubeModelB e c q i) (cubeModelB e c q j)=2*c^2/q (cubePairAxis i j)-1 := by
  rw [cubeModelB_inner e he c q hq,cubeSign_weighted_dot (fun k => c^2/q k) i j hij]
  have hh : (∑k,c^2/q k)=1 := by simpa only [Finset.mul_sum,mul_one_div] using hsum
  rw [hh]
  ring

#print axioms cubeModelA_inner
#print axioms cubeModelB_inner
#print axioms cubeModel_cross_inner
#print axioms cubeModelA_off_diagonal
#print axioms cubeModelB_off_diagonal
end Blueprint.Thomson.Tail.Implementation
