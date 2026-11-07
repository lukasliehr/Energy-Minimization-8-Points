import AllS.Units.N_GI.N_disphenoid.N_opposite_lengths

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem unit_dist_eq_inner_eq (x y z w : Point)
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) (hw : ‖w‖=1)
    (hd : dist x y=dist z w) : inner ℝ x y=inner ℝ z w := by
  have h := congrArg (fun r : ℝ => r^2) hd
  rw [dist_eq_norm,dist_eq_norm,norm_sub_sq_real,norm_sub_sq_real,hx,hy,hz,hw] at h
  nlinarith

theorem disphenoid_sum_zero (A : Fin 4 → Point) (hunit : ∀i,‖A i‖=1)
    (h01 : inner ℝ (A 0) (A 1)=inner ℝ (A 2) (A 3))
    (h02 : inner ℝ (A 0) (A 2)=inner ℝ (A 1) (A 3))
    (h03 : inner ℝ (A 0) (A 3)=inner ℝ (A 1) (A 2))
    (w : Fin 4 → ℝ) (hw : ∑i,w i=1) (hwA : ∑i,w i • A i=0) : ∑i,A i=0 := by
  let S := 1+inner ℝ (A 0) (A 1)+inner ℝ (A 0) (A 2)+inner ℝ (A 0) (A 3)
  have hii : ∀i,inner ℝ (A i) (A i)=1 := by intro i;rw [real_inner_self_eq_norm_sq,hunit];norm_num
  have h10 : inner ℝ (A 1) (A 0)=inner ℝ (A 0) (A 1) := real_inner_comm _ _
  have h20 : inner ℝ (A 2) (A 0)=inner ℝ (A 0) (A 2) := real_inner_comm _ _
  have h30 : inner ℝ (A 3) (A 0)=inner ℝ (A 0) (A 3) := real_inner_comm _ _
  have h21 : inner ℝ (A 2) (A 1)=inner ℝ (A 1) (A 2) := real_inner_comm _ _
  have h31 : inner ℝ (A 3) (A 1)=inner ℝ (A 1) (A 3) := real_inner_comm _ _
  have h32 : inner ℝ (A 3) (A 2)=inner ℝ (A 2) (A 3) := real_inner_comm _ _
  have hrow : ∀j,inner ℝ (∑i,A i) (A j)=S := by
    intro j
    rw [Fin.sum_univ_four]
    fin_cases j
    · change inner ℝ (A 0+A 1+A 2+A 3) (A 0)=S
      simp only [inner_add_left,hii,h10,h20,h30,h21,h31,h32]
      dsimp [S] <;> linarith
    · change inner ℝ (A 0+A 1+A 2+A 3) (A 1)=S
      simp only [inner_add_left,hii,h10,h20,h30,h21,h31,h32]
      dsimp [S] <;> linarith
    · change inner ℝ (A 0+A 1+A 2+A 3) (A 2)=S
      simp only [inner_add_left,hii,h10,h20,h30,h21,h31,h32]
      dsimp [S] <;> linarith
    · change inner ℝ (A 0+A 1+A 2+A 3) (A 3)=S
      simp only [inner_add_left,hii,h10,h20,h30,h21,h31,h32]
      dsimp [S] <;> linarith
  have hS : S=0 := by
    have hh : inner ℝ (∑i,A i) (∑i,w i • A i)=S := by
      simp only [inner_sum,inner_smul_right,hrow]
      rw [←Finset.sum_mul,hw,one_mul]
    rw [hwA,inner_zero_right] at hh
    exact hh.symm
  have hn : inner ℝ (∑i,A i) (∑i,A i)=0 := by
    simp only [inner_sum,hrow,hS,Finset.sum_const_zero]
  exact (inner_self_eq_zero).mp hn

#print axioms disphenoid_sum_zero
end Blueprint.Thomson.Tail.Implementation
