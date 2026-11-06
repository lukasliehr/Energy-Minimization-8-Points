import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Exact eleven (harmonic degree,pivot row) pairs used by the active registry. -/
def momentPivotKey : Fin 11 → ℕ × ℕ :=
  ![(0,0),(1,3),(2,2),(3,1),(4,0),(5,0),(1,1),(2,0),(6,0),(7,0),(8,0)]

def momentPivotPolynomial (a : ℝ) : Fin 11 → ℝ :=
  ![8,35*a^3-45*a^2+21*a-3,35*a^3-35*a^2+9*a-1,
    35*a^2-30*a+3,35*a^2-30*a+3,5*(a^2+6*a+1),4*(3*a-1),4*(3*a-1),
    (231*a^3-315*a^2+105*a-5)/2,7*(13*a-3)*(a^2+6*a+1)/2,
    (1609*a^4-2996*a^3+1750*a^2-308*a+9)/4]

def MomentPivotContract : Prop := ∀ a : ℝ,physical a → ∀ j : Fin 11,
  momentP (momentPivotKey j).1 (momentPivotKey j).2 a=momentPivotPolynomial a j ∧
    momentP (momentPivotKey j).1 (momentPivotKey j).2 a≠0

theorem momentPivotPolynomial_nonzero (a : ℝ) (ha : physical a) (j : Fin 11) :
    momentPivotPolynomial a j≠0 := by
  have hl : (13/50 : ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3 : ℝ) := ha.2
  have ha0 : 0<a := by linarith
  let t : ℝ := 12*a-3
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  let q : ℝ := (150*a-39)/11
  have hq : 0<q := by dsimp [q];linarith
  have hq1 : 0<1-q := by dsimp [q];linarith
  have h13 : 0<35*a^3-45*a^2+21*a-3 := by
    have he : 35*a^3-45*a^2+21*a-3=
        (829/25000 : ℝ)*(1-q)^3+3*(37/250 : ℝ)*q*(1-q)^2+
          3*(52/225 : ℝ)*q^2*(1-q)+(8/27 : ℝ)*q^3 := by dsimp [q];ring
    rw [he]
    positivity
  have h22 : 35*a^3-35*a^2+9*a-1<0 := by
    have he : -(35*a^3-35*a^2+9*a-1)=
        (25/64 : ℝ)*(1-t)^3+3*(4/9 : ℝ)*t*(1-t)^2+
          3*(14/27 : ℝ)*t^2*(1-t)+(16/27 : ℝ)*t^3 := by dsimp [t];ring
    have hp : 0 < -(35*a^3-35*a^2+9*a-1) := by rw [he];positivity
    linarith
  have h40 : 35*a^2-30*a+3<0 := by
    have he : -(35*a^2-30*a+3)=
        (37/16 : ℝ)*(1-t)^2+2*(17/6 : ℝ)*t*(1-t)+(28/9 : ℝ)*t^2 := by dsimp [t];ring
    have hp : 0 < -(35*a^2-30*a+3) := by rw [he];positivity
    linarith
  have h50 : 0<5*(a^2+6*a+1) := by positivity
  have h20 : 4*(3*a-1)<0 := by linarith
  have h60 : 0<(231*a^3-315*a^2+105*a-5)/2 := by
    have he : (231*a^3-315*a^2+105*a-5)/2=
        (331/128 : ℝ)*(1-t)^3+3*(59/24 : ℝ)*t*(1-t)^2+
          3*(13/6 : ℝ)*t^2*(1-t)+(16/9 : ℝ)*t^3 := by dsimp [t];ring
    rw [he]
    positivity
  have h70 : 0<7*(13*a-3)*(a^2+6*a+1)/2 := by
    have hf : 0<13*a-3 := by linarith
    positivity
  have h80 : 0<(1609*a^4-2996*a^3+1750*a^2-308*a+9)/4 := by
    have he : (1609*a^4-2996*a^3+1750*a^2-308*a+9)/4=
        (217/1024 : ℝ)*(1-t)^4+4*(293/384 : ℝ)*t*(1-t)^3+
          6*(581/432 : ℝ)*t^2*(1-t)^2+4*(103/54 : ℝ)*t^3*(1-t)+
          (196/81 : ℝ)*t^4 := by dsimp [t];ring
    rw [he]
    positivity
  fin_cases j <;> simp only [momentPivotPolynomial,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · norm_num
  · exact ne_of_gt h13
  · exact ne_of_lt h22
  · exact ne_of_lt h40
  · exact ne_of_lt h40
  · exact ne_of_gt h50
  · exact ne_of_lt h20
  · exact ne_of_lt h20
  · exact ne_of_gt h60
  · exact ne_of_gt h70
  · exact ne_of_gt h80

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem momentPivotPolynomial_eq (a : ℝ) (j : Fin 11) :
    momentP (momentPivotKey j).1 (momentPivotKey j).2 a=momentPivotPolynomial a j := by
  have hq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hqn : Real.sqrt (2 : ℝ)≠0 := by positivity
  have h3 := power_even_odd 2 (Real.sqrt 2) hq 3
  have h4 := power_even_odd 2 (Real.sqrt 2) hq 4
  have h5 := power_even_odd 2 (Real.sqrt 2) hq 5
  have h6 := power_even_odd 2 (Real.sqrt 2) hq 6
  have h7 := power_even_odd 2 (Real.sqrt 2) hq 7
  have h8 := power_even_odd 2 (Real.sqrt 2) hq 8
  have h9 := power_even_odd 2 (Real.sqrt 2) hq 9
  have h10 := power_even_odd 2 (Real.sqrt 2) hq 10
  have h11 := power_even_odd 2 (Real.sqrt 2) hq 11
  have h12 := power_even_odd 2 (Real.sqrt 2) hq 12
  have h13 := power_even_odd 2 (Real.sqrt 2) hq 13
  have h14 := power_even_odd 2 (Real.sqrt 2) hq 14
  have h15 := power_even_odd 2 (Real.sqrt 2) hq 15
  have h16 := power_even_odd 2 (Real.sqrt 2) hq 16
  have h17 := power_even_odd 2 (Real.sqrt 2) hq 17
  have h18 := power_even_odd 2 (Real.sqrt 2) hq 18
  have h19 := power_even_odd 2 (Real.sqrt 2) hq 19
  have h20 := power_even_odd 2 (Real.sqrt 2) hq 20
  have h21 := power_even_odd 2 (Real.sqrt 2) hq 21
  have h22 := power_even_odd 2 (Real.sqrt 2) hq 22
  have h23 := power_even_odd 2 (Real.sqrt 2) hq 23
  have h24 := power_even_odd 2 (Real.sqrt 2) hq 24
  have h25 := power_even_odd 2 (Real.sqrt 2) hq 25
  have h26 := power_even_odd 2 (Real.sqrt 2) hq 26
  have h27 := power_even_odd 2 (Real.sqrt 2) hq 27
  have h28 := power_even_odd 2 (Real.sqrt 2) hq 28
  have h29 := power_even_odd 2 (Real.sqrt 2) hq 29
  have h30 := power_even_odd 2 (Real.sqrt 2) hq 30
  have h31 := power_even_odd 2 (Real.sqrt 2) hq 31
  have h32 := power_even_odd 2 (Real.sqrt 2) hq 32
  norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32
  fin_cases j <;> norm_num [momentPivotKey,momentPivotPolynomial,momentP,momentR,
    Finset.sum_filter,Finset.sum_range_succ,Nat.choose,contacts,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals field_simp
  all_goals ring_nf
  all_goals try simp only [hq,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32]
  all_goals ring

theorem moment_kernels_pivot_nonzero : MomentPivotContract := by
  intro a ha j
  exact ⟨momentPivotPolynomial_eq a j, by rw [momentPivotPolynomial_eq];exact momentPivotPolynomial_nonzero a ha j⟩

#check moment_kernels_pivot_nonzero
#print axioms moment_kernels_pivot_nonzero
end Blueprint.Thomson.Finite
