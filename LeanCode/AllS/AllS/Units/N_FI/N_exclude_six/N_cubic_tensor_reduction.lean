import AllS.Units.N_FI.N_exclude_six.N_linear_tensor_reduction

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem sixSecond_square_gap (a : ℝ) (ha1 : a < 1) :
    (sixSecond a 2)^2-(sixSecond a 0)^2=√2*a := by
  have hs := Real.sq_sqrt (show 0 ≤ 1-a by linarith)
  have hn : 1-a ≠ 0 := by linarith
  have hs2 : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn2 : √(2:ℝ) ≠ 0 := by positivity
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  calc
    _ = ((contacts a 0-contacts a 3)^2-(contacts a 0-contacts a 2)^2)/(4*(1-a)) := by
      change ((contacts a 0-contacts a 3)/(2*√(1-a)))^2-
        ((contacts a 0-contacts a 2)/(2*√(1-a)))^2=_
      rw [div_pow,div_pow,mul_pow,hs]
      ring
    _ = _ := by
      dsimp [contacts]
      simp only [div_eq_mul_inv,hinv]
      field_simp
      ring

theorem exclude_six_cubic_tensor_reduction (a : ℝ) (ha : physical a) (xi : Fin 6 → ℝ)
    (hnorm : SixTypeNorms a xi)
    (h01 : (xi 0)^2=(xi 1)^2) (h23 : (xi 2)^2=(xi 3)^2) (h45 : (xi 4)^2=(xi 5)^2)
    (hlin3 : xi 4+xi 5=0) (hlin12 : (xi 0+xi 1)+(xi 2+xi 3)=0)
    (hcube : (∑ k, (xi k)^3)=0) :
    xi 0+xi 1=0 ∧ xi 2+xi 3=0 ∧ xi 4+xi 5=0 := by
  have ha0 : 0 < a := by have hb := packing_endpoint_bounds.1; linarith [ha.1]
  have hrpos : 0 < √2*a := mul_pos (by positivity) ha0
  have hr : (xi 0)^2-(xi 2)^2=√2*a := by
    have hn0 := hnorm 0
    have hn2 := hnorm 2
    change (sixFirst a 0)^2+_+_=1 at hn0
    change (sixFirst a 2)^2+_+_=1 at hn2
    rw [sixFirst_entries a ha0] at hn0 hn2
    change (bpairP a)^2+(sixSecond a 0)^2+(xi 0)^2=1 at hn0
    change (-bpairP a)^2+(sixSecond a 2)^2+(xi 2)^2=1 at hn2
    have hg := sixSecond_square_gap a (by linarith [ha.2])
    nlinarith
  have hw : (xi 0)^2*(xi 0+xi 1)+(xi 2)^2*(xi 2+xi 3)+(xi 4)^2*(xi 4+xi 5)=0 := by
    rw [Fin.sum_univ_six] at hcube
    linear_combination hcube+xi 1*h01+xi 3*h23+xi 5*h45
  rw [hlin3,mul_zero,add_zero] at hw
  have hprod : ((xi 0)^2-(xi 2)^2)*(xi 0+xi 1)=0 := by
    linear_combination hw-(xi 2)^2*hlin12
  have hz : xi 0+xi 1=0 := (mul_eq_zero.mp hprod).resolve_left (by rw [hr]; exact hrpos.ne')
  exact ⟨hz,by linarith,hlin3⟩

#check exclude_six_cubic_tensor_reduction
#print axioms exclude_six_cubic_tensor_reduction
end Blueprint.Thomson.Finite
