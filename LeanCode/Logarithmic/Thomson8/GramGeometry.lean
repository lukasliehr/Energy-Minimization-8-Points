import Thomson8.GramAlgebra
import Thomson8.GeometryBasics
import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace Thomson8

open scoped InnerProductSpace

theorem gram_three_det (p q r : Point) (hp : ‖p‖=1) (hq : ‖q‖=1) (hr : ‖r‖=1) :
    (Matrix.gram ℝ ![p,q,r]).det = gramDet3 ⟪p,q⟫_ℝ ⟪p,r⟫_ℝ ⟪q,r⟫_ℝ := by
  simp [Matrix.det_fin_three,Matrix.gram,gramDet3,real_inner_self_eq_norm_sq,hp,hq,hr,
    real_inner_comm]
  ring

theorem gram_four_det_zero (v : Fin 4 → Point) : (Matrix.gram ℝ v).det=0 := by
  by_contra h
  have hc := (Matrix.linearIndependent_of_det_gram_ne_zero h).fintype_card_le_finrank
  norm_num [Point] at hc

theorem gram_four_formula (p q r s : Point) (hp : ‖p‖=1) (hq : ‖q‖=1)
    (hr : ‖r‖=1) (hs : ‖s‖=1) :
    (Matrix.gram ℝ ![p,q,r,s]).det =
      -gramResidual ⟪p,q⟫_ℝ ⟪p,r⟫_ℝ ⟪q,r⟫_ℝ ⟪p,s⟫_ℝ ⟪q,s⟫_ℝ ⟪r,s⟫_ℝ := by
  have hm0 : (Matrix.gram ℝ ![p,q,r,s]).submatrix Fin.succ (0 : Fin 4).succAbove = !![⟪q,q⟫_ℝ, ⟪q,r⟫_ℝ, ⟪q,s⟫_ℝ; ⟪r,q⟫_ℝ, ⟪r,r⟫_ℝ, ⟪r,s⟫_ℝ; ⟪s,q⟫_ℝ, ⟪s,r⟫_ℝ, ⟪s,s⟫_ℝ] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hm1 : (Matrix.gram ℝ ![p,q,r,s]).submatrix Fin.succ (1 : Fin 4).succAbove = !![⟪q,p⟫_ℝ, ⟪q,r⟫_ℝ, ⟪q,s⟫_ℝ; ⟪r,p⟫_ℝ, ⟪r,r⟫_ℝ, ⟪r,s⟫_ℝ; ⟪s,p⟫_ℝ, ⟪s,r⟫_ℝ, ⟪s,s⟫_ℝ] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hm2 : (Matrix.gram ℝ ![p,q,r,s]).submatrix Fin.succ (2 : Fin 4).succAbove = !![⟪q,p⟫_ℝ, ⟪q,q⟫_ℝ, ⟪q,s⟫_ℝ; ⟪r,p⟫_ℝ, ⟪r,q⟫_ℝ, ⟪r,s⟫_ℝ; ⟪s,p⟫_ℝ, ⟪s,q⟫_ℝ, ⟪s,s⟫_ℝ] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hm3 : (Matrix.gram ℝ ![p,q,r,s]).submatrix Fin.succ (3 : Fin 4).succAbove = !![⟪q,p⟫_ℝ, ⟪q,q⟫_ℝ, ⟪q,r⟫_ℝ; ⟪r,p⟫_ℝ, ⟪r,q⟫_ℝ, ⟪r,r⟫_ℝ; ⟪s,p⟫_ℝ, ⟪s,q⟫_ℝ, ⟪s,r⟫_ℝ] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_four]
  rw [hm0, hm1, hm2, hm3]
  have hd (a b c d e f g h i : ℝ) :
      (!![a,b,c;d,e,f;g,h,i]).det = a*e*i-a*f*h-b*d*i+b*f*g+c*d*h-c*e*g := by
    rw [Matrix.det_fin_three]
    rfl
  simp only [hd]
  have h2 : (![p,q,r,s] : Fin 4 → Point) 2=r := rfl
  have h3 : (![p,q,r,s] : Fin 4 → Point) 3=s := rfl
  norm_num [Matrix.det_fin_three,Matrix.gram,h2,h3,real_inner_self_eq_norm_sq,hp,hq,hr,hs,
    gramResidual,gramDet3,real_inner_comm]
  ring

theorem gram_residual_zero (p q r s : Point) (hp : ‖p‖=1) (hq : ‖q‖=1)
    (hr : ‖r‖=1) (hs : ‖s‖=1) :
    gramResidual ⟪p,q⟫_ℝ ⟪p,r⟫_ℝ ⟪q,r⟫_ℝ ⟪p,s⟫_ℝ ⟪q,s⟫_ℝ ⟪r,s⟫_ℝ=0 := by
  have h := gram_four_formula p q r s hp hq hr hs
  rw [gram_four_det_zero] at h
  linarith

#print axioms gram_residual_zero

end Thomson8
