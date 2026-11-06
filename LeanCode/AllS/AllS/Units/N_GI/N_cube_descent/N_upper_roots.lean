import AllS.Units.N_GI.N_cube_descent.N_interior_descent

noncomputable section
open Real Filter Topology
namespace Blueprint.Thomson.Tail.Implementation

def cubeRootSum (c : ℝ) : ℝ := (1-c)/2
def cubeRootProduct (c : ℝ) : ℝ := c^2*(1+c)/(2*(1+2*c))
def cubeRootDiscriminant (c : ℝ) : ℝ := cubeRootSum c^2-4*cubeRootProduct c
def cubeRootPlus (c : ℝ) : ℝ := (cubeRootSum c+√(cubeRootDiscriminant c))/2
def cubeRootMinus (c : ℝ) : ℝ := (cubeRootSum c-√(cubeRootDiscriminant c))/2

theorem cube_discriminant_formula (c : ℝ) (hc : 0<c) :
    cubeRootDiscriminant c=(1-11*c^2-6*c^3)/(4*(1+2*c)) := by
  unfold cubeRootDiscriminant cubeRootSum cubeRootProduct
  have hn : 1+2*c≠0 := by positivity
  field_simp [hn]
  ring

theorem cube_discriminant_positive (c : ℝ) (hc : 0<c) (hcub : c≤7/25) :
    0<cubeRootDiscriminant c := by
  rw [cube_discriminant_formula c hc]
  apply div_pos _ (by positivity)
  have h2 : c^2≤(7/25:ℝ)^2 := by gcongr
  have h3 : c^3≤(7/25:ℝ)^3 := by gcongr
  nlinarith

theorem cube_roots_sum_product (c : ℝ) (hc : 0<c) (hcub : c≤7/25) :
    cubeRootPlus c+cubeRootMinus c=cubeRootSum c ∧
    cubeRootPlus c*cubeRootMinus c=cubeRootProduct c := by
  have hd := Real.sq_sqrt (cube_discriminant_positive c hc hcub).le
  constructor
  · unfold cubeRootPlus cubeRootMinus;ring
  · unfold cubeRootPlus cubeRootMinus
    change (√(cubeRootDiscriminant c))^2=(cubeRootSum c)^2-4*cubeRootProduct c at hd
    nlinarith

theorem cube_roots_positive (c : ℝ) (hc : 0<c) (hcub : c≤7/25) :
    0<cubeRootMinus c ∧ cubeRootMinus c<cubeRootPlus c := by
  have hD := cube_discriminant_positive c hc hcub
  have hs : 0<cubeRootSum c := by unfold cubeRootSum;linarith
  have hp : 0<cubeRootProduct c := by unfold cubeRootProduct;positivity
  have hsq := Real.sq_sqrt hD.le
  have hrootpos := Real.sqrt_pos.mpr hD
  have hrootlt : √(cubeRootDiscriminant c)<cubeRootSum c := by
    change (√(cubeRootDiscriminant c))^2=(cubeRootSum c)^2-4*cubeRootProduct c at hsq
    nlinarith
  unfold cubeRootMinus cubeRootPlus
  constructor <;> linarith

theorem cube_upper_sum_product (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q)
    (hc1 : c<1) (h0 : q 0=cubeUpper c) :
    q 1+q 2=cubeRootSum c ∧ q 1*q 2=cubeRootProduct c := by
  have hs := h.2.2.1
  rw [Fin.sum_univ_three,h0] at hs
  have hs2 : 2*(q 1+q 2)=1-c := by unfold cubeUpper at hs;linarith
  have hr := h.2.2.2
  rw [Fin.sum_univ_three] at hr
  have hn0 := (h.2.1 0).ne'
  have hn1 := (h.2.1 1).ne'
  have hn2 := (h.2.1 2).ne'
  have hrpoly : c^2*(q 1*q 2+q 0*q 2+q 0*q 1)=q 0*q 1*q 2 := by
    field_simp [hn0,hn1,hn2] at hr
    nlinarith
  rw [h0] at hrpoly
  unfold cubeUpper at hrpoly
  have hh : c^2*(2*(q 1*q 2)+(1+c)*(q 1+q 2))=(1+c)*(q 1*q 2) := by nlinarith [hrpoly]
  have hf : (1-c)*(2*(1+2*c)*(q 1*q 2)-c^2*(1+c))=0 := by
    linear_combination -2*hh+c^2*(1+c)*hs2
  have hf' := (mul_eq_zero.mp hf).resolve_left (sub_pos.mpr hc1).ne'
  refine ⟨by unfold cubeRootSum;linarith,?_⟩
  unfold cubeRootProduct
  have hn : 2*(1+2*c)≠0 := by have hc:=h.1;positivity
  apply (eq_div_iff hn).mpr
  nlinarith

theorem cube_roots_recover (c x y : ℝ) (hc : 0<c) (hcub : c≤7/25)
    (hs : x+y=cubeRootSum c) (hp : x*y=cubeRootProduct c) (hxy : y≤x) :
    x=cubeRootPlus c ∧ y=cubeRootMinus c := by
  have hD : cubeRootDiscriminant c=(x-y)^2 := by unfold cubeRootDiscriminant;rw [←hs,←hp];ring
  have hsqrt : √(cubeRootDiscriminant c)=x-y := by rw [hD,Real.sqrt_sq (sub_nonneg.mpr hxy)]
  unfold cubeRootPlus cubeRootMinus
  rw [hsqrt]
  constructor <;> linarith

#print axioms cube_upper_sum_product
end Blueprint.Thomson.Tail.Implementation
