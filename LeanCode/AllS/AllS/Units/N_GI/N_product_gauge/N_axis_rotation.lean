import AllS.Units.N_GI.N_product_gauge.N_compact_action

noncomputable section
open Real SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def axisRotate (k : Fin 3) (t : ℝ) (x : Point) : Point :=
  ![!₂[x 0,cos t*x 1-sin t*x 2,sin t*x 1+cos t*x 2],
    !₂[cos t*x 0+sin t*x 2,x 1,-sin t*x 0+cos t*x 2],
    !₂[cos t*x 0-sin t*x 1,sin t*x 0+cos t*x 1,x 2]] k

def axisRotationLinear (k : Fin 3) (t : ℝ) : Point →ₗ[ℝ] Point where
  toFun := axisRotate k t
  map_add' x y := by ext j; fin_cases k <;> fin_cases j <;> simp [axisRotate] <;> ring
  map_smul' a x := by ext j; fin_cases k <;> fin_cases j <;> simp [axisRotate] <;> ring

theorem axisRotate_norm (k : Fin 3) (t : ℝ) (x : Point) : ‖axisRotate k t x‖=‖x‖ := by
  have h : inner ℝ (axisRotate k t x) (axisRotate k t x)=inner ℝ x x := by
    have ht := sin_sq_add_cos_sq t
    simp only [inner_coordinate_sum]
    fin_cases k <;> simp [axisRotate,Fin.sum_univ_succ]
    · linear_combination (x 1)^2*ht+(x 2)^2*ht
    · linear_combination (x 0)^2*ht+(x 2)^2*ht
    · linear_combination (x 0)^2*ht+(x 1)^2*ht
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (axisRotate k t x),norm_nonneg x]

def axisRotationIsometry (k : Fin 3) (t : ℝ) : Point →ₗᵢ[ℝ] Point where
  toLinearMap := axisRotationLinear k t
  norm_map' := axisRotate_norm k t

def axisRotationOperator (k : Fin 3) (t : ℝ) : Point →L[ℝ] Point :=
  (axisRotationIsometry k t).toContinuousLinearMap

@[simp] theorem axisRotationOperator_apply (k : Fin 3) (t : ℝ) (x : Point) :
    axisRotationOperator k t x=axisRotate k t x := rfl

theorem axisRotationOperator_mem (k : Fin 3) (t : ℝ) : axisRotationOperator k t∈gaugeOrthogonalOperators :=
  axisRotate_norm k t

@[simp] theorem axisRotate_zero (k : Fin 3) (x : Point) : axisRotate k 0 x=x := by
  ext j
  fin_cases k <;> fin_cases j <;> simp [axisRotate]

theorem axisRotate_inner_hasDerivAt (k : Fin 3) (x y : Point) :
    HasDerivAt (fun t : ℝ => inner ℝ x (axisRotate k t y)) (-(crossVec x y) k) 0 := by
  have hc := (hasDerivAt_cos (0:ℝ))
  have hs := (hasDerivAt_sin (0:ℝ))
  simp only [inner_coordinate_sum,Fin.sum_univ_three]
  fin_cases k
  · change HasDerivAt (fun t => x 0*y 0+x 1*(cos t*y 1-sin t*y 2)+x 2*(sin t*y 1+cos t*y 2))
      (-(x 1*y 2-x 2*y 1)) 0
    convert! ((hasDerivAt_const (0:ℝ) (x 0*y 0)).add
      (((hc.mul_const (y 1)).sub (hs.mul_const (y 2))).const_mul (x 1))).add
      (((hs.mul_const (y 1)).add (hc.mul_const (y 2))).const_mul (x 2)) using 1 <;>
      simp [crossVec] <;> (try rfl) <;> (try funext t) <;> ring
  · change HasDerivAt (fun t => x 0*(cos t*y 0+sin t*y 2)+x 1*y 1+x 2*(-sin t*y 0+cos t*y 2))
      (-(x 2*y 0-x 0*y 2)) 0
    convert! ((((hc.mul_const (y 0)).add (hs.mul_const (y 2))).const_mul (x 0)).add
      (hasDerivAt_const (0:ℝ) (x 1*y 1))).add
      ((((hs.neg).mul_const (y 0)).add (hc.mul_const (y 2))).const_mul (x 2)) using 1 <;>
      simp [crossVec] <;> (try rfl) <;> (try funext t) <;> ring
  · change HasDerivAt (fun t => x 0*(cos t*y 0-sin t*y 1)+x 1*(sin t*y 0+cos t*y 1)+x 2*y 2)
      (-(x 0*y 1-x 1*y 0)) 0
    convert! ((((hc.mul_const (y 0)).sub (hs.mul_const (y 1))).const_mul (x 0)).add
      (((hs.mul_const (y 0)).add (hc.mul_const (y 1))).const_mul (x 1))).add
      (hasDerivAt_const (0:ℝ) (x 2*y 2)) using 1 <;>
      simp [crossVec] <;> (try rfl) <;> (try funext t) <;> ring

#print axioms axisRotate_inner_hasDerivAt
end Blueprint.Thomson.Tail.Implementation
