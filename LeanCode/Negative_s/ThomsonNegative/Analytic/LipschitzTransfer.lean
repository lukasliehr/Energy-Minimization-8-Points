import ThomsonNegative.Analytic.ScalarReduction

/-! Cache scalar models at a proposed height, then transfer them to the exact
root using the already proved residual bound. No second series evaluation is
needed when these analytic error inflations are used. -/

noncomputable section
open Real
namespace ThomsonNegative

lemma auxSlope_bounds (q x : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1)
    (hx : x ∈ Set.Icc (0:ℝ) (2/3)) : 0 ≤ auxSlope q x ∧ auxSlope q x ≤ 2 := by
  have ht := auxSlope_tail q x hq ⟨hx.1,by linarith [hx.2]⟩ 0
  norm_num [slopePartial] at ht
  refine ⟨ht.1,ht.2.trans ?_⟩
  apply (div_le_iff₀ (by linarith [hx.2] : 0 < 1-x)).mpr
  linarith [hx.2]

theorem auxSlope_lipschitz (q x y : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1)
    (hx : x ∈ Set.Icc (0:ℝ) (2/3)) (hy : y ∈ Set.Icc (0:ℝ) (2/3)) :
    |auxSlope q x-auxSlope q y| ≤ 9*|x-y| := by
  have hd (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) (2/3)) :
      HasDerivWithinAt (auxSlope q) ((1-z)^(-q-1)) (Set.Icc (0:ℝ) (2/3)) z :=
    (auxSlope_hasDerivAt q z hq.1.ne' (by linarith [hz.2])).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) (2/3)) : ‖(1-z)^(-q-1)‖ ≤ 9 := by
    have h := aux_curvature_bounds q z ⟨hq.1.le,hq.2⟩ hz
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact h.2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc (0:ℝ) (2/3)) hy hx
  simpa only [Real.norm_eq_abs] using h

theorem normalizedAux_lipschitz (q x y : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hx : x ∈ Set.Icc (0:ℝ) (2/3)) (hy : y ∈ Set.Icc (0:ℝ) (2/3)) :
    |normalizedAux q x-normalizedAux q y| ≤ 2*|x-y| := by
  have hd (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) (2/3)) :
      HasDerivWithinAt (normalizedAux q) (auxSlope q z) (Set.Icc (0:ℝ) (2/3)) z :=
    (normalizedAux_hasDerivAt q z hq (by linarith [hz.2])).hasDerivWithinAt
  have hb (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) (2/3)) : ‖auxSlope q z‖ ≤ 2 := by
    have h := auxSlope_bounds q z ⟨hq.1,hq.2.le⟩ hz
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc (0:ℝ) (2/3)) hy hx
  simpa only [Real.norm_eq_abs] using h

lemma affine_argument_lipschitz (m c a b : ℝ) (hm : |m| ≤ 1) :
    |(m*a+c)-(m*b+c)| ≤ |a-b| := by
  rw [show (m*a+c)-(m*b+c)=m*(a-b) by ring,abs_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (abs_nonneg (a-b))

/-- Every contact argument changes by at most the change in squared height. -/
theorem contact_argument_lipschitz (a b : ℝ) :
    |(1+a)/2-(1+b)/2| ≤ |a-b| ∧
    |a-b| ≤ |a-b| ∧
    |(1-a)*(2+√2)/4-(1-b)*(2+√2)/4| ≤ |a-b| ∧
    |(1-a)*(2-√2)/4-(1-b)*(2-√2)/4| ≤ |a-b| := by
  have hr := sqrt_two_pos
  have hr2 := sqrt_two_lt_two
  have hA := affine_argument_lipschitz (1/2) (1/2) a b (by norm_num)
  have hCp : |-(2+√(2:ℝ))/4| ≤ 1 := by
    rw [abs_div,abs_neg,abs_of_pos (by positivity),abs_of_pos (by norm_num)]
    linarith
  have hDp : |-(2-√(2:ℝ))/4| ≤ 1 := by
    rw [abs_div,abs_neg,abs_of_pos (by linarith),abs_of_pos (by norm_num)]
    linarith
  have hC := affine_argument_lipschitz (-(2+√2)/4) ((2+√2)/4) a b hCp
  have hD := affine_argument_lipschitz (-(2-√2)/4) ((2-√2)/4) a b hDp
  refine ⟨?_,le_rfl,?_,?_⟩
  · convert! hA using 1 <;> congr 1 <;> ring
  · convert! hC using 1 <;> congr 1 <;> ring
  · convert! hD using 1 <;> congr 1 <;> ring

/-- Generic cached-model transfer. If the argument moves by at most ε,
only 2ε and 9ε need to be added to the value and x-slope remainders. -/
theorem cached_auxiliary_transfer (q x y value slope valueError slopeError ε : ℝ)
    (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hx : x ∈ Set.Icc (0:ℝ) (2/3)) (hy : y ∈ Set.Icc (0:ℝ) (2/3))
    (hxy : |x-y| ≤ ε)
    (hv : |normalizedAux q x-value| ≤ valueError)
    (hs : |auxSlope q x-slope| ≤ slopeError) :
    |normalizedAux q y-value| ≤ valueError+2*ε ∧
    |auxSlope q y-slope| ≤ slopeError+9*ε := by
  have hA := normalizedAux_lipschitz q y x hq hy hx
  have hS := auxSlope_lipschitz q y x ⟨hq.1,hq.2.le⟩ hy hx
  rw [abs_sub_comm y x] at hA hS
  have hAt := abs_sub_le (normalizedAux q y) (normalizedAux q x) value
  have hSt := abs_sub_le (auxSlope q y) (auxSlope q x) slope
  constructor <;> linarith

#print axioms auxSlope_lipschitz
#print axioms normalizedAux_lipschitz
#print axioms contact_argument_lipschitz
#print axioms cached_auxiliary_transfer
end ThomsonNegative
