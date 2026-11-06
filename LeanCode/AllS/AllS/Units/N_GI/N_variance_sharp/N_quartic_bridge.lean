import AllS.Units.N_GI.N_variance_sharp.N_sqrt_bridge

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- The actual cubic cross term of the weighted centered-distance expansion. -/
def varianceCubic (q : TangentCoordinates) : ℝ :=
  2*∑ e : ContactIndex,contactWeight e*contactLinearArray q e*contactQuadraticArray q e

/-- The remaining variance tensor input, restricted to the rotation slice.
This is an explicit hypothesis, not an assertion of a checked tensor bound. -/
def VarianceCubicAbsorption : Prop := ∀ q : TangentCoordinates,q∈rotationSlice →
  -(15:ℝ)/4*‖q‖^4≤(∑ e : ContactIndex,contactWeight e*(contactLinearArray q e)^2)-
    (17:ℝ)/5*‖q‖^2+varianceCubic q

theorem variance_centered_square (q : TangentCoordinates) :
    (contactNorm (fun e=>contactLinearArray q e+contactCenter (contactQuadraticArray q) e))^2=
      (∑ e : ContactIndex,contactWeight e*(contactLinearArray q e)^2)+varianceCubic q+
        (contactNorm (contactCenter (contactQuadraticArray q)))^2 := by
  have hzero : (∑ e : ContactIndex,contactWeight e*contactLinearArray q e)=0 :=
    contact_spectrum_stress_zero q
  have hcross : (∑ e : ContactIndex,contactWeight e*(2*contactLinearArray q e*
      contactCenter (contactQuadraticArray q) e))=varianceCubic q := by
    have he (e : ContactIndex) : contactWeight e*(2*contactLinearArray q e*contactCenter (contactQuadraticArray q) e)=
        2*(contactWeight e*contactLinearArray q e*contactQuadraticArray q e)-
        (2*contactMean (contactQuadraticArray q))*(contactWeight e*contactLinearArray q e) := by
      dsimp [contactCenter]
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,hzero,mul_zero,sub_zero]
    rfl
  rw [contactNorm_sq,contactNorm_sq]
  simp_rw [add_sq,mul_add]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hcross]

theorem variance_quartic_lower_of_cubic (hC : VarianceCubicAbsorption) (q : TangentCoordinates)
    (hq : q∈rotationSlice) :
    (17:ℝ)/5*‖q‖^2-(15/4)*‖q‖^4≤
      (contactNorm (fun e=>contactLinearArray q e+contactCenter (contactQuadraticArray q) e))^2 := by
  rw [variance_centered_square]
  have h := hC q hq
  nlinarith [sq_nonneg (contactNorm (contactCenter (contactQuadraticArray q)))]

theorem sharp_variance_of_cubic (hC : VarianceCubicAbsorption) (q : TangentCoordinates)
    (hq : q∈rotationSlice) (hr : ‖q‖≤3/10) :
    ‖q‖*Real.sqrt ((17:ℝ)/5-(15/4)*‖q‖^2)-varianceSigmaH*‖q‖^2≤
      contactNorm (contactCenter (contactDeltaArray q)) :=
  sharp_variance_of_quartic q hr (variance_quartic_lower_of_cubic hC q hq)

#print axioms variance_centered_square
#print axioms sharp_variance_of_cubic
end Blueprint.Thomson.Tail.Implementation
