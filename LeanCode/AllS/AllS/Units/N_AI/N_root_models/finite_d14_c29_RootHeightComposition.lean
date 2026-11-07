import AllS.Units.N_AI.N_root_models.finite_d14_c29_RootImage

set_option maxHeartbeats 0
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.CAP.Instances.finite_d14_c29_RootHeightComposition
open Blueprint.CAP Blueprint.Thomson.Finite
open Blueprint.CAP.ArithmeticPilot.finite_d14_c29_RootCompositionGates
open Blueprint.CAP.Instances.finite_d14_c29_RootConstants
open Blueprint.CAP.Instances.finite_d14_c29_RootQuotient (numerator denominator)

def heightNum (x : ℝ) := 2*Real.exp (numerator x/denominator x)-2+Real.sqrt 2
def heightDen (x : ℝ) := 2*Real.exp (numerator x/denominator x)+2+Real.sqrt 2
def Statement : Prop := heightComposition.asTM.Valid
  (fun x => rootHeight (denominator x) (numerator x))

theorem twice_valid : twiceU.asTM.Valid (fun x => 2*Real.exp (numerator x/denominator x)) := by
  have h := productGateSupport U twoM twiceU _ _
    ArithmeticPilot.finite_d14_c29_RootProduct_004.tail finite_d14_c29_RootImage.U_valid two_valid
    ArithmeticPilot.finite_d14_c29_RootProduct_004.gate
  simpa only [mul_comm] using h

theorem numerator_valid : heightNumerator.asTM.Valid heightNum := by
  change heightNumerator.asTM.Valid (fun x => 2*Real.exp (numerator x/denominator x)-2+Real.sqrt 2)
  have h := QModel.add_gate_valid twiceU minusTwoM twiceUMinusTwo _ _
    twice_valid minusTwo_valid twiceUMinusTwo_add
  simpa only [heightNum,sub_eq_add_neg] using
    QModel.add_gate_valid twiceUMinusTwo rhoM heightNumerator _ _ h rho_valid heightNumerator_add

theorem denominator_valid : heightDenominator.asTM.Valid heightDen := by
  have h := QModel.add_gate_valid twiceU twoM twiceUPlusTwo _ _
    twice_valid two_valid twiceUPlusTwo_add
  exact QModel.add_gate_valid twiceUPlusTwo rhoM heightDenominator _ _ h rho_valid heightDenominator_add

theorem inverse_valid : heightInverse.asTM.Valid (fun x => 1/heightDen x) := by
  have hP := inverseProposal.midpoint_polynomial_valid inverse_wf.1 inverse_wf.2
  have hprod := productGateSupport heightDenominator inverseProposal inverseProduct _ _
    ArithmeticPilot.finite_d14_c29_RootProduct_006.tail denominator_valid hP
    ArithmeticPilot.finite_d14_c29_RootProduct_006.gate
  have hn := QModel.neg_gate_valid inverseProduct minusInverseProduct _ hprod minusInverseProduct_neg
  have hJ : inverseResidual.asTM.Valid
      (fun x => 1-heightDen x*scalarEval inverseProposal.midpointCoefficients x) := by
    simpa only [sub_eq_add_neg] using
      QModel.add_gate_valid oneM minusInverseProduct inverseResidual _ _ one_valid hn inverseResidual_add
  have hc : heightInverse.asTM.CoeffContains inverseProposal.midpointCoefficients := by
    intro k
    change ((heightInverse.coeff k).lo:ℝ) ≤ ((inverseProposal.coeff k).mid:ℝ) ∧
      ((inverseProposal.coeff k).mid:ℝ) ≤ ((heightInverse.coeff k).hi:ℝ)
    constructor
    · exact_mod_cast (inverse_coeff k).1
    · exact_mod_cast (inverse_coeff k).2
  have hsep : ∀ x ∈ cellDomain, (heightDenominator.hull.lo:ℝ) ≤ |heightDen x| := by
    intro x hx
    obtain ⟨he,a,ha,hra⟩ := denominator_valid
    have hH := heightDenominator.hull_positive he inverse_error.1
    have hi := hH.2.2 a ha x hx (heightDen x-scalarEval a x) (hra x hx)
    have hf : heightDenominator.hull.asBox.Contains (heightDen x) := by
      convert hi using 1 <;> ring
    exact hf.1.trans (le_abs_self _)
  exact residualQuotientSupport heightInverse inverseResidual (fun _ => 1) heightDen
    inverseProposal.midpointCoefficients heightDenominator.hull.lo inverse_error.1 hsep hc hJ inverse_error.2

theorem sound : Statement := by
  unfold Statement
  have h := productGateSupport heightNumerator heightInverse heightComposition _ _
    ArithmeticPilot.finite_d14_c29_RootProduct_007.tail numerator_valid inverse_valid
    ArithmeticPilot.finite_d14_c29_RootProduct_007.gate
  simpa only [rootHeight,heightNum,heightDen,one_div,div_eq_mul_inv,one_mul] using h

#print Statement
#print axioms sound
#print axioms inverse_valid
end Blueprint.CAP.Instances.finite_d14_c29_RootHeightComposition
