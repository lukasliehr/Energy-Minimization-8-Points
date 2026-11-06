import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootQuotientGates
import AllS.Units.N_AI.N_scalar_models.AffineModelSupport
import AllS.Units.N_AI.N_scalar_models.ResidualQuotientSupport
import AllS.Units.N_AI.N_root_models.N_proposal_domain
import AllS.Units.N_AI.N_root_models.finite_d14_c23_RootTranscendental_000

set_option maxHeartbeats 0
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.CAP.Instances.finite_d14_c23_RootQuotient
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootProduct_000 (left right result tail gate)
open Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootRecurrence_000 (input)
open Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootQuotientGates
open Blueprint.CAP.ArithmeticPilot.RootControlsAll_finite_d14_c23 (z)

def numerator : ℝ → ℝ := scalarEval (dyadicRootCoefficients z)
def denominator (x : ℝ) : ℝ := (q0:ℝ)+(q1:ℝ)*x
def Statement : Prop := input.asTM.Valid (fun x => numerator x/denominator x)

theorem sound : Statement := by
  rcases gates with ⟨hQ,hPwf,hPe,hNeg,hAdd,hCoeff,hμ,hq1,herror⟩
  have hQvalid := left.affine_gate_valid q0 q1 hQ
  have hPvalid := right.midpoint_polynomial_valid hPwf hPe
  have hYvalid := productGateSupport left right result denominator
    (scalarEval right.midpointCoefficients) tail hQvalid hPvalid gate
  have hNegValid := QModel.neg_gate_valid result negativeProduct _ hYvalid hNeg
  have hVvalid : V.asTM.Valid numerator := by
    have heq : (fun k : Fin 29 => (((z k:ℚ)/2^256 : ℚ):ℝ)) =
        dyadicRootCoefficients z := by
      funext k
      simp only [dyadicRootCoefficients, Rat.cast_div, Rat.cast_pow,
        Rat.cast_intCast, Rat.cast_ofNat]
    have h := QModel.point_polynomial_valid (fun k => (z k:ℚ)/2^256)
    rw [heq] at h
    exact h
  have hJvalid : residual.asTM.Valid
      (fun x => numerator x-denominator x*scalarEval right.midpointCoefficients x) := by
    simpa only [sub_eq_add_neg] using
      QModel.add_gate_valid V negativeProduct residual _ _ hVvalid hNegValid hAdd
  have hc : input.asTM.CoeffContains right.midpointCoefficients := by
    intro k
    change ((input.coeff k).lo:ℝ) ≤ ((right.coeff k).mid:ℝ) ∧
      ((right.coeff k).mid:ℝ) ≤ ((input.coeff k).hi:ℝ)
    constructor
    · exact_mod_cast (hCoeff k).1
    · exact_mod_cast (hCoeff k).2
  have hsep : ∀ x ∈ cellDomain, (qmin:ℝ) ≤ |denominator x| := by
    intro x hx
    have hq1R : (0:ℝ) ≤ q1 := by exact_mod_cast hq1
    have hxlo : -1 ≤ x := hx.1
    have hmul := mul_le_mul_of_nonneg_left hxlo hq1R
    have hlow : (qmin:ℝ) ≤ denominator x := by
      simp only [qmin, Rat.cast_sub, denominator]
      linarith
    exact hlow.trans (le_abs_self _)
  exact residualQuotientSupport input residual numerator denominator
    right.midpointCoefficients qmin hμ hsep hc hJvalid herror

theorem exponential_valid :
    ArithmeticPilot.finite_d14_c23_RootRecurrence_000.result.asTM.Valid
      (fun x => Real.exp (numerator x/denominator x)) :=
  finite_d14_c23_RootTranscendental_000.sound _ sound

#print Statement
#print axioms sound
#print axioms exponential_valid
end Blueprint.CAP.Instances.finite_d14_c23_RootQuotient
