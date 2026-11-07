import AllS.Units.N_AI.N_root_models.base_B_26_RootConstants
import AllS.Units.N_AI.N_root_models.base_B_26_RootQuotient
import AllS.Units.N_AI.N_root_models.base_B_26_RootTranscendental_001
import AllS.Units.N_AI.N_root_models.base_B_26_RootTranscendental_002
import AllS.Units.N_AI.N_root_models.base_B_26_RootTranscendental_003
import AllS.Units.N_AI.N_root_models.base_B_26_RootTranscendental_004

set_option maxHeartbeats 0
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.CAP.Instances.base_B_26_RootImage
open Blueprint.CAP Blueprint.Thomson.Finite
open Blueprint.CAP.ArithmeticPilot.base_B_26_RootCompositionGates
open Blueprint.CAP.Instances.base_B_26_RootConstants
open Blueprint.CAP.Instances.base_B_26_RootQuotient (numerator denominator)

def Statement : Prop := image.asTM.Valid (fun x => rootT (denominator x) (numerator x)) ∧
  defect.asTM.Valid (fun x => numerator x-rootT (denominator x) (numerator x)) ∧
  ∀ x ∈ cellDomain, |numerator x-rootT (denominator x) (numerator x)| ≤ (delta:ℝ)

theorem U_valid : U.asTM.Valid (fun x => Real.exp (numerator x/denominator x)) :=
  base_B_26_RootQuotient.exponential_valid

theorem image_valid : image.asTM.Valid (fun x => rootT (denominator x) (numerator x)) := by
  have hQ : Q.asTM.Valid denominator :=
    QModel.affine_gate_valid Q _ _ ArithmeticPilot.base_B_26_RootQuotientGates.gates.1
  have hm := QModel.neg_gate_valid Q minusQ _ hQ minusQ_neg
  have hp1 := productGateSupport minusQ logtwoM tailExponent _ _
    ArithmeticPilot.base_B_26_RootProduct_001.tail hm logtwo_valid
    ArithmeticPilot.base_B_26_RootProduct_001.gate
  have ht := base_B_26_RootTranscendental_001.sound _ hp1
  have hru := QModel.add_gate_valid rhoM U rhoPlusU _ _ rho_valid U_valid rhoPlusU_add
  have hlru := base_B_26_RootTranscendental_002.sound _ hru
  have hp2 := productGateSupport minusQ logRhoPlusU innerExponent _ _
    ArithmeticPilot.base_B_26_RootProduct_002.tail hm hlru
    ArithmeticPilot.base_B_26_RootProduct_002.gate
  have he := base_B_26_RootTranscendental_003.sound _ hp2
  have hb := productGateSupport innerExp betaM betaExp _ _
    ArithmeticPilot.base_B_26_RootProduct_003.tail he beta_valid
    ArithmeticPilot.base_B_26_RootProduct_003.gate
  have hot := QModel.add_gate_valid oneM tailTwo onePlusTail _ _ one_valid ht onePlusTail_add
  have hnb := QModel.neg_gate_valid betaExp minusBetaExp _ hb minusBetaExp_neg
  have harg := QModel.add_gate_valid onePlusTail minusBetaExp outerLogArg _ _ hot hnb outerLogArg_add
  have hol := base_B_26_RootTranscendental_004.sound _ harg
  have hnol := QModel.neg_gate_valid outerLog minusOuterLog _ hol minusOuterLog_neg
  have hi := QModel.add_gate_valid ceeM minusOuterLog image _ _ cee_valid hnol image_add
  simpa only [rootT, sub_eq_add_neg, mul_comm] using hi

theorem V_valid : V.asTM.Valid numerator := by
  let z := ArithmeticPilot.RootControlsAll_base_B_26.z
  have heq : (fun k : Fin 17 => (((z k:ℚ)/2^256:ℚ):ℝ)) = dyadicRootCoefficients z := by
    funext k
    simp only [dyadicRootCoefficients,Rat.cast_div,Rat.cast_pow,Rat.cast_intCast,Rat.cast_ofNat]
  have h := QModel.point_polynomial_valid (fun k => (z k:ℚ)/2^256)
  rw [heq] at h
  exact h

theorem defect_valid : defect.asTM.Valid
    (fun x => numerator x-rootT (denominator x) (numerator x)) := by
  have hn := QModel.neg_gate_valid image minusImage _ image_valid minusImage_neg
  simpa only [sub_eq_add_neg] using
    QModel.add_gate_valid V minusImage defect _ _ V_valid hn defect_add

theorem defect_bound (x : ℝ) (hx : x ∈ cellDomain) :
    |numerator x-rootT (denominator x) (numerator x)| ≤ (delta:ℝ) :=
  defect.valid_abs_le _ defect_valid x hx

theorem sound : Statement := ⟨image_valid,defect_valid,defect_bound⟩
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.base_B_26_RootImage
