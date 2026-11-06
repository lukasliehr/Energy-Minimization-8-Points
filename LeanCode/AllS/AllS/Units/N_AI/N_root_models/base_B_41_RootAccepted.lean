import AllS.Units.N_AI.N_root_models.base_B_41_RootHeightComposition
import AllS.Units.N_AI.N_root_models.N_height_enclosure
import AllS.Units.N_AI.N_root_models.RootControlSupport
import AllS.Units.N_AI.N_root_models.RootInvariantInstance

set_option maxHeartbeats 0
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.CAP.Instances.base_B_41_RootAccepted
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open Blueprint.CAP.ArithmeticPilot.base_B_41_RootCompositionGates
open Blueprint.CAP.ArithmeticPilot.RootControlsAll_base_B_41 (center halfwidth z invariantUpper)
open Blueprint.CAP.Instances.base_B_41_RootQuotient (numerator denominator)

def exponent (x : ℝ) := (center:ℝ)+(halfwidth:ℝ)*x
def Statement : Prop := heightFinal.asTM.Valid (fun x => aS (exponent x)) ∧
  heightFinal.asTM.CommonPositiveHull heightFinal.hull.asBox (13/50) ∧
  ∀ x ∈ cellDomain, aS (exponent x) ∈ Set.Ioo (13/50:ℝ) (1/3)

theorem denominator_eq (x : ℝ) : denominator x = 1+exponent x/2 := by
  simp only [denominator,exponent,ArithmeticPilot.base_B_41_RootQuotientGates.q0,
    ArithmeticPilot.base_B_41_RootQuotientGates.q1,Rat.cast_add,Rat.cast_one,
    Rat.cast_div,Rat.cast_ofNat]
  ring

theorem domain (x : ℝ) (hx : x ∈ cellDomain) :
    0 ≤ exponent x ∧ (qmin:ℝ) ≤ 1+exponent x/2 ∧
    numerator x ∈ Set.Icc 0 rootC ∧
    |numerator x-rootT (1+exponent x/2) (numerator x)| ≤ (delta:ℝ) := by
  have hpar := ArithmeticPilot.RootControlsAll_base_B_41.parameter_gates
  have hh : (0:ℝ) < halfwidth := by exact_mod_cast hpar.1
  have hc : (0:ℝ) ≤ (center:ℝ)-(halfwidth:ℝ) := by exact_mod_cast hpar.2.1
  have hcontrols : ∀ i, 0 ≤ bernsteinControls (dyadicRootCoefficients z) i ∧
      bernsteinControls (dyadicRootCoefficients z) i ≤ (invariantUpper:ℝ) := by
    intro i
    rw [rootControlSupport z i]
    exact_mod_cast ArithmeticPilot.RootControlsAll_base_B_41.control_gates i
  have hp := root_models_proposal_domain z (center:ℝ) (halfwidth:ℝ) invariantUpper hh hc
    rootInvariantInstance hcontrols x hx
  have hs : 0 ≤ exponent x := by
    have hm := mul_le_mul_of_nonneg_left hx.1 hh.le
    dsimp [exponent]
    linarith
  have hq : (qmin:ℝ) = 1+((center:ℝ)-(halfwidth:ℝ))/2 := by
    simp only [qmin,Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  refine ⟨hs,?_,hp.2.2,?_⟩
  · rw [hq]
    exact hp.2.1
  · rw [←denominator_eq]
    exact base_B_41_RootImage.defect_bound x hx

theorem sound : Statement := by
  have hM : heightComposition.asTM.Valid
      (fun x => rootHeight (1+exponent x/2) (numerator x)) := by
    simpa only [base_B_41_RootHeightComposition.Statement,denominator_eq] using
      base_B_41_RootHeightComposition.sound
  have hq : (1:ℝ) ≤ qmin := by norm_num [qmin,center,halfwidth]
  have hmq : ((6 : ℕ) : ℝ) ≤ qmin := by norm_num [qmin,center,halfwidth]
  have hlambda : (lambda:ℝ) = rootLambda 6 := by norm_num [lambda,rootLambda]
  have hc : heightFinal.asTM.coeff = heightComposition.asTM.coeff := by
    funext k
    exact congrArg QInterval.asBox (height_widen.1 k)
  have he : (heightComposition.error:ℝ)+5*(delta:ℝ)/(17*(qmin:ℝ)*(1-rootLambda 6)) ≤
      (heightFinal.error:ℝ) := by
    rw [←hlambda]
    exact_mod_cast height_widen.2
  exact root_models_height_enclosure heightComposition.asTM heightFinal.asTM exponent numerator
    qmin delta 6 heightFinal.hull.asBox hM hq (by norm_num)
    hmq (by exact_mod_cast defect_nonneg) domain hc he
    ⟨le_rfl,le_rfl⟩ height_range.1 height_range.2

#print Statement
#print axioms sound
end Blueprint.CAP.Instances.base_B_41_RootAccepted
