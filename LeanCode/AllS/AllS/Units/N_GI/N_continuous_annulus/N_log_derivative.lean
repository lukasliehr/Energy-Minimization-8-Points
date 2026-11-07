import AllS.Units.N_GI.N_weighted_monotonicity.N_variance_derivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def massOneBeta (W : ℝ) : ℝ := twoValueA W 1+twoValueB W 1

theorem massOne_parameters (W : ℝ) (hW : 1<W) :
    0 < twoValueA W 1 ∧ 0 < massOneBeta W ∧
    twoValueA W 1=(W-1)*twoValueB W 1 ∧
    twoValueA W 1*massOneBeta W=1 ∧ massOneBeta W=W*twoValueB W 1 := by
  obtain ⟨hA,hB,hbal,h1,h2,hC⟩ := twoValue_coefficients W 1 (by norm_num) hW
  simp only [one_mul,mul_one] at hbal h1
  refine ⟨hA,by dsimp [massOneBeta]; linarith,hbal,h1,?_⟩
  dsimp [massOneBeta]
  linarith

theorem massOne_exp_factor (W v : ℝ) :
    twoValueExp W v 1=exp (-v*twoValueA W 1)*(1+(W-1)*exp (massOneBeta W*v)) := by
  have he : exp (-v*twoValueA W 1)*exp (massOneBeta W*v)=exp (v*twoValueB W 1) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [massOneBeta]
    ring
  change 1*exp (-v*twoValueA W 1)+(W-1)*exp (v*twoValueB W 1)=_
  rw [one_mul]
  rw [mul_add,mul_one]
  rw [show exp (-v*twoValueA W 1)*((W-1)*exp (massOneBeta W*v))=
    (W-1)*(exp (-v*twoValueA W 1)*exp (massOneBeta W*v)) by ring,he]

theorem massOne_log_hasDerivAt (W v : ℝ) (hW : 1<W) (hv : 0<v) :
    HasDerivAt (fun t=>log (twoValueExp W t 1))
      (twoValueA W 1*(exp (massOneBeta W*v)-1)/(1+(W-1)*exp (massOneBeta W*v))) v := by
  obtain ⟨hA,hb,hbal,hAb,hbW⟩ := massOne_parameters W hW
  have hden : 0<1+(W-1)*exp (massOneBeta W*v) := by positivity
  have hf : 0<twoValueExp W v 1 := by rw [massOne_exp_factor]; positivity
  have hd := (weighted_monotonicity_variance_derivative W v 1 hv (by norm_num) hW).1
  have hc := (twoValue_coefficients W 1 (by norm_num) hW).2.2.2.2.2
  simp only [one_mul] at hc
  have hsplit : exp (v*twoValueB W 1)=exp (-v*twoValueA W 1)*exp (massOneBeta W*v) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [massOneBeta]
    ring
  convert! hd.log hf.ne' using 1
  dsimp [twoValueVarianceDeriv]
  simp only [one_mul]
  rw [←hc,hsplit,massOne_exp_factor]
  field_simp
  <;> ring

theorem massOne_log_derivative_lower (W v : ℝ) (hW : 1<W) (hv : 0<v) :
    v/(W*(1+massOneBeta W*v))≤
      twoValueA W 1*(exp (massOneBeta W*v)-1)/(1+(W-1)*exp (massOneBeta W*v)) := by
  obtain ⟨hA,hb,hbal,hAb,hbW⟩ := massOne_parameters W hW
  have hden : 0<1+(W-1)*exp (massOneBeta W*v) := by positivity
  have hden2 : 0<W*(1+massOneBeta W*v) := by positivity
  apply (div_le_div_iff₀ hden2 hden).mpr
  have he : 0≤exp (massOneBeta W*v)-1-massOneBeta W*v := by
    linarith [Real.add_one_le_exp (massOneBeta W*v)]
  have hh := mul_nonneg (show 0≤W*twoValueA W 1+v by positivity) he
  have hsq : 0 ≤ massOneBeta W*v^2 := by positivity
  have hid : twoValueA W 1*(exp (massOneBeta W*v)-1)*(W*(1+massOneBeta W*v))-
      v*(1+(W-1)*exp (massOneBeta W*v))=
      (W*twoValueA W 1+v)*(exp (massOneBeta W*v)-1-massOneBeta W*v)+massOneBeta W*v^2 := by
    linear_combination W*v*exp (massOneBeta W*v)*hAb
  linarith

#print axioms massOne_log_hasDerivAt
#print axioms massOne_log_derivative_lower
end Blueprint.Thomson.Tail.Implementation
