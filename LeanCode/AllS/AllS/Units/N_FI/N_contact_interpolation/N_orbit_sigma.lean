import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_sympoly

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def contactSigma (a : ℝ) (r : Fin 5) : ℝ :=
  ∑ j : Fin 3, contacts a (contactRepresentative r j)

def sigmaOrbitOrder : Fin 5 → Fin 5 := ![2,4,3,0,1]

def OrbitSigmaContract : Prop := ∀ a : ℝ, physical a →
  contactSigma a = ![4*a-1,-a+Real.sqrt 2*(1-a),-a-Real.sqrt 2*(1-a),-a,-1] ∧
  StrictMono (contactSigma a ∘ sigmaOrbitOrder)

theorem sigmaOrbitOrder_bijective : Function.Bijective sigmaOrbitOrder := by decide

theorem contactSigma_values (a : ℝ) :
    contactSigma a = ![4*a-1,-a+Real.sqrt 2*(1-a),-a-Real.sqrt 2*(1-a),-a,-1] := by
  have hq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hqn : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hinv : (Real.sqrt (2 : ℝ))⁻¹ = Real.sqrt 2/2 := by
    field_simp
    nlinarith
  funext r
  fin_cases r <;>
    norm_num [contactSigma,contactRepresentative,contacts,Fin.sum_univ_succ,div_eq_mul_inv,hinv]
  all_goals try dsimp
  all_goals ring

theorem contact_interpolation_orbit_sigma : OrbitSigmaContract := by
  intro a ha
  refine ⟨contactSigma_values a, ?_⟩
  obtain ⟨hl,hu⟩ := ha
  have hb := packing_endpoint_bounds.1
  have hq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hqn := Real.sqrt_nonneg (2 : ℝ)
  have hq1 : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hleft := mul_pos (show 0 < 1-a by linarith) (sub_pos.mpr hq1)
  have hright := mul_pos (show 0 < (1/3 : ℝ)-a by linarith)
    (show 0 < 5+Real.sqrt (2 : ℝ) by positivity)
  have h₀ : -a-Real.sqrt 2*(1-a) < -1 := by nlinarith
  have h₁ : (-1 : ℝ) < -a := by linarith
  have h₂ : -a < 4*a-1 := by linarith
  have h₃ : 4*a-1 < -a+Real.sqrt 2*(1-a) := by nlinarith
  rw [contactSigma_values]
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [sigmaOrbitOrder,Function.comp_def] at *
  all_goals try dsimp
  all_goals linarith

theorem contactSigma_injective (a : ℝ) (ha : physical a) : Function.Injective (contactSigma a) := by
  intro i j hij
  obtain ⟨i',rfl⟩ := sigmaOrbitOrder_bijective.2 i
  obtain ⟨j',rfl⟩ := sigmaOrbitOrder_bijective.2 j
  have he : i' = j' := (contact_interpolation_orbit_sigma a ha).2.injective hij
  rw [he]

#check contact_interpolation_orbit_sigma
#print axioms contact_interpolation_orbit_sigma
#check OrbitSigmaContract
#print axioms OrbitSigmaContract
end Blueprint.Thomson.Finite
