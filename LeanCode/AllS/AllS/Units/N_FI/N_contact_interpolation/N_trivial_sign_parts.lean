import AllS.Units.N_FI.N_contact_interpolation.N_orbit_sigma
import AllS.Units.N_FI.N_contact_interpolation.N_scalar_lagrange

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def polyLift (p : Polynomial ℝ) (q : Poly3) : Poly3 := p.eval₂ MvPolynomial.C q

def deltaPoly : Poly3 :=
  (MvPolynomial.X 0-MvPolynomial.X 1)*(MvPolynomial.X 0-MvPolynomial.X 2)*
    (MvPolynomial.X 1-MvPolynomial.X 2)

def invariantInterpolant (a : ℝ) (v : Fin 5 → ℝ) : Poly3 :=
  polyLift (scalarLagrange (contactSigma a) v) sigma

def signSigmaNodes (a : ℝ) : Fin 2 → ℝ := ![-a,-1]

def alternatingInterpolant (a : ℝ) (v : Fin 2 → ℝ) : Poly3 :=
  deltaPoly*polyLift (scalarLagrange (signSigmaNodes a) v) sigma

def permutedContact (a : ℝ) (r : Fin 5) (σ : Equiv.Perm (Fin 3)) : Fin 3 → ℝ :=
  contactTripleEval a (contactRepresentative r) ∘ σ

def TrivialSignInterpolationContract : Prop := ∀ a : ℝ, physical a →
  (∀ v : Fin 5 → ℝ, ∀ r : Fin 5, ∀ σ : Equiv.Perm (Fin 3),
    MvPolynomial.eval (permutedContact a r σ) (invariantInterpolant a v) = v r) ∧
  (∀ v : Fin 2 → ℝ, ∀ r : Fin 5, ∀ σ : Equiv.Perm (Fin 3),
    MvPolynomial.eval (permutedContact a r σ) (alternatingInterpolant a v) =
      MvPolynomial.eval (permutedContact a r σ) deltaPoly * ![0,0,0,v 0,v 1] r)

theorem polyLift_eval (p : Polynomial ℝ) (q : Poly3) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (polyLift p q) = p.eval (MvPolynomial.eval x q) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [polyLift,Polynomial.eval₂_add,map_add,Polynomial.eval_add] at *
    rw [hp,hr]
  | monomial n c => simp [polyLift,Polynomial.eval₂_monomial,Polynomial.eval_monomial]

theorem sigma_eval (x : Fin 3 → ℝ) : MvPolynomial.eval x sigma = ∑ i, x i := by
  simp [sigma,Fin.sum_univ_succ]
  ring

theorem sigma_eval_permutedContact (a : ℝ) (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) sigma = contactSigma a r := by
  rw [sigma_eval]
  exact Equiv.sum_comp σ (fun j => contacts a (contactRepresentative r j))

theorem invariantInterpolant_eval (a : ℝ) (ha : physical a) (v : Fin 5 → ℝ)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (invariantInterpolant a v) = v r := by
  rw [invariantInterpolant,polyLift_eval,sigma_eval_permutedContact]
  exact scalarLagrange_eval _ _ (contactSigma_injective a ha) r

theorem deltaPoly_eval (x : Fin 3 → ℝ) :
    MvPolynomial.eval x deltaPoly = (x 0-x 1)*(x 0-x 2)*(x 1-x 2) := by
  simp [deltaPoly]

theorem deltaPoly_eval_ne_iff (x : Fin 3 → ℝ) :
    MvPolynomial.eval x deltaPoly ≠ 0 ↔ Function.Injective x := by
  rw [deltaPoly_eval]
  constructor
  · intro h i j hij
    have h01 : x 0 ≠ x 1 := by intro he; apply h; simp [he]
    have h02 : x 0 ≠ x 2 := by intro he; apply h; simp [he]
    have h12 : x 1 ≠ x 2 := by intro he; apply h; simp [he]
    fin_cases i <;> fin_cases j <;> norm_num at * <;> tauto
  · intro h
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (h.ne (by decide)))
      (sub_ne_zero.mpr (h.ne (by decide)))) (sub_ne_zero.mpr (h.ne (by decide)))

theorem deltaPoly_permute_zero (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3))
    (hx : MvPolynomial.eval x deltaPoly = 0) :
    MvPolynomial.eval (x ∘ σ) deltaPoly = 0 := by
  by_contra hn
  have hi := (deltaPoly_eval_ne_iff (x ∘ σ)).mp hn
  have hix : Function.Injective x := by
    intro i j he
    have he' : (x ∘ σ) (σ.symm i) = (x ∘ σ) (σ.symm j) := by simpa using he
    simpa using congrArg σ (hi he')
  exact (deltaPoly_eval_ne_iff x).mpr hix hx

theorem deltaPoly_repeated (a : ℝ) (r : Fin 3) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a (Fin.castAdd 2 r) σ) deltaPoly = 0 := by
  apply deltaPoly_permute_zero
  rw [deltaPoly_eval]
  fin_cases r <;> simp [contactTripleEval,contactRepresentative]

theorem signSigmaNodes_injective (a : ℝ) (ha : physical a) :
    Function.Injective (signSigmaNodes a) := by
  have hu := ha.2
  intro i j he
  fin_cases i <;> fin_cases j <;> norm_num [signSigmaNodes] at * <;> linarith

theorem alternatingInterpolant_eval (a : ℝ) (ha : physical a) (v : Fin 2 → ℝ)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (alternatingInterpolant a v) =
      MvPolynomial.eval (permutedContact a r σ) deltaPoly * ![0,0,0,v 0,v 1] r := by
  rw [alternatingInterpolant,map_mul,polyLift_eval,sigma_eval_permutedContact]
  fin_cases r
  · have h := deltaPoly_repeated a 0 σ
    change MvPolynomial.eval (permutedContact a 0 σ) deltaPoly = 0 at h
    simp [h]
  · have h := deltaPoly_repeated a 1 σ
    change MvPolynomial.eval (permutedContact a 1 σ) deltaPoly = 0 at h
    simp [h]
  · have h := deltaPoly_repeated a 2 σ
    change MvPolynomial.eval (permutedContact a 2 σ) deltaPoly = 0 at h
    simp [h]
  · change MvPolynomial.eval (permutedContact a 3 σ) deltaPoly *
      (scalarLagrange (signSigmaNodes a) v).eval (contactSigma a 3) =
        MvPolynomial.eval (permutedContact a 3 σ) deltaPoly * v 0
    have he : contactSigma a 3 = signSigmaNodes a 0 := by
      rw [contactSigma_values]
      rfl
    rw [he,scalarLagrange_eval _ _ (signSigmaNodes_injective a ha)]
  · change MvPolynomial.eval (permutedContact a 4 σ) deltaPoly *
      (scalarLagrange (signSigmaNodes a) v).eval (contactSigma a 4) =
        MvPolynomial.eval (permutedContact a 4 σ) deltaPoly * v 1
    have he : contactSigma a 4 = signSigmaNodes a 1 := by
      rw [contactSigma_values]
      rfl
    rw [he,scalarLagrange_eval _ _ (signSigmaNodes_injective a ha)]

theorem contact_interpolation_trivial_sign_parts : TrivialSignInterpolationContract := by
  intro a ha
  exact ⟨invariantInterpolant_eval a ha,alternatingInterpolant_eval a ha⟩

#check contact_interpolation_trivial_sign_parts
#print axioms contact_interpolation_trivial_sign_parts
#check TrivialSignInterpolationContract
#print axioms TrivialSignInterpolationContract
end Blueprint.Thomson.Finite
