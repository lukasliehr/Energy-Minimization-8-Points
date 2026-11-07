import AllS.Units.N_F.N_geometry
import AllS.Units.N_FI.N_upstream_evaluation.N_moment_sums
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The four exact affine contacts, as polynomials in the varying height. -/
def contactPolynomial : Fin 4 → Polynomial ℝ :=
  ![Polynomial.X,2*Polynomial.X-1,
    -Polynomial.X+Polynomial.C (1/Real.sqrt 2)*(1-Polynomial.X),
    -Polynomial.X-Polynomial.C (1/Real.sqrt 2)*(1-Polynomial.X)]

def candidateTripleSubst (i j k : Fin 8) : Poly3 →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![contactPolynomial (candidateContactLabel i j),
    contactPolynomial (candidateContactLabel i k),contactPolynomial (candidateContactLabel j k)]

/-- This linear map holds every coefficient of the input polynomial fixed. -/
def candidateFamilyMap : Poly3 →ₗ[ℝ] Polynomial ℝ :=
  ∑ i : Fin 8,∑ j : Fin 8,∑ k : Fin 8,
    if i≠j ∧ j≠k ∧ k≠i then (candidateTripleSubst i j k).toLinearMap else 0

def L0 (a : ℝ) : Poly3 →ₗ[ℝ] ℝ where
  toFun f := (candidateFamilyMap f).eval a
  map_add' f g := by simp
  map_smul' c f := by simp

def L1 (a : ℝ) : Poly3 →ₗ[ℝ] ℝ where
  toFun f := (candidateFamilyMap f).derivative.eval a
  map_add' f g := by simp
  map_smul' c f := by simp

def ell0 (a : ℝ) : Poly3 →ₗ[ℝ] ℝ := (1/6 : ℝ) • L0 a
def ell1 (a : ℝ) : Poly3 →ₗ[ℝ] ℝ := (1/6 : ℝ) • L1 a

theorem contactPolynomial_eval (a : ℝ) (i : Fin 4) :
    (contactPolynomial i).eval a=contacts a i := by
  fin_cases i <;> simp [contactPolynomial,contacts] <;> ring

theorem candidateTripleSubst_eval (a : ℝ) (i j k : Fin 8) (f : Poly3) :
    (candidateTripleSubst i j k f).eval a=
      MvPolynomial.eval ![contacts a (candidateContactLabel i j),
        contacts a (candidateContactLabel i k),contacts a (candidateContactLabel j k)] f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [candidateTripleSubst]
  | add f g hf hg => simp only [map_add,Polynomial.eval_add,hf,hg]
  | mul_X f r hf =>
    simp only [map_mul,Polynomial.eval_mul,hf]
    congr 1
    fin_cases r <;> simp [candidateTripleSubst,contactPolynomial_eval]

theorem candidateFamilyMap_apply (f : Poly3) :
    candidateFamilyMap f=∑ i : Fin 8,∑ j : Fin 8,∑ k : Fin 8,
      if i≠j ∧ j≠k ∧ k≠i then candidateTripleSubst i j k f else 0 := by
  simp only [candidateFamilyMap,LinearMap.sum_apply,LinearMap.zero_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> rfl

theorem L0_eq_distinctPolySum (a : ℝ) (ha : physical a) (f : Poly3) :
    L0 a f=distinctPolySum (X a) f := by
  change (candidateFamilyMap f).eval a=_
  rw [candidateFamilyMap_apply]
  simp only [Polynomial.eval_finsetSum,distinctPolySum,DistinctSum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : i≠j ∧ j≠k ∧ k≠i
  · rw [if_pos h,if_pos h,candidateTripleSubst_eval]
    simp only [polyOnTriples,candidate_gram_entry a ha,if_neg h.1,if_neg h.2.1,if_neg h.2.2.symm]
  · simp [h]

theorem physical_eventually (a : ℝ) (ha : physical a) :
    ∀ᶠ b in nhds a,physical b :=
  isOpen_Ioo.mem_nhds ha

def FamilyFunctionalsContract : Prop := ∀ a : ℝ,physical a → ∀ f : Poly3,
  L0 a f=distinctPolySum (X a) f ∧
    HasDerivAt (fun b => distinctPolySum (X b) f) (L1 a f) a

theorem compatibility_family_functionals : FamilyFunctionalsContract := by
  intro a ha f
  refine ⟨L0_eq_distinctPolySum a ha f,?_⟩
  have hd := (candidateFamilyMap f).hasDerivAt a
  apply hd.congr_of_eventuallyEq
  filter_upwards [physical_eventually a ha] with b hb
  exact (L0_eq_distinctPolySum b hb f).symm

#check compatibility_family_functionals
#print axioms compatibility_family_functionals
end Blueprint.Thomson.Finite
