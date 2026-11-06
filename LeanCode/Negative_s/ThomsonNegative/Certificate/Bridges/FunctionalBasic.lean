import ThomsonNegative.Certificate.Bridges.TargetCompatibility
import ThomsonNegative.Structure.Factored.FunctionalData
import ThomsonNegative.Structure.Packed.IdentitySound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure

def integerPolynomial : List Int → Polynomial ℝ
  | [] => 0
  | c::cs => Polynomial.C (c:ℝ)+Polynomial.X*integerPolynomial cs

lemma integerPolynomial_eval (L : List Int) (a : ℝ) :
    (integerPolynomial L).eval a=Packed.evalZ L a := by
  induction L with
  | nil => simp [integerPolynomial,Packed.evalZ]
  | cons c cs ih =>
    simp only [integerPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
    rw [ih]
    rfl

def functionalPolynomial (i : Fin 102) : Polynomial ℝ :=
  Polynomial.C (1/(Factored.FunctionalData.denominator i.val:ℝ))*
    integerPolynomial (Exact.recCoeffs (Factored.FunctionalData.numerator i.val))

def functionalSlopePolynomial (i : Fin 102) : Polynomial ℝ :=
  Polynomial.C (1/(Factored.FunctionalData.denominator i.val:ℝ))*
    integerPolynomial (Exact.recCoeffs (Factored.FunctionalData.slopeNumerator i.val))

def orbitSigma (a : ℝ) : Fin 5 → ℝ :=
  ![4*a-1,-a+Real.sqrt 2*(1-a),-a-Real.sqrt 2*(1-a),-a,-1]
def orbitE2 (a : ℝ) : Fin 5 → ℝ :=
  ![5*a^2-2*a,-a^2/2-a+1/2,-a^2/2-a+1/2,-3*a^2/2+a-1/2,-7*a^2/2+3*a-1/2]
def orbitE3 (a : ℝ) : Fin 5 → ℝ :=
  ![2*a^3-a^2,3*a^3/2-a^2+a/2-Real.sqrt 2*a^2*(1-a),
    3*a^3/2-a^2+a/2+Real.sqrt 2*a^2*(1-a),a^3/2+a^2-a/2,a^3+3*a^2/2-2*a+1/2]

lemma orbit_sigma_eval (r : Fin 5) (a : ℝ) :
    (orbitSubstitution r sigma).eval a=orbitSigma a r := by
  fin_cases r <;>
    simp [orbitSubstitution,sigma,orbitLabels,contactPolynomial,orbitSigma] <;> ring

lemma orbit_e2_eval (r : Fin 5) (a : ℝ) :
    (orbitSubstitution r e2).eval a=orbitE2 a r := by
  fin_cases r <;>
    simp [orbitSubstitution,e2,orbitLabels,contactPolynomial,orbitE2] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

lemma orbit_e3_eval (r : Fin 5) (a : ℝ) :
    (orbitSubstitution r e3).eval a=orbitE3 a r := by
  fin_cases r <;>
    simp [orbitSubstitution,e3,orbitLabels,contactPolynomial,orbitE3] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

lemma familyPolynomial_eval (p : Poly3) (a : ℝ) :
    (familyPolynomial p).eval a=∑ r : Fin 5,orbitCount r*(orbitSubstitution r p).eval a := by
  rw [familyPolynomial_apply]
  simp [Fin.sum_univ_succ]

lemma familyPolynomial_invariant_eval (t : Tag) (a : ℝ) :
    (familyPolynomial (invariantMonomial t)).eval a=
      ∑ r : Fin 5,orbitCount r*(orbitSigma a r^t.1*orbitE2 a r^t.2.1*orbitE3 a r^t.2.2) := by
  rw [familyPolynomial_eval]
  simp only [invariantMonomial,map_mul,map_pow,Polynomial.eval_mul,Polynomial.eval_pow,
    orbit_sigma_eval,orbit_e2_eval,orbit_e3_eval]

lemma sqrt_two_pow_even (n : Nat) : (Real.sqrt (2:ℝ))^(2*n)=(2:ℝ)^n := by
  rw [pow_mul,Real.sq_sqrt (by norm_num)]

@[simp] lemma sqrt_two_pow02 : (Real.sqrt (2:ℝ))^2=(2:ℝ) := by
  convert sqrt_two_pow_even 1 using 1 <;> norm_num

@[simp] lemma sqrt_two_pow04 : (Real.sqrt (2:ℝ))^4=(4:ℝ) := by
  convert sqrt_two_pow_even 2 using 1 <;> norm_num

@[simp] lemma sqrt_two_pow06 : (Real.sqrt (2:ℝ))^6=(8:ℝ) := by
  convert sqrt_two_pow_even 3 using 1 <;> norm_num

@[simp] lemma sqrt_two_pow08 : (Real.sqrt (2:ℝ))^8=(16:ℝ) := by
  convert sqrt_two_pow_even 4 using 1 <;> norm_num

@[simp] lemma sqrt_two_pow10 : (Real.sqrt (2:ℝ))^10=(32:ℝ) := by
  convert sqrt_two_pow_even 5 using 1 <;> norm_num

@[simp] lemma sqrt_two_pow12 : (Real.sqrt (2:ℝ))^12=(64:ℝ) := by
  convert sqrt_two_pow_even 6 using 1 <;> norm_num
end ThomsonNegative.Certificate.Bridges
