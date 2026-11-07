import ThomsonNegative.Certificate.Bridges.PowerSums
import ThomsonNegative.Certificate.Bridges.RawScalar

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
open MvPolynomial

def rawProject (p : Poly3) : Poly3 :=
  C 6*reynoldsPolynomial p+repeatPolynomial 0 (reynoldsPolynomial p)+
    repeatPolynomial 1 (reynoldsPolynomial p)+repeatPolynomial 2 (reynoldsPolynomial p)

lemma rawProject_add (p q : Poly3) : rawProject (p+q)=rawProject p+rawProject q := by
  simp only [rawProject,reynolds_add,map_add,mul_add]
  ring

lemma rawProject_C_mul (c : ℝ) (p : Poly3) : rawProject (C c*p)=C c*rawProject p := by
  simp only [rawProject,reynolds_C_mul,map_mul,repeatPolynomial,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq]
  ring

lemma rawProject_zero : rawProject 0=0 := by simp [rawProject,reynoldsPolynomial]

def orbitCoordinates (a b c : Nat) : Poly3 :=
  coordinatePowerSum a*coordinatePowerSum b*coordinatePowerSum c-
    coordinatePowerSum (a+b)*coordinatePowerSum c-
    coordinatePowerSum (a+c)*coordinatePowerSum b-
    coordinatePowerSum (b+c)*coordinatePowerSum a+
    C 2*coordinatePowerSum (a+b+c)+
    C (1/3:ℝ)*(coordinatePowerSum (a+b)+coordinatePowerSum (a+c)+coordinatePowerSum (b+c))

lemma orbitCoordinates_subst (a b c : Nat) :
    invariantSubst (orbitCoordinates a b c)=
      rawProject (MvPolynomial.X 0^a*MvPolynomial.X 1^b*MvPolynomial.X 2^c) := by
  simp only [orbitCoordinates,map_add,map_sub,map_mul,coordinatePowerSum_subst]
  apply MvPolynomial.funext
  intro x
  simp [rawProject,reynoldsPolynomial_eval,repeatPolynomial_eval,
    ThomsonNegative.Geometry.GenericMoments.symEval,rawPowerSum,invariantSubst,pow_add]
  ring

abbrev RawTerm := Int × (Nat × Nat × Nat)

def termPolynomial (i j : Nat) (t : RawTerm) : Poly3 :=
  C (t.1:ℝ)*(MvPolynomial.X 0^(i+t.2.1)*MvPolynomial.X 1^(j+t.2.2.1)*MvPolynomial.X 2^t.2.2.2)

def termCoordinates (i j : Nat) (t : RawTerm) : Poly3 :=
  C (t.1:ℝ)*orbitCoordinates (i+t.2.1) (j+t.2.2.1) t.2.2.2

def termsPolynomial (i j : Nat) : List RawTerm → Poly3
  | [] => 0
  | t::ts => termPolynomial i j t+termsPolynomial i j ts

def termsCoordinates (i j : Nat) : List RawTerm → Poly3
  | [] => 0
  | t::ts => termCoordinates i j t+termsCoordinates i j ts

lemma termsCoordinates_subst (i j : Nat) (ts : List RawTerm) :
    invariantSubst (termsCoordinates i j ts)=rawProject (termsPolynomial i j ts) := by
  induction ts with
  | nil => simp [termsCoordinates,termsPolynomial,rawProject_zero]
  | cons t ts ih =>
    simp only [termsCoordinates,termsPolynomial,map_add,rawProject_add,ih]
    congr 1
    change invariantSubst (C (t.1:ℝ)*orbitCoordinates _ _ _)=rawProject (C (t.1:ℝ)*_)
    rw [map_mul,rawProject_C_mul,orbitCoordinates_subst]
    simp [invariantSubst]

lemma termsPolynomial_shift (i j : Nat) (ts : List RawTerm) :
    termsPolynomial i j ts=MvPolynomial.X 0^i*MvPolynomial.X 1^j*termsPolynomial 0 0 ts := by
  induction ts with
  | nil => simp [termsPolynomial]
  | cons t ts ih => simp only [termsPolynomial,termPolynomial,ih,zero_add,pow_add]; ring

lemma rawMoment_from_terms (k i j : Nat) (ts : List RawTerm)
    (h : termsPolynomial 0 0 ts=kernelQPolynomial k) :
    invariantSubst (termsCoordinates i j ts+C ((if k=0 then 1 else 0)/7:ℝ))=
      kernelRPolynomial k i j := by
  rw [map_add,termsCoordinates_subst,termsPolynomial_shift,h]
  simp [rawProject,kernelRPolynomial,kernelSPolynomial,invariantSubst]

end ThomsonNegative.Certificate.Bridges
