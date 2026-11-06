import ThomsonNegative.Structure.CanonicalBasis

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
open MvPolynomial
open ThomsonNegative.Geometry.GenericMoments

def rawPowerSum (n : ℕ) : Poly3 := MvPolynomial.X 0^n+MvPolynomial.X 1^n+MvPolynomial.X 2^n

def coordinatePowerSum : ℕ → Poly3
  | 0 => C 3
  | 1 => MvPolynomial.X 0
  | 2 => MvPolynomial.X 0^2-C 2*MvPolynomial.X 1
  | n+3 => MvPolynomial.X 0*coordinatePowerSum (n+2)-MvPolynomial.X 1*coordinatePowerSum (n+1)+MvPolynomial.X 2*coordinatePowerSum n

lemma rawPowerSum_recurrence (n : ℕ) :
    rawPowerSum (n+3)=sigma*rawPowerSum (n+2)-e2*rawPowerSum (n+1)+e3*rawPowerSum n := by
  simp only [rawPowerSum,sigma,e2,e3,pow_add]
  ring

lemma coordinatePowerSum_subst (n : ℕ) : invariantSubst (coordinatePowerSum n)=rawPowerSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · apply MvPolynomial.funext
      intro x
      norm_num [coordinatePowerSum,rawPowerSum,invariantSubst]
    rcases n with _ | n
    · simp [coordinatePowerSum,rawPowerSum,invariantSubst,sigma]
    rcases n with _ | n
    · apply MvPolynomial.funext
      intro x
      simp [coordinatePowerSum,rawPowerSum,invariantSubst,sigma,e2]
      ring
    · rw [coordinatePowerSum]
      simp only [map_add,map_sub,map_mul]
      rw [ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      simpa only [invariantSubst,MvPolynomial.aeval_X,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using (rawPowerSum_recurrence n).symm

def r0Coordinates (i j : ℕ) : Poly3 :=
  coordinatePowerSum i*coordinatePowerSum j-C (2/3:ℝ)*coordinatePowerSum (i+j)+
    C (1/3:ℝ)*(coordinatePowerSum i+coordinatePowerSum j)+C (1/7:ℝ)

lemma r0Coordinates_subst (i j : ℕ) : invariantSubst (r0Coordinates i j)=kernelRPolynomial 0 i j := by
  simp only [r0Coordinates,map_add,map_sub,map_mul,coordinatePowerSum_subst]
  apply MvPolynomial.funext
  intro x
  rw [kernelRPolynomial_eval]
  simp [rawPowerSum,invariantSubst,Rfun,Sfun,symEval,kernelQ,pow_add]
  ring

#print axioms coordinatePowerSum_subst
#print axioms r0Coordinates_subst
end ThomsonNegative.Certificate.Bridges
