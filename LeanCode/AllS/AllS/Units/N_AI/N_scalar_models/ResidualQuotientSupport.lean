import AllS.Units.N_AI.N_scalar_models.N_reciprocal_quotient_model
import AllS.Units.N_AI.N_scalar_models.ScalarInitialization
import AllS.Units.N_AI.N_scalar_models.ProductGateSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def QModel.midpointCoefficients {n : ℕ} (P : QModel n) : Fin (n+1) → ℝ :=
  fun k => ((P.coeff k).mid:ℝ)

def ResidualQuotientSupportStatement : Prop :=
  ∀ {n : ℕ} (R J : QModel n) (f g : ℝ → ℝ) (c : Fin (n+1) → ℝ) (μ : ℚ),
    0 < μ → (∀ x ∈ cellDomain, (μ:ℝ) ≤ |g x|) → R.asTM.CoeffContains c →
    J.asTM.Valid (fun x => f x-g x*scalarEval c x) →
    (J.norm+J.error)/μ ≤ R.error → R.asTM.Valid (fun x => f x/g x)

theorem QModel.midpoint_coefficients_mem {n : ℕ} (P : QModel n)
    (hp : ∀ k, (P.coeff k).lo ≤ (P.coeff k).hi) :
    P.asTM.CoeffContains P.midpointCoefficients := by
  intro k
  have h : ((P.coeff k).lo:ℝ) ≤ ((P.coeff k).hi:ℝ) := by exact_mod_cast hp k
  change ((P.coeff k).lo:ℝ) ≤ ((P.coeff k).mid:ℝ) ∧
    ((P.coeff k).mid:ℝ) ≤ ((P.coeff k).hi:ℝ)
  simp only [QInterval.mid, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  constructor <;> linarith

theorem QModel.midpoint_polynomial_valid {n : ℕ} (P : QModel n)
    (hp : ∀ k, (P.coeff k).lo ≤ (P.coeff k).hi) (he : 0 ≤ P.error) :
    P.asTM.Valid (scalarEval P.midpointCoefficients) :=
  TM.valid_polynomial P.asTM _ (P.midpoint_coefficients_mem hp) he

theorem QModel.valid_abs_le {n : ℕ} (J : QModel n) (h : ℝ → ℝ)
    (hj : J.asTM.Valid h) (x : ℝ) (hx : x ∈ cellDomain) :
    |h x| ≤ ((J.norm+J.error:ℚ):ℝ) := by
  simpa only [QModel.norm, QModel.asTM, QInterval.asBox, Box.magnitude, QInterval.mag,
    Rat.cast_add, Rat.cast_sum] using hj.abs_le x hx

/- The quotient recurrence is a way to propose the polynomial. Soundness uses
   its fixed coefficient membership and COMPLETE residual, so no recurrence
   identity or small-residual/Neumann hypothesis is needed in this theorem. -/
theorem residualQuotientSupport : ResidualQuotientSupportStatement := by
  intro n R J f g c μ hμ hsep hc hj he
  have hμR : (0:ℝ) < μ := by exact_mod_cast hμ
  have hres : ∀ x ∈ cellDomain,
      |f x-g x*(finitePolynomial c).eval x| ≤ ((J.norm+J.error:ℚ):ℝ) := by
    intro x hx
    simpa only [finitePolynomial_eval] using J.valid_abs_le _ hj x hx
  have hB0 : (0:ℝ) ≤ ((J.norm+J.error:ℚ):ℝ) :=
    (abs_nonneg _).trans (hres 0 (by constructor <;> norm_num [cellDomain]))
  have heR : ((J.norm+J.error:ℚ):ℝ)/(μ:ℝ) ≤ (R.error:ℝ) := by exact_mod_cast he
  refine ⟨by exact_mod_cast (div_nonneg hB0 hμR.le).trans heR, c, hc, ?_⟩
  intro x hx
  rw [←finitePolynomial_eval]
  exact (scalar_models_quotient_residual f g (finitePolynomial c) μ
    ((J.norm+J.error:ℚ):ℝ) hμR hsep hres x hx).trans heR

#check residualQuotientSupport
#print ResidualQuotientSupportStatement
#print axioms residualQuotientSupport
#print axioms QModel.midpoint_polynomial_valid
end Blueprint.CAP
