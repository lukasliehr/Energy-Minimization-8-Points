import AllS.Units.N_AI.N_scalar_models.N_product_error
import AllS.Units.N_AI.N_scalar_models.N_log_common_hull

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def quotientCoefficientRecurrence {n : ℕ} (a b c : Fin (n+1)→ℝ) : Prop :=
  c 0=a 0/b 0 ∧ ∀ m : Fin (n+1), 0 < m.val →
    c m=(a m-∑ i∈Finset.univ.erase (0:Fin (n+1)),
      if h : i.val ≤ m.val then b i*c ⟨m.val-i.val, by omega⟩ else 0)/b 0

def ScalarReciprocalQuotientModelStatement : Prop :=
  ∀ {n : ℕ} (MU MV R J : TM n) (f g : ℝ→ℝ)
    (a : MU.Witness f) (b : MV.Witness g) (c : Fin (n+1)→ℝ) (μ B : ℝ),
    b.coeff 0≠0 → 0<μ →
    (∀ x∈cellDomain, μ≤|g x|) → quotientCoefficientRecurrence a.coeff b.coeff c →
    R.CoeffContains c → J.Valid (fun x=>f x-g x*scalarEval c x) →
    (∑ k, ((J.coeff k).magnitude:ℝ))+(J.error:ℝ)≤B →
    B/μ≤(R.error:ℝ) → R.Valid (fun x=>f x/g x)

theorem TM.Valid.abs_le {n : ℕ} {J : TM n} {h : ℝ→ℝ} (hj : J.Valid h)
    (x : ℝ) (hx : x∈cellDomain) :
    |h x| ≤ (∑ k, ((J.coeff k).magnitude:ℝ))+(J.error:ℝ) := by
  obtain ⟨he,a,ha,hr⟩ := hj
  have hp : |scalarEval a x| ≤ ∑ k, ((J.coeff k).magnitude:ℝ) :=
    (scalarEval_abs_le_sum a x hx).trans
      (Finset.sum_le_sum fun k _ => Box.abs_le_magnitude (ha k))
  calc
    |h x| = |scalarEval a x+(h x-scalarEval a x)| := by congr 1; ring
    _ ≤ |scalarEval a x|+|h x-scalarEval a x| := abs_add_le _ _
    _ ≤ _ := add_le_add hp (hr x hx)

theorem scalar_models_reciprocal_quotient_model : ScalarReciprocalQuotientModelStatement := by
  intro n MU MV R J f g a b c μ B hb hμ hsep hrec hc hj hB he
  have hres : ∀ x∈cellDomain, |f x-g x*(finitePolynomial c).eval x|≤B := by
    intro x hx
    rw [finitePolynomial_eval]
    exact (hj.abs_le x hx).trans hB
  have hB₀ : 0≤B := (abs_nonneg _).trans
    (hres 0 (by constructor <;> norm_num [cellDomain]))
  refine ⟨by exact_mod_cast (div_nonneg hB₀ hμ.le).trans he, c, hc, ?_⟩
  intro x hx
  rw [←finitePolynomial_eval]
  exact (scalar_models_quotient_residual f g (finitePolynomial c) μ B hμ hsep hres x hx).trans he

#check scalar_models_reciprocal_quotient_model
#print ScalarReciprocalQuotientModelStatement
#print axioms scalar_models_reciprocal_quotient_model
end Blueprint.CAP
