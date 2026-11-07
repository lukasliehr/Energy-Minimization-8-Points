import AllS.Units.N_AI.N_matrix_polynomials.N_bernstein_interval

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def dyadicRootCoefficients {N : ℕ} (z : Fin (N+1) → ℤ) (k : Fin (N+1)) : ℝ :=
  (z k : ℝ)/2^256

def RootProposalDomainStatement : Prop :=
  ∀ {N : ℕ} (z : Fin (N+1) → ℤ) (c h C : ℝ),
    0 < h → 0 ≤ c-h → C ≤ Real.log (1+Real.sqrt 2/2) →
    (∀ i, 0 ≤ bernsteinControls (dyadicRootCoefficients z) i ∧
      bernsteinControls (dyadicRootCoefficients z) i ≤ C) →
    ∀ x ∈ cellDomain,
      1 ≤ 1+(c-h)/2 ∧ 1+(c-h)/2 ≤ 1+(c+h*x)/2 ∧
      0 ≤ scalarEval (dyadicRootCoefficients z) x ∧
      scalarEval (dyadicRootCoefficients z) x ≤ Real.log (1+Real.sqrt 2/2)

theorem bernstein_range_of_controls {d : ℕ} (a : Fin (d+1) → ℝ) (l u x : ℝ)
    (h : ∀ i, l ≤ bernsteinControls a i ∧ bernsteinControls a i ≤ u)
    (hx : x ∈ cellDomain) : l ≤ scalarEval a x ∧ scalarEval a x ≤ u := by
  rw [matrix_polynomials_bernstein_identity d a x]
  change l ≤ ∑ i, bernsteinControls a i*bernsteinWeight d i.val x ∧
    (∑ i, bernsteinControls a i*bernsteinWeight d i.val x) ≤ u
  constructor
  · calc
      l = ∑ i : Fin (d+1), l*bernsteinWeight d i.val x := by rw [←Finset.mul_sum, bernsteinWeight_sum, mul_one]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i).1 (bernsteinWeight_nonneg d i.val x hx))
  · calc
      _ ≤ ∑ i : Fin (d+1), u*bernsteinWeight d i.val x :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i).2 (bernsteinWeight_nonneg d i.val x hx))
      _ = u := by rw [←Finset.mul_sum, bernsteinWeight_sum, mul_one]

theorem root_models_proposal_domain : RootProposalDomainStatement := by
  intro N z c h C hh hc hC hcontrols x hx
  have hP := bernstein_range_of_controls (dyadicRootCoefficients z) 0 C x hcontrols hx
  refine ⟨by linarith, ?_, hP.1, hP.2.trans hC⟩
  have hxlo := hx.1
  have hmul := mul_le_mul_of_nonneg_left hxlo (le_of_lt hh)
  linarith

#print RootProposalDomainStatement
#print axioms root_models_proposal_domain
end Blueprint.CAP
