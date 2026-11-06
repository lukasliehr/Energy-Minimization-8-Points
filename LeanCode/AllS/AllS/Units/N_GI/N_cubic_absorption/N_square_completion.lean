import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- Completion of both signed squares.  Positive semidefiniteness is enough;
no square root or diagonalization of the operator is needed for this step. -/
theorem cubic_square_completion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ[ℝ] E)
    (hA : ∀ x, 0 ≤ inner ℝ x (A x))
    (hsym : ∀ x y, inner ℝ x (A y)=inner ℝ y (A x))
    (q u : E) (C K : ℝ) (hc : inner ℝ q (A u)=C)
    (hu : inner ℝ u (A u) ≤ K) :
    -inner ℝ q (A q)+C ≤ K/4 ∧ -K/4 ≤ inner ℝ q (A q)+C := by
  have hminus := hA (q-(1/2:ℝ) • u)
  have hplus := hA (q+(1/2:ℝ) • u)
  simp only [map_sub,map_add,map_smul,inner_sub_left,inner_sub_right,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    hsym u q,hc] at hminus hplus
  constructor <;> nlinarith

#print axioms cubic_square_completion
end Blueprint.Thomson.Tail.Implementation
