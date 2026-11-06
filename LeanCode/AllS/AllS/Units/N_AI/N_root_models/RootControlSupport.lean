import AllS.Units.N_AI.N_root_models.N_proposal_domain
import AllS.Units.N_AI.N_data.RationalBernstein

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def RootControlSupportStatement : Prop :=
  ∀ {N : ℕ} (z : Fin (N+1) → ℤ) (i : Fin (N+1)),
    bernsteinControls (dyadicRootCoefficients z) i = (rationalRootControls z i : ℝ)

theorem rationalBernsteinTransform_cast (d i k : ℕ) (hi : i ≤ d) :
    (rationalBernsteinTransform d i k : ℝ) = (bernsteinTransform d i k : ℝ) := by
  rw [bernsteinTransform_source_formula d i k hi]
  simp [rationalBernsteinTransform]

theorem rootControlSupport : RootControlSupportStatement := by
  intro N z i
  unfold bernsteinControls rationalRootControls dyadicRootCoefficients
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_intCast,
    Rat.cast_pow, Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro k _
  rw [rationalBernsteinTransform_cast N i.val k.val (by omega)]
  ring

#print RootControlSupportStatement
#print axioms rootControlSupport
end Blueprint.CAP
