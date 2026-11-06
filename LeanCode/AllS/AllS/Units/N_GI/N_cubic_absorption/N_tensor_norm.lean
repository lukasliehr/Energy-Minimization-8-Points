import AllS.Units.N_GI.N_cubic_absorption.N_square_completion

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- Ordered tensor coordinates, with no symmetric-array multiplicities. -/
def orderedSquare {ι : Type*} [Fintype ι] (q : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι × ι) := WithLp.toLp 2 (fun ij => q ij.1*q ij.2)

theorem orderedSquare_norm_sq {ι : Type*} [Fintype ι] (q : EuclideanSpace ℝ ι) :
    ‖orderedSquare q‖^2=‖q‖^4 := by
  simp only [EuclideanSpace.real_norm_sq_eq,orderedSquare,Fintype.sum_prod_type,
    mul_pow,← Finset.mul_sum,← Finset.sum_mul]
  rw [← EuclideanSpace.real_norm_sq_eq q]
  ring

/-- The quadratic input norm transfers an ordered-array quadratic-form bound. -/
theorem cubic_tensor_norm {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (U : EuclideanSpace ℝ (ι × ι) →ₗ[ℝ] EuclideanSpace ℝ ι)
    (B : ℝ) (hU : ∀ z, inner ℝ (U z) (A (U z)) ≤ B*‖z‖^2)
    (q : EuclideanSpace ℝ ι) :
    inner ℝ (U (orderedSquare q)) (A (U (orderedSquare q))) ≤ B*‖q‖^4 := by
  simpa only [orderedSquare_norm_sq] using hU (orderedSquare q)

theorem cubic_two_signed_bounds {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hA : ∀ x, 0 ≤ inner ℝ x (A x))
    (hsym : ∀ x y, inner ℝ x (A y)=inner ℝ y (A x))
    (U : EuclideanSpace ℝ (ι × ι) →ₗ[ℝ] EuclideanSpace ℝ ι)
    (B : ℝ) (hU : ∀ z, inner ℝ (U z) (A (U z)) ≤ B*‖z‖^2)
    (C : EuclideanSpace ℝ ι → ℝ)
    (hc : ∀ q, inner ℝ q (A (U (orderedSquare q)))=C q)
    (q : EuclideanSpace ℝ ι) :
    -inner ℝ q (A q)+C q ≤ B*‖q‖^4/4 ∧
    -(B*‖q‖^4)/4 ≤ inner ℝ q (A q)+C q :=
  cubic_square_completion A hA hsym q (U (orderedSquare q)) (C q) (B*‖q‖^4)
    (hc q) (cubic_tensor_norm A U B hU q)

#print axioms orderedSquare_norm_sq
#print axioms cubic_two_signed_bounds
end Blueprint.Thomson.Tail.Implementation

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem cubic_absorption_tensor_norm {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (U : EuclideanSpace ℝ (ι × ι) →ₗ[ℝ] EuclideanSpace ℝ ι)
    (B : ℝ) (hU : ∀ z, inner ℝ (U z) (A (U z)) ≤ B*‖z‖^2) (q : EuclideanSpace ℝ ι) :
    ‖orderedSquare q‖^2=‖q‖^4 ∧
      inner ℝ (U (orderedSquare q)) (A (U (orderedSquare q))) ≤ B*‖q‖^4 :=
  ⟨orderedSquare_norm_sq q,cubic_tensor_norm A U B hU q⟩

#print axioms cubic_absorption_tensor_norm
end Blueprint.Thomson.Tail.Implementation
