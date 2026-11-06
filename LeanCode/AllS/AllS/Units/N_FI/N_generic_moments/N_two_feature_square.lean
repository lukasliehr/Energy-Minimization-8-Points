import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/KernelPositivity.lean:8-13. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.GenericMoments

theorem two_feature_square {ι : Type*} [Fintype ι] (c a b : ι → ℝ) : (∑ i, ∑ j, c i * c j * (a i * a j + b i * b j)) = (∑ i, c i * a i) ^ 2 + (∑ i, c i * b i) ^ 2 := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
theorem generic_moments_two_feature_square {ι : Type*} [Fintype ι] (c a b : ι → ℝ) : (∑ i, ∑ j, c i * c j * (a i * a j + b i * b j)) = (∑ i, c i * a i) ^ 2 + (∑ i, c i * b i) ^ 2 :=
  GenericMoments.two_feature_square c a b
#check generic_moments_two_feature_square
#print axioms generic_moments_two_feature_square
end Blueprint.Thomson.Finite

