import AllS.Units.N_FI.N_generic_moments.N_sum_swaps
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SumLinearity.distinctSum_add, SumLinearity.distinctSum_mul, SumLinearity.offSum_add, SumLinearity.offSum_mul.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem distinctSum_add (f g : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f i j k+g i j k)=distinctSum f+distinctSum g := by
  simp only [distinctSum, Finite.DistinctSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem distinctSum_mul (c : ℝ) (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => c*f i j k)=c*distinctSum f := by
  simp [distinctSum, Finite.DistinctSum,Finset.mul_sum,mul_ite]

theorem offSum_add (f g : Index → Index → ℝ) :
    offSum (fun i j => f i j+g i j)=offSum f+offSum g := by
  simp only [offSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem offSum_mul (c : ℝ) (f : Index → Index → ℝ) :
    offSum (fun i j => c*f i j)=c*offSum f := by
  simp [offSum,Finset.mul_sum,mul_ite]

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_sum_linearity (f g : Fin 8 → Fin 8 → Fin 8 → ℝ) (p q : Fin 8 → Fin 8 → ℝ) (c : ℝ) :
    distinctSum (fun i j k => f i j k + g i j k) = distinctSum f + distinctSum g ∧
    distinctSum (fun i j k => c * f i j k) = c * distinctSum f ∧
    offSum (fun i j => p i j + q i j) = offSum p + offSum q ∧
    offSum (fun i j => c * p i j) = c * offSum p := by
  exact ⟨distinctSum_add f g, distinctSum_mul c f, offSum_add p q, offSum_mul c p⟩
#check generic_moments_sum_linearity
#print axioms generic_moments_sum_linearity
end Blueprint.Thomson.Finite
