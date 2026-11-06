import AllS.Units.N_FI.N_generic_moments.N_kernelQ_complex
import AllS.Units.N_FI.N_generic_moments.N_sum_swaps
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: MomentMatrices.powerFeatures, MomentMatrices.momentMatrix, MomentMatrices.momentMatrix_entry.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

noncomputable def powerFeatures (m : ℕ) (x : Point) (y : Configuration) :
    Matrix (Fin m) Index ℝ := fun a j => ⟪x,y j⟫_ℝ^a.val

noncomputable def momentMatrix (m k : ℕ) (y : Configuration) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i : Index, powerFeatures m (y i) y * sphericalKernel (y i) y k *
    (powerFeatures m (y i) y).transpose

theorem momentMatrix_entry (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (fun u v t => u^a.val*v^b.val*kernelQ k u v t)) := by
  simp only [momentMatrix,Matrix.sum_apply,Matrix.mul_apply,Matrix.transpose_apply,
    powerFeatures,sphericalKernel,tripleSum,onTriples,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_moment_entry (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (fun u v t => u^a.val*v^b.val*kernelQ k u v t)) :=
  GenericMoments.momentMatrix_entry m k y a b
#check generic_moments_moment_entry
#print axioms generic_moments_moment_entry
end Blueprint.Thomson.Finite
