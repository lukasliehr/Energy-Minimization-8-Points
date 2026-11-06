import AllS.Units.N_FI.N_generic_moments.N_kernelQ_complex
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: KernelPositivity.kernelQ_swap.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem kernelQ_swap (k : ℕ) (u v t : ℝ) : kernelQ k u v t = kernelQ k v u t := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [kernelQ,mul_comm]
  | more k hk hk1 => simp [kernelQ,hk,hk1,mul_comm,mul_left_comm,mul_assoc]

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_kernelQ_swap (k : ℕ) (u v t : ℝ) : kernelQ k u v t = kernelQ k v u t :=
  GenericMoments.kernelQ_swap k u v t
#check generic_moments_kernelQ_swap
#print axioms generic_moments_kernelQ_swap
end Blueprint.Thomson.Finite
