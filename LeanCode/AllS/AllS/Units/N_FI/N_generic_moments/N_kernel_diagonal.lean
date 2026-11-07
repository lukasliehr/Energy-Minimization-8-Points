import AllS.Units.N_FI.N_generic_moments.N_kernelQ_complex
import AllS.Units.N_FI.N_generic_moments.N_onTriples_symmetry
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Generic all-parameter proof. S/R identities adapt upstream RCounting
(commit50d14bc06bd41f61573eb6a36eedb8d00759af8f); outer products expand
the explicit proved tangent features. No fixed-exponent certificate. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
namespace Blueprint.Thomson.GenericMoments
noncomputable def Sfun (k a b : ℕ) : ℝ → ℝ → ℝ → ℝ :=
  symEval (fun u v t => u^a * v^b * kernelQ k u v t)

theorem kernelQ_diagonal (k : ℕ) : kernelQ k 1 1 1 = if k=0 then 1 else 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQ]
  | one => simp [kernelQ]
  | more k hk hk1 => simp [kernelQ]

theorem Sfun_diagonal (k a b : ℕ) : Sfun k a b 1 1 1 = if k=0 then 1 else 0 := by
  simp only [Sfun, symEval, one_pow, one_mul, kernelQ_diagonal]
  split_ifs <;> norm_num

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments

theorem generic_moments_kernel_diagonal (k a b : ℕ) :
    kernelQ k 1 1 1 = (if k=0 then 1 else 0) ∧
    Sfun k a b 1 1 1 = (if k=0 then 1 else 0) := by
  exact ⟨kernelQ_diagonal k, Sfun_diagonal k a b⟩
end Blueprint.Thomson.Finite

#check Blueprint.Thomson.Finite.generic_moments_kernel_diagonal
#print axioms Blueprint.Thomson.Finite.generic_moments_kernel_diagonal
