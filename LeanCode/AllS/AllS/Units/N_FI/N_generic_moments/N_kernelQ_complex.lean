import AllS.Units.N_FI.N_generic_moments.N_real_power_recurrence
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: Kernels.kernelQ, KernelPositivity.sphericalKernel, Kernels.kernelQ_complex.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

noncomputable def kernelQ : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _,_,_ => 1
  | 1, u,v,t => t-u*v
  | k+2, u,v,t => 2*(t-u*v)*kernelQ (k+1) u v t -
      (1-u^2)*(1-v^2)*kernelQ k u v t

noncomputable def sphericalKernel {ι : Type*} (x : Point) (y : ι → Point) (k : ℕ) :
    Matrix ι ι ℝ := fun i j => kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ

theorem kernelQ_complex (k : ℕ) (u v t : ℝ) (w : ℂ)
    (hr : w.re=t-u*v) (hn : Complex.normSq w=(1-u^2)*(1-v^2)) :
    kernelQ k u v t = (w^k).re := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQ]
  | one => simpa [kernelQ] using hr.symm
  | more k hk hk1 =>
    rw [kernelQ, hk, hk1, real_power_recurrence, hr, hn]

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_kernelQ_complex (k : ℕ) (u v t : ℝ) (w : ℂ)
    (hr : w.re=t-u*v) (hn : Complex.normSq w=(1-u^2)*(1-v^2)) :
    kernelQ k u v t = (w^k).re :=
  GenericMoments.kernelQ_complex k u v t w hr hn
#check generic_moments_kernelQ_complex
#print axioms generic_moments_kernelQ_complex
end Blueprint.Thomson.Finite
