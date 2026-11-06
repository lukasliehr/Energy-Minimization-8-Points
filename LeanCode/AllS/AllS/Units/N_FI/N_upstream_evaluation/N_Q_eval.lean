import AllS.Units.N_FI.N_moment_kernels.N_canonical_QSR
import AllS.Units.N_F.N_generic_moments

noncomputable section
namespace Blueprint.Thomson.Finite

def KernelQEvaluationContract : Prop := ∀ k : ℕ, ∀ u v t : ℝ,
  MvPolynomial.eval ![u,v,t] (kernelQPoly k) = GenericMoments.kernelQ k u v t
theorem upstream_evaluation_Q_eval (k : ℕ) (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] (kernelQPoly k) = GenericMoments.kernelQ k u v t := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQPoly, GenericMoments.kernelQ]
  | one => simp [kernelQPoly, GenericMoments.kernelQ]
  | more k hk hk1 => simp [kernelQPoly, GenericMoments.kernelQ, hk, hk1]

#check upstream_evaluation_Q_eval
#print axioms upstream_evaluation_Q_eval
#check KernelQEvaluationContract
#print axioms KernelQEvaluationContract
end Blueprint.Thomson.Finite
