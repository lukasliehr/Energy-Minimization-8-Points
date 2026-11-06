import AllS.Units.N_FI.N_upstream_evaluation.N_Q_eval
import AllS.Units.N_FI.N_upstream_evaluation.N_S_R_eval
import AllS.Units.N_FI.N_upstream_evaluation.N_moment_sums

noncomputable section
namespace Blueprint.Thomson.Finite

def GenericMomentEvaluationContract : Prop :=
  KernelQEvaluationContract ∧ KernelSREvaluationContract ∧ MomentEvaluationContract
theorem generic_moment_evaluation : GenericMomentEvaluationContract :=
  ⟨upstream_evaluation_Q_eval, upstream_evaluation_S_R_eval, upstream_evaluation_moment_sums⟩

#check generic_moment_evaluation
#print axioms generic_moment_evaluation
#check GenericMomentEvaluationContract
#print axioms GenericMomentEvaluationContract
end Blueprint.Thomson.Finite
