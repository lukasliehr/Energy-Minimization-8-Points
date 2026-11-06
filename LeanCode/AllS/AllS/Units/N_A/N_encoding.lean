import AllS.Units.N_AI.N_encoding.N_output_witness

namespace Blueprint.CAP
def CompleteEncodingsStatement : Prop :=
  EncodingListEvaluationStatement ∧ EncodingInjectivityStatement ∧
    EncodingProductBoundStatement ∧ EncodingOutputWitnessStatement

theorem completeEncodings_sound : CompleteEncodingsStatement :=
  ⟨encoding_list_evaluation, encoding_injectivity, encoding_product_bound, encoding_output_witness⟩
#check completeEncodings_sound
#print CompleteEncodingsStatement
#print axioms completeEncodings_sound
end Blueprint.CAP
