import AllS.Units.N_GI.N_signed_mean.N_tensor_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanUniformGram_entry_07_12 :
    meanUniformGramFromU 7 12=meanUniformGramData 7 12 := by decide +kernel

#print axioms meanUniformGram_entry_07_12
end Blueprint.Thomson.Tail.Implementation
