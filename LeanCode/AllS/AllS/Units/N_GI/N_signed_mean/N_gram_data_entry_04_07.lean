import AllS.Units.N_GI.N_signed_mean.N_tensor_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanUniformGram_entry_04_07 :
    meanUniformGramFromU 4 7=meanUniformGramData 4 7 := by decide +kernel

#print axioms meanUniformGram_entry_04_07
end Blueprint.Thomson.Tail.Implementation
