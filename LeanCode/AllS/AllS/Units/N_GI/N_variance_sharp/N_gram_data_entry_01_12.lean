import AllS.Units.N_GI.N_variance_sharp.N_variance_tensor_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceUniformGram_entry_01_12 :
    varianceUniformGramFromU 1 12=varianceUniformGramData 1 12 := by decide +kernel
#print axioms varianceUniformGram_entry_01_12
end Blueprint.Thomson.Tail.Implementation
