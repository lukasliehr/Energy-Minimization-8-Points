import AllS.Units.N_GI.N_variance_sharp.N_variance_tensor_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceUniformGram_entry_01_04 :
    varianceUniformGramFromU 1 4=varianceUniformGramData 1 4 := by decide +kernel
#print axioms varianceUniformGram_entry_01_04
end Blueprint.Thomson.Tail.Implementation
