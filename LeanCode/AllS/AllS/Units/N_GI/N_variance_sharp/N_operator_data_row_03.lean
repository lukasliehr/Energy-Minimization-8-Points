import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceAFromData_exact_03 : ∀j : Fin 16,
    varianceAFromData 3 j =
      if (1:Fin 8)=((finProdFinEquiv (m:=8) (n:=2)).symm j).1 then
        varianceBlockAData 1 1 ((finProdFinEquiv (m:=8) (n:=2)).symm j).2 else 0 := by decide +kernel
#print axioms varianceAFromData_exact_03
end Blueprint.Thomson.Tail.Implementation
