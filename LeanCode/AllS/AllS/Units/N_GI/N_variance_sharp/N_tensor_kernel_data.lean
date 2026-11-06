import AllS.Units.N_GI.N_variance_sharp.N_physical_data
import AllS.Units.N_GI.N_variance_sharp.N_variance_tensor_data

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceAUData (i j k : Fin 16) : MeanRadical :=
  ∑b : Fin 2,meanRadicalMul
    (varianceBlockAData ((finProdFinEquiv (m:=8) (n:=2)).symm i).1
      ((finProdFinEquiv (m:=8) (n:=2)).symm i).2 b)
    (varianceUniformUData (varianceBlockEntry i b) j k)

def varianceSymAUData (i j k : Fin 16) : MeanRadical :=
  (1/6:ℚ) • (varianceAUData i j k+varianceAUData i k j+
    varianceAUData j i k+varianceAUData j k i+varianceAUData k i j+varianceAUData k j i)

end Blueprint.Thomson.Tail.Implementation
