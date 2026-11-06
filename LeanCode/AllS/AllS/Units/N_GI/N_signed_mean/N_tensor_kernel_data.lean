import AllS.Units.N_GI.N_signed_mean.N_basis_data
import AllS.Units.N_GI.N_signed_mean.N_tensor_data
import AllS.Units.N_GI.N_signed_mean.N_radical_operations

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def meanDotKernelData (p : Fin 8) (j k : Fin 16) : MeanRadical :=
  meanRadicalMul (meanBasisData (finProdFinEquiv (m:=8) (n:=2) (p,0)) j) (meanBasisData (finProdFinEquiv (m:=8) (n:=2) (p,0)) k)+
  meanRadicalMul (meanBasisData (finProdFinEquiv (m:=8) (n:=2) (p,1)) j) (meanBasisData (finProdFinEquiv (m:=8) (n:=2) (p,1)) k)

def meanOrderedKernelData (i j k : Fin 16) : MeanRadical :=
  -(∑p : Fin 8,meanRadicalMul (meanBKernelData i p) (meanDotKernelData p j k))

def meanCubicKernelData (i j k : Fin 16) : MeanRadical :=
  (1/3:ℚ) • (meanOrderedKernelData i j k+meanOrderedKernelData j i k+meanOrderedKernelData k i j)

def meanAUData (i j k : Fin 16) : MeanRadical :=
  ∑b : Fin 2,meanRadicalMul
    (meanBlockAData ((finProdFinEquiv (m:=8) (n:=2)).symm i).1
      ((finProdFinEquiv (m:=8) (n:=2)).symm i).2 b)
    (meanUniformUData (finProdFinEquiv (((finProdFinEquiv (m:=8) (n:=2)).symm i).1,b)) j k)

def meanSymAUData (i j k : Fin 16) : MeanRadical :=
  (1/6:ℚ) • (meanAUData i j k+meanAUData i k j+
    meanAUData j i k+meanAUData j k i+meanAUData k i j+meanAUData k j i)

end Blueprint.Thomson.Tail.Implementation
