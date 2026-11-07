import AllS.Units.N_GI.N_signed_mean.N_basis_data
import AllS.Units.N_GI.N_signed_mean.N_scalar_coefficients

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanFlatBasis : OrthonormalBasis (Fin 16) ℝ TangentCoordinates :=
  meanBlockBasis.reindex (finProdFinEquiv (m:=8) (n:=2))

def meanFlatIndex (i : Fin 16) : Fin 8 × Fin 2 :=
  meanBlockIndex ((finProdFinEquiv (m:=8) (n:=2)).symm i)

theorem meanFlatBasis_apply (i : Fin 16) : meanFlatBasis i=meanTangentNormalized (meanFlatIndex i) := by
  rw [meanFlatBasis,OrthonormalBasis.reindex_apply,meanBlockBasis_apply]
  rfl

end Blueprint.Thomson.Tail.Implementation
