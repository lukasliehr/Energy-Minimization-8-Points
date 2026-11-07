import AllS.Units.N_GI.N_signed_mean.N_basis_row_00
import AllS.Units.N_GI.N_signed_mean.N_basis_row_01
import AllS.Units.N_GI.N_signed_mean.N_basis_row_02
import AllS.Units.N_GI.N_signed_mean.N_basis_row_03
import AllS.Units.N_GI.N_signed_mean.N_basis_row_04
import AllS.Units.N_GI.N_signed_mean.N_basis_row_05
import AllS.Units.N_GI.N_signed_mean.N_basis_row_06
import AllS.Units.N_GI.N_signed_mean.N_basis_row_07
import AllS.Units.N_GI.N_signed_mean.N_basis_row_08
import AllS.Units.N_GI.N_signed_mean.N_basis_row_09
import AllS.Units.N_GI.N_signed_mean.N_basis_row_10
import AllS.Units.N_GI.N_signed_mean.N_basis_row_11
import AllS.Units.N_GI.N_signed_mean.N_basis_row_12
import AllS.Units.N_GI.N_signed_mean.N_basis_row_13
import AllS.Units.N_GI.N_signed_mean.N_basis_row_14
import AllS.Units.N_GI.N_signed_mean.N_basis_row_15
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation
theorem meanFlatBasis_coordinates (i : Fin 16) (p : Fin 8) (b : Fin 2) :
    meanFlatBasis i (p,b)=meanRadicalEval (meanBasisData (finProdFinEquiv (p,b)) i) := by
  fin_cases i
  · exact meanFlatBasis_coordinates_0 p b
  · exact meanFlatBasis_coordinates_1 p b
  · exact meanFlatBasis_coordinates_2 p b
  · exact meanFlatBasis_coordinates_3 p b
  · exact meanFlatBasis_coordinates_4 p b
  · exact meanFlatBasis_coordinates_5 p b
  · exact meanFlatBasis_coordinates_6 p b
  · exact meanFlatBasis_coordinates_7 p b
  · exact meanFlatBasis_coordinates_8 p b
  · exact meanFlatBasis_coordinates_9 p b
  · exact meanFlatBasis_coordinates_10 p b
  · exact meanFlatBasis_coordinates_11 p b
  · exact meanFlatBasis_coordinates_12 p b
  · exact meanFlatBasis_coordinates_13 p b
  · exact meanFlatBasis_coordinates_14 p b
  · exact meanFlatBasis_coordinates_15 p b
theorem meanBVertexKernel_data (i : Fin 16) (p : Fin 8) :
    meanBVertexKernel (meanFlatIndex i) p=meanRadicalEval (meanBKernelData i p) := by
  fin_cases i
  · exact meanBVertexKernel_data_0 p
  · exact meanBVertexKernel_data_1 p
  · exact meanBVertexKernel_data_2 p
  · exact meanBVertexKernel_data_3 p
  · exact meanBVertexKernel_data_4 p
  · exact meanBVertexKernel_data_5 p
  · exact meanBVertexKernel_data_6 p
  · exact meanBVertexKernel_data_7 p
  · exact meanBVertexKernel_data_8 p
  · exact meanBVertexKernel_data_9 p
  · exact meanBVertexKernel_data_10 p
  · exact meanBVertexKernel_data_11 p
  · exact meanBVertexKernel_data_12 p
  · exact meanBVertexKernel_data_13 p
  · exact meanBVertexKernel_data_14 p
  · exact meanBVertexKernel_data_15 p
#print axioms meanFlatBasis_coordinates
#print axioms meanBVertexKernel_data
end Blueprint.Thomson.Tail.Implementation
