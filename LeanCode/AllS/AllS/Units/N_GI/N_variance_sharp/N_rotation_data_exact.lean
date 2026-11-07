import AllS.Units.N_GI.N_variance_sharp.N_rotation_coeff_0
import AllS.Units.N_GI.N_variance_sharp.N_rotation_coeff_1
import AllS.Units.N_GI.N_variance_sharp.N_rotation_coeff_2
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_00
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_01
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_02
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_03
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_04
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_05
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_06
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_07
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_08
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_09
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_10
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_11
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_12
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_13
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_14
import AllS.Units.N_GI.N_variance_sharp.N_projectedM_symm_15
import AllS.Units.N_GI.N_variance_sharp.N_rotation_table_checks
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceRotationCoeffData_exact (j : Fin 3) (i : Fin 16) : varianceRotationCoeffKernel j i=varianceRotationCoeffData j i := by
  fin_cases j
  · exact varianceRotationCoeffData_exact_0 i
  · exact varianceRotationCoeffData_exact_1 i
  · exact varianceRotationCoeffData_exact_2 i
theorem varianceProjectedMData_symm (e i j : Fin 16) : varianceProjectedMData e i j=varianceProjectedMData e j i := by
  fin_cases e
  · exact varianceProjectedMData_symm_00 i j
  · exact varianceProjectedMData_symm_01 i j
  · exact varianceProjectedMData_symm_02 i j
  · exact varianceProjectedMData_symm_03 i j
  · exact varianceProjectedMData_symm_04 i j
  · exact varianceProjectedMData_symm_05 i j
  · exact varianceProjectedMData_symm_06 i j
  · exact varianceProjectedMData_symm_07 i j
  · exact varianceProjectedMData_symm_08 i j
  · exact varianceProjectedMData_symm_09 i j
  · exact varianceProjectedMData_symm_10 i j
  · exact varianceProjectedMData_symm_11 i j
  · exact varianceProjectedMData_symm_12 i j
  · exact varianceProjectedMData_symm_13 i j
  · exact varianceProjectedMData_symm_14 i j
  · exact varianceProjectedMData_symm_15 i j
#print axioms varianceRotationCoeffData_exact
#print axioms varianceProjectedMData_symm
end Blueprint.Thomson.Tail.Implementation
