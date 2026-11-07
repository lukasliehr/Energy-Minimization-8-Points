import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_00
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_01
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_02
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_03
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_04
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_05
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_06
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_07
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_08
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_09
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_10
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_11
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_12
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_13
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_14
import AllS.Units.N_GI.N_variance_sharp.N_physical_data_row_15
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact (e : ContactIndex) (i : Fin 16) : varianceLinearKernel e i=varianceLinearData (finProdFinEquiv e) i := by
  rcases e with ⟨p,b⟩
  fin_cases p <;> fin_cases b
  · exact varianceLinearData_exact_00 i
  · exact varianceLinearData_exact_01 i
  · exact varianceLinearData_exact_02 i
  · exact varianceLinearData_exact_03 i
  · exact varianceLinearData_exact_04 i
  · exact varianceLinearData_exact_05 i
  · exact varianceLinearData_exact_06 i
  · exact varianceLinearData_exact_07 i
  · exact varianceLinearData_exact_08 i
  · exact varianceLinearData_exact_09 i
  · exact varianceLinearData_exact_10 i
  · exact varianceLinearData_exact_11 i
  · exact varianceLinearData_exact_12 i
  · exact varianceLinearData_exact_13 i
  · exact varianceLinearData_exact_14 i
  · exact varianceLinearData_exact_15 i
#print axioms varianceLinearData_exact
theorem varianceMData_exact (e : ContactIndex) (i j : Fin 16) : varianceMKernel e i j=varianceMData (finProdFinEquiv e) i j := by
  rcases e with ⟨p,b⟩
  fin_cases p <;> fin_cases b
  · exact varianceMData_exact_00 i j
  · exact varianceMData_exact_01 i j
  · exact varianceMData_exact_02 i j
  · exact varianceMData_exact_03 i j
  · exact varianceMData_exact_04 i j
  · exact varianceMData_exact_05 i j
  · exact varianceMData_exact_06 i j
  · exact varianceMData_exact_07 i j
  · exact varianceMData_exact_08 i j
  · exact varianceMData_exact_09 i j
  · exact varianceMData_exact_10 i j
  · exact varianceMData_exact_11 i j
  · exact varianceMData_exact_12 i j
  · exact varianceMData_exact_13 i j
  · exact varianceMData_exact_14 i j
  · exact varianceMData_exact_15 i j
#print axioms varianceMData_exact
theorem varianceProjectedLinearData_exact (e i : Fin 16) : varianceProjectedLinearFromData e i=varianceProjectedLinearData e i := by
  fin_cases e
  · exact varianceProjectedLinearData_exact_00 i
  · exact varianceProjectedLinearData_exact_01 i
  · exact varianceProjectedLinearData_exact_02 i
  · exact varianceProjectedLinearData_exact_03 i
  · exact varianceProjectedLinearData_exact_04 i
  · exact varianceProjectedLinearData_exact_05 i
  · exact varianceProjectedLinearData_exact_06 i
  · exact varianceProjectedLinearData_exact_07 i
  · exact varianceProjectedLinearData_exact_08 i
  · exact varianceProjectedLinearData_exact_09 i
  · exact varianceProjectedLinearData_exact_10 i
  · exact varianceProjectedLinearData_exact_11 i
  · exact varianceProjectedLinearData_exact_12 i
  · exact varianceProjectedLinearData_exact_13 i
  · exact varianceProjectedLinearData_exact_14 i
  · exact varianceProjectedLinearData_exact_15 i
#print axioms varianceProjectedLinearData_exact
theorem varianceProjectedMData_exact (e i j : Fin 16) : varianceProjectedMFromData e i j=varianceProjectedMData e i j := by
  fin_cases e
  · exact varianceProjectedMData_exact_00 i j
  · exact varianceProjectedMData_exact_01 i j
  · exact varianceProjectedMData_exact_02 i j
  · exact varianceProjectedMData_exact_03 i j
  · exact varianceProjectedMData_exact_04 i j
  · exact varianceProjectedMData_exact_05 i j
  · exact varianceProjectedMData_exact_06 i j
  · exact varianceProjectedMData_exact_07 i j
  · exact varianceProjectedMData_exact_08 i j
  · exact varianceProjectedMData_exact_09 i j
  · exact varianceProjectedMData_exact_10 i j
  · exact varianceProjectedMData_exact_11 i j
  · exact varianceProjectedMData_exact_12 i j
  · exact varianceProjectedMData_exact_13 i j
  · exact varianceProjectedMData_exact_14 i j
  · exact varianceProjectedMData_exact_15 i j
#print axioms varianceProjectedMData_exact
end Blueprint.Thomson.Tail.Implementation
