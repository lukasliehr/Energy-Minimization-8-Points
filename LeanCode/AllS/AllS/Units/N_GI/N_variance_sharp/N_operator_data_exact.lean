import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_00
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_01
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_02
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_03
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_04
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_05
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_06
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_07
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_08
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_09
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_10
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_11
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_12
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_13
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_14
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_row_15
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceAFromData_exact (i j : Fin 16) : varianceAFromData i j=
    if ((finProdFinEquiv (m:=8) (n:=2)).symm i).1=((finProdFinEquiv (m:=8) (n:=2)).symm j).1 then
      varianceBlockAData ((finProdFinEquiv (m:=8) (n:=2)).symm i).1
        ((finProdFinEquiv (m:=8) (n:=2)).symm i).2 ((finProdFinEquiv (m:=8) (n:=2)).symm j).2 else 0 := by
  fin_cases i
  · exact varianceAFromData_exact_00 j
  · exact varianceAFromData_exact_01 j
  · exact varianceAFromData_exact_02 j
  · exact varianceAFromData_exact_03 j
  · exact varianceAFromData_exact_04 j
  · exact varianceAFromData_exact_05 j
  · exact varianceAFromData_exact_06 j
  · exact varianceAFromData_exact_07 j
  · exact varianceAFromData_exact_08 j
  · exact varianceAFromData_exact_09 j
  · exact varianceAFromData_exact_10 j
  · exact varianceAFromData_exact_11 j
  · exact varianceAFromData_exact_12 j
  · exact varianceAFromData_exact_13 j
  · exact varianceAFromData_exact_14 j
  · exact varianceAFromData_exact_15 j
#print axioms varianceAFromData_exact
end Blueprint.Thomson.Tail.Implementation
