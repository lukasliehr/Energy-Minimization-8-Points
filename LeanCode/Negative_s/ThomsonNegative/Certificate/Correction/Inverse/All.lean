import ThomsonNegative.Certificate.Correction.Inverse.CommonChecks
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate00
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate01
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate02
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate03
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate04
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate05
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate06
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate07
import ThomsonNegative.Certificate.Correction.Inverse.Aggregate08

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem denominator_checks (j : Fin 68) : (denominatorEquation j).check=true := allBelow_spec _ _ denominators_checked j j.isLt
theorem lift_checks (i j : Fin 68) : (liftEquation i j).check=true := by
  fin_cases i
  · exact lift_row_0 j
  · exact lift_row_1 j
  · exact lift_row_2 j
  · exact lift_row_3 j
  · exact lift_row_4 j
  · exact lift_row_5 j
  · exact lift_row_6 j
  · exact lift_row_7 j
  · exact lift_row_8 j
  · exact lift_row_9 j
  · exact lift_row_10 j
  · exact lift_row_11 j
  · exact lift_row_12 j
  · exact lift_row_13 j
  · exact lift_row_14 j
  · exact lift_row_15 j
  · exact lift_row_16 j
  · exact lift_row_17 j
  · exact lift_row_18 j
  · exact lift_row_19 j
  · exact lift_row_20 j
  · exact lift_row_21 j
  · exact lift_row_22 j
  · exact lift_row_23 j
  · exact lift_row_24 j
  · exact lift_row_25 j
  · exact lift_row_26 j
  · exact lift_row_27 j
  · exact lift_row_28 j
  · exact lift_row_29 j
  · exact lift_row_30 j
  · exact lift_row_31 j
  · exact lift_row_32 j
  · exact lift_row_33 j
  · exact lift_row_34 j
  · exact lift_row_35 j
  · exact lift_row_36 j
  · exact lift_row_37 j
  · exact lift_row_38 j
  · exact lift_row_39 j
  · exact lift_row_40 j
  · exact lift_row_41 j
  · exact lift_row_42 j
  · exact lift_row_43 j
  · exact lift_row_44 j
  · exact lift_row_45 j
  · exact lift_row_46 j
  · exact lift_row_47 j
  · exact lift_row_48 j
  · exact lift_row_49 j
  · exact lift_row_50 j
  · exact lift_row_51 j
  · exact lift_row_52 j
  · exact lift_row_53 j
  · exact lift_row_54 j
  · exact lift_row_55 j
  · exact lift_row_56 j
  · exact lift_row_57 j
  · exact lift_row_58 j
  · exact lift_row_59 j
  · exact lift_row_60 j
  · exact lift_row_61 j
  · exact lift_row_62 j
  · exact lift_row_63 j
  · exact lift_row_64 j
  · exact lift_row_65 j
  · exact lift_row_66 j
  · exact lift_row_67 j
theorem inverse_checks (i j : Fin 68) : (inverseEquation i j).check=true := by
  fin_cases i
  · exact inverse_row_0 j
  · exact inverse_row_1 j
  · exact inverse_row_2 j
  · exact inverse_row_3 j
  · exact inverse_row_4 j
  · exact inverse_row_5 j
  · exact inverse_row_6 j
  · exact inverse_row_7 j
  · exact inverse_row_8 j
  · exact inverse_row_9 j
  · exact inverse_row_10 j
  · exact inverse_row_11 j
  · exact inverse_row_12 j
  · exact inverse_row_13 j
  · exact inverse_row_14 j
  · exact inverse_row_15 j
  · exact inverse_row_16 j
  · exact inverse_row_17 j
  · exact inverse_row_18 j
  · exact inverse_row_19 j
  · exact inverse_row_20 j
  · exact inverse_row_21 j
  · exact inverse_row_22 j
  · exact inverse_row_23 j
  · exact inverse_row_24 j
  · exact inverse_row_25 j
  · exact inverse_row_26 j
  · exact inverse_row_27 j
  · exact inverse_row_28 j
  · exact inverse_row_29 j
  · exact inverse_row_30 j
  · exact inverse_row_31 j
  · exact inverse_row_32 j
  · exact inverse_row_33 j
  · exact inverse_row_34 j
  · exact inverse_row_35 j
  · exact inverse_row_36 j
  · exact inverse_row_37 j
  · exact inverse_row_38 j
  · exact inverse_row_39 j
  · exact inverse_row_40 j
  · exact inverse_row_41 j
  · exact inverse_row_42 j
  · exact inverse_row_43 j
  · exact inverse_row_44 j
  · exact inverse_row_45 j
  · exact inverse_row_46 j
  · exact inverse_row_47 j
  · exact inverse_row_48 j
  · exact inverse_row_49 j
  · exact inverse_row_50 j
  · exact inverse_row_51 j
  · exact inverse_row_52 j
  · exact inverse_row_53 j
  · exact inverse_row_54 j
  · exact inverse_row_55 j
  · exact inverse_row_56 j
  · exact inverse_row_57 j
  · exact inverse_row_58 j
  · exact inverse_row_59 j
  · exact inverse_row_60 j
  · exact inverse_row_61 j
  · exact inverse_row_62 j
  · exact inverse_row_63 j
  · exact inverse_row_64 j
  · exact inverse_row_65 j
  · exact inverse_row_66 j
  · exact inverse_row_67 j
theorem shift_numerator_checks (i j : Fin 68) : shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator i j) (shiftANumerator i j)=true := by
  fin_cases i
  · exact shift_row_0 j
  · exact shift_row_1 j
  · exact shift_row_2 j
  · exact shift_row_3 j
  · exact shift_row_4 j
  · exact shift_row_5 j
  · exact shift_row_6 j
  · exact shift_row_7 j
  · exact shift_row_8 j
  · exact shift_row_9 j
  · exact shift_row_10 j
  · exact shift_row_11 j
  · exact shift_row_12 j
  · exact shift_row_13 j
  · exact shift_row_14 j
  · exact shift_row_15 j
  · exact shift_row_16 j
  · exact shift_row_17 j
  · exact shift_row_18 j
  · exact shift_row_19 j
  · exact shift_row_20 j
  · exact shift_row_21 j
  · exact shift_row_22 j
  · exact shift_row_23 j
  · exact shift_row_24 j
  · exact shift_row_25 j
  · exact shift_row_26 j
  · exact shift_row_27 j
  · exact shift_row_28 j
  · exact shift_row_29 j
  · exact shift_row_30 j
  · exact shift_row_31 j
  · exact shift_row_32 j
  · exact shift_row_33 j
  · exact shift_row_34 j
  · exact shift_row_35 j
  · exact shift_row_36 j
  · exact shift_row_37 j
  · exact shift_row_38 j
  · exact shift_row_39 j
  · exact shift_row_40 j
  · exact shift_row_41 j
  · exact shift_row_42 j
  · exact shift_row_43 j
  · exact shift_row_44 j
  · exact shift_row_45 j
  · exact shift_row_46 j
  · exact shift_row_47 j
  · exact shift_row_48 j
  · exact shift_row_49 j
  · exact shift_row_50 j
  · exact shift_row_51 j
  · exact shift_row_52 j
  · exact shift_row_53 j
  · exact shift_row_54 j
  · exact shift_row_55 j
  · exact shift_row_56 j
  · exact shift_row_57 j
  · exact shift_row_58 j
  · exact shift_row_59 j
  · exact shift_row_60 j
  · exact shift_row_61 j
  · exact shift_row_62 j
  · exact shift_row_63 j
  · exact shift_row_64 j
  · exact shift_row_65 j
  · exact shift_row_66 j
  · exact shift_row_67 j
#print axioms inverse_checks
#print axioms shift_numerator_checks
end ThomsonNegative.Certificate.Correction.Inverse
