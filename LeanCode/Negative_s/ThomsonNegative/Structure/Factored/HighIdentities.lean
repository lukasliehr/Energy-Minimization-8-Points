import ThomsonNegative.Structure.Factored.HighDenominators
import ThomsonNegative.Structure.Packed.MatrixSound
import ThomsonNegative.Structure.Factored.high3.Column00
import ThomsonNegative.Structure.Factored.high3.Column01
import ThomsonNegative.Structure.Factored.high3.Column02
import ThomsonNegative.Structure.Factored.high14.Column00
import ThomsonNegative.Structure.Factored.high14.Column01
import ThomsonNegative.Structure.Factored.high14.Column02
import ThomsonNegative.Structure.Factored.high14.Column03
import ThomsonNegative.Structure.Factored.high14.Column04
import ThomsonNegative.Structure.Factored.high14.Column05
import ThomsonNegative.Structure.Factored.high14.Column06
import ThomsonNegative.Structure.Factored.high14.Column07
import ThomsonNegative.Structure.Factored.high14.Column08
import ThomsonNegative.Structure.Factored.high14.Column09
import ThomsonNegative.Structure.Factored.high14.Column10
import ThomsonNegative.Structure.Factored.high14.Column11
import ThomsonNegative.Structure.Factored.high14.Column12
import ThomsonNegative.Structure.Factored.high14.Column13
import ThomsonNegative.Structure.Factored.insert15.Column00
import ThomsonNegative.Structure.Factored.insert15.Column01
import ThomsonNegative.Structure.Factored.insert15.Column02
import ThomsonNegative.Structure.Factored.insert15.Column03
import ThomsonNegative.Structure.Factored.insert15.Column04
import ThomsonNegative.Structure.Factored.insert15.Column05
import ThomsonNegative.Structure.Factored.insert15.Column06
import ThomsonNegative.Structure.Factored.insert15.Column07
import ThomsonNegative.Structure.Factored.insert15.Column08
import ThomsonNegative.Structure.Factored.insert15.Column09
import ThomsonNegative.Structure.Factored.insert15.Column10
import ThomsonNegative.Structure.Factored.insert15.Column11
import ThomsonNegative.Structure.Factored.insert15.Column12
import ThomsonNegative.Structure.Factored.insert15.Column13
import ThomsonNegative.Structure.Factored.insert15.Column14
import ThomsonNegative.Structure.Factored.insert36.Column00
import ThomsonNegative.Structure.Factored.insert36.Column01
import ThomsonNegative.Structure.Factored.insert36.Column02
import ThomsonNegative.Structure.Factored.insert36.Column03
import ThomsonNegative.Structure.Factored.insert36.Column04
import ThomsonNegative.Structure.Factored.insert36.Column05
import ThomsonNegative.Structure.Factored.insert36.Column06
import ThomsonNegative.Structure.Factored.insert36.Column07
import ThomsonNegative.Structure.Factored.insert36.Column08
import ThomsonNegative.Structure.Factored.insert36.Column09
import ThomsonNegative.Structure.Factored.insert36.Column10
import ThomsonNegative.Structure.Factored.insert36.Column11
import ThomsonNegative.Structure.Factored.insert36.Column12
import ThomsonNegative.Structure.Factored.insert36.Column13
import ThomsonNegative.Structure.Factored.insert36.Column14
import ThomsonNegative.Structure.Factored.insert36.Column15
import ThomsonNegative.Structure.Factored.insert36.Column16
import ThomsonNegative.Structure.Factored.insert36.Column17
import ThomsonNegative.Structure.Factored.insert36.Column18
import ThomsonNegative.Structure.Factored.insert36.Column19
import ThomsonNegative.Structure.Factored.insert36.Column20
import ThomsonNegative.Structure.Factored.insert36.Column21
import ThomsonNegative.Structure.Factored.insert36.Column22
import ThomsonNegative.Structure.Factored.insert36.Column23
import ThomsonNegative.Structure.Factored.insert36.Column24
import ThomsonNegative.Structure.Factored.insert36.Column25
import ThomsonNegative.Structure.Factored.insert36.Column26
import ThomsonNegative.Structure.Factored.insert36.Column27
import ThomsonNegative.Structure.Factored.insert36.Column28
import ThomsonNegative.Structure.Factored.insert36.Column29
import ThomsonNegative.Structure.Factored.insert36.Column30
import ThomsonNegative.Structure.Factored.insert36.Column31
import ThomsonNegative.Structure.Factored.insert36.Column32
import ThomsonNegative.Structure.Factored.insert36.Column33
import ThomsonNegative.Structure.Factored.insert36.Column34
import ThomsonNegative.Structure.Factored.insert36.Column35
noncomputable section
namespace ThomsonNegative.Structure.Factored
open ThomsonNegative.Structure.Exact
theorem high3_identity (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    HighData.A.eval a * HighData.K3.eval a=HighData.H3.eval a := by
  apply product_matrix_sound _ _ _ 202 30 61 a
    (A_regular a ha hb) (K3_regular a ha hb) (H3_regular a ha hb)
  intro j
  fin_cases j
  · exact high3.column_0
  · exact high3.column_1
  · exact high3.column_2
theorem high14_identity (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    HighData.A.eval a * HighData.K14.eval a=HighData.H14.eval a := by
  apply product_matrix_sound _ _ _ 202 30 61 a
    (A_regular a ha hb) (K14_regular a ha hb) (H14_regular a ha hb)
  intro j
  fin_cases j
  · exact high14.column_0
  · exact high14.column_1
  · exact high14.column_2
  · exact high14.column_3
  · exact high14.column_4
  · exact high14.column_5
  · exact high14.column_6
  · exact high14.column_7
  · exact high14.column_8
  · exact high14.column_9
  · exact high14.column_10
  · exact high14.column_11
  · exact high14.column_12
  · exact high14.column_13
theorem insert15_identity (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    HighData.A.eval a * HighData.K15.eval a=HighData.LP.eval a := by
  apply product_matrix_sound _ _ _ 202 30 61 a
    (A_regular a ha hb) (K15_regular a ha hb) (LP_regular a ha hb)
  intro j
  fin_cases j
  · exact insert15.column_0
  · exact insert15.column_1
  · exact insert15.column_2
  · exact insert15.column_3
  · exact insert15.column_4
  · exact insert15.column_5
  · exact insert15.column_6
  · exact insert15.column_7
  · exact insert15.column_8
  · exact insert15.column_9
  · exact insert15.column_10
  · exact insert15.column_11
  · exact insert15.column_12
  · exact insert15.column_13
  · exact insert15.column_14
theorem insert36_identity (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    HighData.A.eval a * HighData.K36.eval a=HighData.LS.eval a := by
  apply product_matrix_sound _ _ _ 202 30 61 a
    (A_regular a ha hb) (K36_regular a ha hb) (LS_regular a ha hb)
  intro j
  fin_cases j
  · exact insert36.column_0
  · exact insert36.column_1
  · exact insert36.column_2
  · exact insert36.column_3
  · exact insert36.column_4
  · exact insert36.column_5
  · exact insert36.column_6
  · exact insert36.column_7
  · exact insert36.column_8
  · exact insert36.column_9
  · exact insert36.column_10
  · exact insert36.column_11
  · exact insert36.column_12
  · exact insert36.column_13
  · exact insert36.column_14
  · exact insert36.column_15
  · exact insert36.column_16
  · exact insert36.column_17
  · exact insert36.column_18
  · exact insert36.column_19
  · exact insert36.column_20
  · exact insert36.column_21
  · exact insert36.column_22
  · exact insert36.column_23
  · exact insert36.column_24
  · exact insert36.column_25
  · exact insert36.column_26
  · exact insert36.column_27
  · exact insert36.column_28
  · exact insert36.column_29
  · exact insert36.column_30
  · exact insert36.column_31
  · exact insert36.column_32
  · exact insert36.column_33
  · exact insert36.column_34
  · exact insert36.column_35
end ThomsonNegative.Structure.Factored
