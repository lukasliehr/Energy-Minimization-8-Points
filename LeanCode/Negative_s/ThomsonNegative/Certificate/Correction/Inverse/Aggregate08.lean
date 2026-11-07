import ThomsonNegative.Certificate.Correction.Inverse.AggregateSound
import ThomsonNegative.Certificate.Correction.Inverse.RowCheck64
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_0
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_1
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_2
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_3
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_4
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_5
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_6
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_7
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck64_8
import ThomsonNegative.Certificate.Correction.Inverse.ShiftCheck64_0
import ThomsonNegative.Certificate.Correction.Inverse.RowCheck65
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_0
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_1
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_2
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_3
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_4
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_5
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_6
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_7
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck65_8
import ThomsonNegative.Certificate.Correction.Inverse.ShiftCheck65_0
import ThomsonNegative.Certificate.Correction.Inverse.RowCheck66
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_0
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_1
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_2
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_3
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_4
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_5
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_6
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_7
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck66_8
import ThomsonNegative.Certificate.Correction.Inverse.ShiftCheck66_0
import ThomsonNegative.Certificate.Correction.Inverse.RowCheck67
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_0
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_1
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_2
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_3
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_4
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_5
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_6
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_7
import ThomsonNegative.Certificate.Correction.Inverse.EntryCheck67_8
import ThomsonNegative.Certificate.Correction.Inverse.ShiftCheck67_0

namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem shift_row_64 (j : Fin 68) : shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 64 j) (shiftANumerator 64 j)=true := by
  have hj := j.isLt
  exact segment_true (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 64 k) (shiftANumerator 64 k)) 0 68 shift_checked_64_0 j (by omega) (by omega)
theorem lift_row_64 (j : Fin 68) : (liftEquation 64 j).check=true := allBelow_spec _ _ lifts_checked_64 j j.isLt
theorem inverse_row_64 (j : Fin 68) : (inverseEquation 64 j).check=true := by
  have hj := j.isLt
  by_cases h0 : j.val<8
  · exact segment_true (fun k => (inverseEquation 64 k).check) 0 8 inverse_checked_64_0 j (by omega) h0
  by_cases h1 : j.val<16
  · exact segment_true (fun k => (inverseEquation 64 k).check) 8 8 inverse_checked_64_1 j (by omega) h1
  by_cases h2 : j.val<24
  · exact segment_true (fun k => (inverseEquation 64 k).check) 16 8 inverse_checked_64_2 j (by omega) h2
  by_cases h3 : j.val<32
  · exact segment_true (fun k => (inverseEquation 64 k).check) 24 8 inverse_checked_64_3 j (by omega) h3
  by_cases h4 : j.val<40
  · exact segment_true (fun k => (inverseEquation 64 k).check) 32 8 inverse_checked_64_4 j (by omega) h4
  by_cases h5 : j.val<48
  · exact segment_true (fun k => (inverseEquation 64 k).check) 40 8 inverse_checked_64_5 j (by omega) h5
  by_cases h6 : j.val<56
  · exact segment_true (fun k => (inverseEquation 64 k).check) 48 8 inverse_checked_64_6 j (by omega) h6
  by_cases h7 : j.val<64
  · exact segment_true (fun k => (inverseEquation 64 k).check) 56 8 inverse_checked_64_7 j (by omega) h7
  exact segment_true (fun k => (inverseEquation 64 k).check) 64 4 inverse_checked_64_8 j (by omega) (by omega)
theorem shift_row_65 (j : Fin 68) : shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 65 j) (shiftANumerator 65 j)=true := by
  have hj := j.isLt
  exact segment_true (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 65 k) (shiftANumerator 65 k)) 0 68 shift_checked_65_0 j (by omega) (by omega)
theorem lift_row_65 (j : Fin 68) : (liftEquation 65 j).check=true := allBelow_spec _ _ lifts_checked_65 j j.isLt
theorem inverse_row_65 (j : Fin 68) : (inverseEquation 65 j).check=true := by
  have hj := j.isLt
  by_cases h0 : j.val<8
  · exact segment_true (fun k => (inverseEquation 65 k).check) 0 8 inverse_checked_65_0 j (by omega) h0
  by_cases h1 : j.val<16
  · exact segment_true (fun k => (inverseEquation 65 k).check) 8 8 inverse_checked_65_1 j (by omega) h1
  by_cases h2 : j.val<24
  · exact segment_true (fun k => (inverseEquation 65 k).check) 16 8 inverse_checked_65_2 j (by omega) h2
  by_cases h3 : j.val<32
  · exact segment_true (fun k => (inverseEquation 65 k).check) 24 8 inverse_checked_65_3 j (by omega) h3
  by_cases h4 : j.val<40
  · exact segment_true (fun k => (inverseEquation 65 k).check) 32 8 inverse_checked_65_4 j (by omega) h4
  by_cases h5 : j.val<48
  · exact segment_true (fun k => (inverseEquation 65 k).check) 40 8 inverse_checked_65_5 j (by omega) h5
  by_cases h6 : j.val<56
  · exact segment_true (fun k => (inverseEquation 65 k).check) 48 8 inverse_checked_65_6 j (by omega) h6
  by_cases h7 : j.val<64
  · exact segment_true (fun k => (inverseEquation 65 k).check) 56 8 inverse_checked_65_7 j (by omega) h7
  exact segment_true (fun k => (inverseEquation 65 k).check) 64 4 inverse_checked_65_8 j (by omega) (by omega)
theorem shift_row_66 (j : Fin 68) : shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 66 j) (shiftANumerator 66 j)=true := by
  have hj := j.isLt
  exact segment_true (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 66 k) (shiftANumerator 66 k)) 0 68 shift_checked_66_0 j (by omega) (by omega)
theorem lift_row_66 (j : Fin 68) : (liftEquation 66 j).check=true := allBelow_spec _ _ lifts_checked_66 j j.isLt
theorem inverse_row_66 (j : Fin 68) : (inverseEquation 66 j).check=true := by
  have hj := j.isLt
  by_cases h0 : j.val<8
  · exact segment_true (fun k => (inverseEquation 66 k).check) 0 8 inverse_checked_66_0 j (by omega) h0
  by_cases h1 : j.val<16
  · exact segment_true (fun k => (inverseEquation 66 k).check) 8 8 inverse_checked_66_1 j (by omega) h1
  by_cases h2 : j.val<24
  · exact segment_true (fun k => (inverseEquation 66 k).check) 16 8 inverse_checked_66_2 j (by omega) h2
  by_cases h3 : j.val<32
  · exact segment_true (fun k => (inverseEquation 66 k).check) 24 8 inverse_checked_66_3 j (by omega) h3
  by_cases h4 : j.val<40
  · exact segment_true (fun k => (inverseEquation 66 k).check) 32 8 inverse_checked_66_4 j (by omega) h4
  by_cases h5 : j.val<48
  · exact segment_true (fun k => (inverseEquation 66 k).check) 40 8 inverse_checked_66_5 j (by omega) h5
  by_cases h6 : j.val<56
  · exact segment_true (fun k => (inverseEquation 66 k).check) 48 8 inverse_checked_66_6 j (by omega) h6
  by_cases h7 : j.val<64
  · exact segment_true (fun k => (inverseEquation 66 k).check) 56 8 inverse_checked_66_7 j (by omega) h7
  exact segment_true (fun k => (inverseEquation 66 k).check) 64 4 inverse_checked_66_8 j (by omega) (by omega)
theorem shift_row_67 (j : Fin 68) : shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 67 j) (shiftANumerator 67 j)=true := by
  have hj := j.isLt
  exact segment_true (fun k => shiftCheck shiftDegree (Structure.Factored.HighData.A.numerator 67 k) (shiftANumerator 67 k)) 0 68 shift_checked_67_0 j (by omega) (by omega)
theorem lift_row_67 (j : Fin 68) : (liftEquation 67 j).check=true := allBelow_spec _ _ lifts_checked_67 j j.isLt
theorem inverse_row_67 (j : Fin 68) : (inverseEquation 67 j).check=true := by
  have hj := j.isLt
  by_cases h0 : j.val<8
  · exact segment_true (fun k => (inverseEquation 67 k).check) 0 8 inverse_checked_67_0 j (by omega) h0
  by_cases h1 : j.val<16
  · exact segment_true (fun k => (inverseEquation 67 k).check) 8 8 inverse_checked_67_1 j (by omega) h1
  by_cases h2 : j.val<24
  · exact segment_true (fun k => (inverseEquation 67 k).check) 16 8 inverse_checked_67_2 j (by omega) h2
  by_cases h3 : j.val<32
  · exact segment_true (fun k => (inverseEquation 67 k).check) 24 8 inverse_checked_67_3 j (by omega) h3
  by_cases h4 : j.val<40
  · exact segment_true (fun k => (inverseEquation 67 k).check) 32 8 inverse_checked_67_4 j (by omega) h4
  by_cases h5 : j.val<48
  · exact segment_true (fun k => (inverseEquation 67 k).check) 40 8 inverse_checked_67_5 j (by omega) h5
  by_cases h6 : j.val<56
  · exact segment_true (fun k => (inverseEquation 67 k).check) 48 8 inverse_checked_67_6 j (by omega) h6
  by_cases h7 : j.val<64
  · exact segment_true (fun k => (inverseEquation 67 k).check) 56 8 inverse_checked_67_7 j (by omega) h7
  exact segment_true (fun k => (inverseEquation 67 k).check) 64 4 inverse_checked_67_8 j (by omega) (by omega)
end ThomsonNegative.Certificate.Correction.Inverse
