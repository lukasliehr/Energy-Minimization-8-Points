import ThomsonNegative.Certificate.Correction.q05.Witness00
import ThomsonNegative.Certificate.Correction.q05.Witness01
import ThomsonNegative.Certificate.Correction.q05.Witness02
import ThomsonNegative.Certificate.Correction.q05.Witness03
import ThomsonNegative.Certificate.Correction.q05.Witness04
import ThomsonNegative.Certificate.Correction.q05.Witness05
import ThomsonNegative.Certificate.Correction.q05.Witness06
import ThomsonNegative.Certificate.Correction.q05.Witness07
import ThomsonNegative.Certificate.Correction.q05.Witness08
import ThomsonNegative.Certificate.Correction.q05.Witness09
import ThomsonNegative.Certificate.Correction.q05.Witness10
import ThomsonNegative.Certificate.Correction.q05.Witness11
import ThomsonNegative.Certificate.Correction.q05.Witness12
import ThomsonNegative.Certificate.Correction.q05.Witness13
import ThomsonNegative.Certificate.Correction.q05.Witness14
import ThomsonNegative.Certificate.Correction.q05.Witness15
import ThomsonNegative.Certificate.Correction.q05.Witness16

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem witness_certified (r : Fin 68) : RowCertified argument residual (witness r) := by
  fin_cases r
  · exact witness0_certified
  · exact witness1_certified
  · exact witness2_certified
  · exact witness3_certified
  · exact witness4_certified
  · exact witness5_certified
  · exact witness6_certified
  · exact witness7_certified
  · exact witness8_certified
  · exact witness9_certified
  · exact witness10_certified
  · exact witness11_certified
  · exact witness12_certified
  · exact witness13_certified
  · exact witness14_certified
  · exact witness15_certified
  · exact witness16_certified
  · exact witness17_certified
  · exact witness18_certified
  · exact witness19_certified
  · exact witness20_certified
  · exact witness21_certified
  · exact witness22_certified
  · exact witness23_certified
  · exact witness24_certified
  · exact witness25_certified
  · exact witness26_certified
  · exact witness27_certified
  · exact witness28_certified
  · exact witness29_certified
  · exact witness30_certified
  · exact witness31_certified
  · exact witness32_certified
  · exact witness33_certified
  · exact witness34_certified
  · exact witness35_certified
  · exact witness36_certified
  · exact witness37_certified
  · exact witness38_certified
  · exact witness39_certified
  · exact witness40_certified
  · exact witness41_certified
  · exact witness42_certified
  · exact witness43_certified
  · exact witness44_certified
  · exact witness45_certified
  · exact witness46_certified
  · exact witness47_certified
  · exact witness48_certified
  · exact witness49_certified
  · exact witness50_certified
  · exact witness51_certified
  · exact witness52_certified
  · exact witness53_certified
  · exact witness54_certified
  · exact witness55_certified
  · exact witness56_certified
  · exact witness57_certified
  · exact witness58_certified
  · exact witness59_certified
  · exact witness60_certified
  · exact witness61_certified
  · exact witness62_certified
  · exact witness63_certified
  · exact witness64_certified
  · exact witness65_certified
  · exact witness66_certified
  · exact witness67_certified
theorem witness_numerator (r : Fin 68) : (witness r).numerator=Source.rowNumerator r := by
  fin_cases r <;> rfl
theorem witness_denominator (r : Fin 68) : (witness r).denominator=Source.rowDenominator r := by
  fin_cases r <;> rfl
theorem witness_models (r : Fin 68) (k : Nat) : (witness r).models k=rowModel r k := by
  fin_cases r <;> rfl
theorem witness_columns (r : Fin 68) (j : Nat) : (witness r).columns j=rowColumns r j := by
  fin_cases r <;> rfl
end ThomsonNegative.Certificate.Correction.q05
