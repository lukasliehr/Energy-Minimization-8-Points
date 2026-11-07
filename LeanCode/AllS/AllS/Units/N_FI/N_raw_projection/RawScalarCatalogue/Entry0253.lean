import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawScalarCatalogue.Entry0253
open RawCatalogue
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def spec : RawScalarSpec := ⟨2,false,true,true,(3,1,0)⟩
def entry : SparsePoly := [((3,3,0),(4/9:ℚ)),((5,2,0),(-8/27:ℚ)),((7,1,0),(4/81:ℚ))]
def raw81 : List (Tag × ℤ) := [((3,3,0),(36:ℤ)),((5,2,0),(-24:ℤ)),((7,1,0),(4:ℤ))]
theorem normalize_81 : normalizeIntegerRawEntry 81 raw81=entry := by norm_num [normalizeIntegerRawEntry,raw81,entry]
theorem identity : ratToReal (sparsePolynomial entry)=rawScalarCoordinates spec := by
  simp only [rawScalarCoordinates,spec,rawEvenCoordinates,rawOddCoordinates,rawParityCoordinates]
  norm_num only [Finset.sum_range_succ,Finset.sum_empty,Nat.choose_zero_right,Nat.choose_succ_succ]
  try simp only [← PowerSumCatalogue.identity_00,← PowerSumCatalogue.identity_01,← PowerSumCatalogue.identity_02,← PowerSumCatalogue.identity_03,← PowerSumCatalogue.identity_04,← PowerSumCatalogue.identity_05,← PowerSumCatalogue.identity_06,← PowerSumCatalogue.identity_07,← PowerSumCatalogue.identity_08,← PowerSumCatalogue.identity_09,← PowerSumCatalogue.identity_10,← PowerSumCatalogue.identity_11,← PowerSumCatalogue.identity_12,← PowerSumCatalogue.identity_13,← PowerSumCatalogue.identity_14,← PowerSumCatalogue.identity_15,← PowerSumCatalogue.identity_16,← PowerSumCatalogue.identity_17,← PowerSumCatalogue.identity_18,← PairPowerSumCatalogue.identity_00,← PairPowerSumCatalogue.identity_01,← PairPowerSumCatalogue.identity_02,← PairPowerSumCatalogue.identity_03,← PairPowerSumCatalogue.identity_04,← PairPowerSumCatalogue.identity_05,← PairPowerSumCatalogue.identity_06,← PairPowerSumCatalogue.identity_07,← PairPowerSumCatalogue.identity_08,← PairPowerSumCatalogue.identity_09]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,entry,rawSymmetricWeight,rawDeterminantCoordinates,
    rawDiscriminantCoordinates,rawStandardCoordinates,coordinateMonomial,PowerSumCatalogue.p00,PowerSumCatalogue.q00,PowerSumCatalogue.p01,PowerSumCatalogue.q01,PowerSumCatalogue.p02,PowerSumCatalogue.q02,PowerSumCatalogue.p03,PowerSumCatalogue.q03,PowerSumCatalogue.p04,PowerSumCatalogue.q04,PowerSumCatalogue.p05,PowerSumCatalogue.q05,PowerSumCatalogue.p06,PowerSumCatalogue.q06,PowerSumCatalogue.p07,PowerSumCatalogue.q07,PowerSumCatalogue.p08,PowerSumCatalogue.q08,PowerSumCatalogue.p09,PowerSumCatalogue.q09,PowerSumCatalogue.p10,PowerSumCatalogue.q10,PowerSumCatalogue.p11,PowerSumCatalogue.q11,PowerSumCatalogue.p12,PowerSumCatalogue.q12,PowerSumCatalogue.p13,PowerSumCatalogue.q13,PowerSumCatalogue.p14,PowerSumCatalogue.q14,PowerSumCatalogue.p15,PowerSumCatalogue.q15,PowerSumCatalogue.p16,PowerSumCatalogue.q16,PowerSumCatalogue.p17,PowerSumCatalogue.q17,PowerSumCatalogue.p18,PowerSumCatalogue.q18,PairPowerSumCatalogue.p00,PairPowerSumCatalogue.q00,PairPowerSumCatalogue.p01,PairPowerSumCatalogue.q01,PairPowerSumCatalogue.p02,PairPowerSumCatalogue.q02,PairPowerSumCatalogue.p03,PairPowerSumCatalogue.q03,PairPowerSumCatalogue.p04,PairPowerSumCatalogue.q04,PairPowerSumCatalogue.p05,PairPowerSumCatalogue.q05,PairPowerSumCatalogue.p06,PairPowerSumCatalogue.q06,PairPowerSumCatalogue.p07,PairPowerSumCatalogue.q07,PairPowerSumCatalogue.p08,PairPowerSumCatalogue.q08,PairPowerSumCatalogue.p09,PairPowerSumCatalogue.q09]
  all_goals ring
#print axioms identity
end Blueprint.Thomson.Finite.RawScalarCatalogue.Entry0253
