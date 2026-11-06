import AllS.Units.N_FI.N_raw_projection.RawScalarSupport
noncomputable section
namespace Blueprint.Thomson.Finite.PairPowerSumCatalogue
open RawCatalogue
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def p00 : SparsePoly := [((0,0,0),(3:ℚ))]
def q00 : Poly3 := ratToReal (sparsePolynomial p00)
theorem identity_00 : q00=rawInvariantPairPowerSum 0 := by
  rw [rawInvariantPairPowerSum]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q00,p00]
  all_goals ring
#print axioms identity_00
def p01 : SparsePoly := [((0,1,0),(1:ℚ))]
def q01 : Poly3 := ratToReal (sparsePolynomial p01)
theorem identity_01 : q01=rawInvariantPairPowerSum 1 := by
  rw [rawInvariantPairPowerSum]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q01,p01]
  all_goals ring
#print axioms identity_01
def p02 : SparsePoly := [((0,2,0),(1:ℚ)),((1,0,1),(-2:ℚ))]
def q02 : Poly3 := ratToReal (sparsePolynomial p02)
theorem identity_02 : q02=rawInvariantPairPowerSum 2 := by
  rw [rawInvariantPairPowerSum]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q02,p02]
  all_goals ring
#print axioms identity_02
def p03 : SparsePoly := [((0,0,2),(3:ℚ)),((0,3,0),(1:ℚ)),((1,1,1),(-3:ℚ))]
def q03 : Poly3 := ratToReal (sparsePolynomial p03)
theorem identity_03 : q03=rawInvariantPairPowerSum 3 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_02,← identity_01,← identity_00]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q03,p03,q02,p02,q01,p01,q00,p00]
  all_goals ring
#print axioms identity_03
def p04 : SparsePoly := [((0,1,2),(4:ℚ)),((0,4,0),(1:ℚ)),((1,2,1),(-4:ℚ)),((2,0,2),(2:ℚ))]
def q04 : Poly3 := ratToReal (sparsePolynomial p04)
theorem identity_04 : q04=rawInvariantPairPowerSum 4 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_03,← identity_02,← identity_01]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q04,p04,q03,p03,q02,p02,q01,p01]
  all_goals ring
#print axioms identity_04
def p05 : SparsePoly := [((0,2,2),(5:ℚ)),((0,5,0),(1:ℚ)),((1,0,3),(-5:ℚ)),((1,3,1),(-5:ℚ)),((2,1,2),(5:ℚ))]
def q05 : Poly3 := ratToReal (sparsePolynomial p05)
theorem identity_05 : q05=rawInvariantPairPowerSum 5 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_04,← identity_03,← identity_02]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q05,p05,q04,p04,q03,p03,q02,p02]
  all_goals ring
#print axioms identity_05
def p06 : SparsePoly := [((0,0,4),(3:ℚ)),((0,3,2),(6:ℚ)),((0,6,0),(1:ℚ)),((1,1,3),(-12:ℚ)),((1,4,1),(-6:ℚ)),((2,2,2),(9:ℚ)),((3,0,3),(-2:ℚ))]
def q06 : Poly3 := ratToReal (sparsePolynomial p06)
theorem identity_06 : q06=rawInvariantPairPowerSum 6 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_05,← identity_04,← identity_03]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q06,p06,q05,p05,q04,p04,q03,p03]
  all_goals ring
#print axioms identity_06
def p07 : SparsePoly := [((0,1,4),(7:ℚ)),((0,4,2),(7:ℚ)),((0,7,0),(1:ℚ)),((1,2,3),(-21:ℚ)),((1,5,1),(-7:ℚ)),((2,0,4),(7:ℚ)),((2,3,2),(14:ℚ)),((3,1,3),(-7:ℚ))]
def q07 : Poly3 := ratToReal (sparsePolynomial p07)
theorem identity_07 : q07=rawInvariantPairPowerSum 7 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_06,← identity_05,← identity_04]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q07,p07,q06,p06,q05,p05,q04,p04]
  all_goals ring
#print axioms identity_07
def p08 : SparsePoly := [((0,2,4),(12:ℚ)),((0,5,2),(8:ℚ)),((0,8,0),(1:ℚ)),((1,0,5),(-8:ℚ)),((1,3,3),(-32:ℚ)),((1,6,1),(-8:ℚ)),((2,1,4),(24:ℚ)),((2,4,2),(20:ℚ)),((3,2,3),(-16:ℚ)),((4,0,4),(2:ℚ))]
def q08 : Poly3 := ratToReal (sparsePolynomial p08)
theorem identity_08 : q08=rawInvariantPairPowerSum 8 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_07,← identity_06,← identity_05]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q08,p08,q07,p07,q06,p06,q05,p05]
  all_goals ring
#print axioms identity_08
def p09 : SparsePoly := [((0,0,6),(3:ℚ)),((0,3,4),(18:ℚ)),((0,6,2),(9:ℚ)),((0,9,0),(1:ℚ)),((1,1,5),(-27:ℚ)),((1,4,3),(-45:ℚ)),((1,7,1),(-9:ℚ)),((2,2,4),(54:ℚ)),((2,5,2),(27:ℚ)),((3,0,5),(-9:ℚ)),((3,3,3),(-30:ℚ)),((4,1,4),(9:ℚ))]
def q09 : Poly3 := ratToReal (sparsePolynomial p09)
theorem identity_09 : q09=rawInvariantPairPowerSum 9 := by
  rw [rawInvariantPairPowerSum]
  rw [← identity_08,← identity_07,← identity_06]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q09,p09,q08,p08,q07,p07,q06,p06]
  all_goals ring
#print axioms identity_09
end Blueprint.Thomson.Finite.PairPowerSumCatalogue
