import AllS.Units.N_FI.N_raw_projection.N_target_directions
import AllS.Units.N_FI.N_kernels.N_finite_layout_linkage

noncomputable section
namespace Blueprint.Thomson.Finite.PowerSumCatalogue
open RawCatalogue
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def p00 : SparsePoly := [((0,0,0),(3:ℚ))]
def q00 : Poly3 := ratToReal (sparsePolynomial p00)
theorem identity_00 : q00=rawInvariantPowerSum 0 := by
  rw [rawInvariantPowerSum]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q00,p00]
  all_goals ring
#print axioms identity_00

def p01 : SparsePoly := [((1,0,0),(1:ℚ))]
def q01 : Poly3 := ratToReal (sparsePolynomial p01)
theorem identity_01 : q01=rawInvariantPowerSum 1 := by
  rw [rawInvariantPowerSum]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q01,p01]
  all_goals ring
#print axioms identity_01

def p02 : SparsePoly := [((0,1,0),(-2:ℚ)),((2,0,0),(1:ℚ))]
def q02 : Poly3 := ratToReal (sparsePolynomial p02)
theorem identity_02 : q02=rawInvariantPowerSum 2 := by
  rw [rawInvariantPowerSum]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q02,p02]
  all_goals ring
#print axioms identity_02

def p03 : SparsePoly := [((0,0,1),(3:ℚ)),((1,1,0),(-3:ℚ)),((3,0,0),(1:ℚ))]
def q03 : Poly3 := ratToReal (sparsePolynomial p03)
theorem identity_03 : q03=rawInvariantPowerSum 3 := by
  rw [rawInvariantPowerSum]
  rw [← identity_02,← identity_01,← identity_00]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q03,p03,q02,p02,q01,p01,q00,p00]
  all_goals ring
#print axioms identity_03

def p04 : SparsePoly := [((0,2,0),(2:ℚ)),((1,0,1),(4:ℚ)),((2,1,0),(-4:ℚ)),((4,0,0),(1:ℚ))]
def q04 : Poly3 := ratToReal (sparsePolynomial p04)
theorem identity_04 : q04=rawInvariantPowerSum 4 := by
  rw [rawInvariantPowerSum]
  rw [← identity_03,← identity_02,← identity_01]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q04,p04,q03,p03,q02,p02,q01,p01]
  all_goals ring
#print axioms identity_04

def p05 : SparsePoly := [((0,1,1),(-5:ℚ)),((1,2,0),(5:ℚ)),((2,0,1),(5:ℚ)),((3,1,0),(-5:ℚ)),((5,0,0),(1:ℚ))]
def q05 : Poly3 := ratToReal (sparsePolynomial p05)
theorem identity_05 : q05=rawInvariantPowerSum 5 := by
  rw [rawInvariantPowerSum]
  rw [← identity_04,← identity_03,← identity_02]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q05,p05,q04,p04,q03,p03,q02,p02]
  all_goals ring
#print axioms identity_05

def p06 : SparsePoly := [((0,0,2),(3:ℚ)),((0,3,0),(-2:ℚ)),((1,1,1),(-12:ℚ)),((2,2,0),(9:ℚ)),((3,0,1),(6:ℚ)),((4,1,0),(-6:ℚ)),((6,0,0),(1:ℚ))]
def q06 : Poly3 := ratToReal (sparsePolynomial p06)
theorem identity_06 : q06=rawInvariantPowerSum 6 := by
  rw [rawInvariantPowerSum]
  rw [← identity_05,← identity_04,← identity_03]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q06,p06,q05,p05,q04,p04,q03,p03]
  all_goals ring
#print axioms identity_06

def p07 : SparsePoly := [((0,2,1),(7:ℚ)),((1,0,2),(7:ℚ)),((1,3,0),(-7:ℚ)),((2,1,1),(-21:ℚ)),((3,2,0),(14:ℚ)),((4,0,1),(7:ℚ)),((5,1,0),(-7:ℚ)),((7,0,0),(1:ℚ))]
def q07 : Poly3 := ratToReal (sparsePolynomial p07)
theorem identity_07 : q07=rawInvariantPowerSum 7 := by
  rw [rawInvariantPowerSum]
  rw [← identity_06,← identity_05,← identity_04]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q07,p07,q06,p06,q05,p05,q04,p04]
  all_goals ring
#print axioms identity_07

def p08 : SparsePoly := [((0,1,2),(-8:ℚ)),((0,4,0),(2:ℚ)),((1,2,1),(24:ℚ)),((2,0,2),(12:ℚ)),((2,3,0),(-16:ℚ)),((3,1,1),(-32:ℚ)),((4,2,0),(20:ℚ)),((5,0,1),(8:ℚ)),((6,1,0),(-8:ℚ)),((8,0,0),(1:ℚ))]
def q08 : Poly3 := ratToReal (sparsePolynomial p08)
theorem identity_08 : q08=rawInvariantPowerSum 8 := by
  rw [rawInvariantPowerSum]
  rw [← identity_07,← identity_06,← identity_05]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q08,p08,q07,p07,q06,p06,q05,p05]
  all_goals ring
#print axioms identity_08

def p09 : SparsePoly := [((0,0,3),(3:ℚ)),((0,3,1),(-9:ℚ)),((1,1,2),(-27:ℚ)),((1,4,0),(9:ℚ)),((2,2,1),(54:ℚ)),((3,0,2),(18:ℚ)),((3,3,0),(-30:ℚ)),((4,1,1),(-45:ℚ)),((5,2,0),(27:ℚ)),((6,0,1),(9:ℚ)),((7,1,0),(-9:ℚ)),((9,0,0),(1:ℚ))]
def q09 : Poly3 := ratToReal (sparsePolynomial p09)
theorem identity_09 : q09=rawInvariantPowerSum 9 := by
  rw [rawInvariantPowerSum]
  rw [← identity_08,← identity_07,← identity_06]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q09,p09,q08,p08,q07,p07,q06,p06]
  all_goals ring
#print axioms identity_09

def p10 : SparsePoly := [((0,2,2),(15:ℚ)),((0,5,0),(-2:ℚ)),((1,0,3),(10:ℚ)),((1,3,1),(-40:ℚ)),((2,1,2),(-60:ℚ)),((2,4,0),(25:ℚ)),((3,2,1),(100:ℚ)),((4,0,2),(25:ℚ)),((4,3,0),(-50:ℚ)),((5,1,1),(-60:ℚ)),((6,2,0),(35:ℚ)),((7,0,1),(10:ℚ)),((8,1,0),(-10:ℚ)),((10,0,0),(1:ℚ))]
def q10 : Poly3 := ratToReal (sparsePolynomial p10)
theorem identity_10 : q10=rawInvariantPowerSum 10 := by
  rw [rawInvariantPowerSum]
  rw [← identity_09,← identity_08,← identity_07]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q10,p10,q09,p09,q08,p08,q07,p07]
  all_goals ring
#print axioms identity_10

def p11 : SparsePoly := [((0,1,3),(-11:ℚ)),((0,4,1),(11:ℚ)),((1,2,2),(66:ℚ)),((1,5,0),(-11:ℚ)),((2,0,3),(22:ℚ)),((2,3,1),(-110:ℚ)),((3,1,2),(-110:ℚ)),((3,4,0),(55:ℚ)),((4,2,1),(165:ℚ)),((5,0,2),(33:ℚ)),((5,3,0),(-77:ℚ)),((6,1,1),(-77:ℚ)),((7,2,0),(44:ℚ)),((8,0,1),(11:ℚ)),((9,1,0),(-11:ℚ)),((11,0,0),(1:ℚ))]
def q11 : Poly3 := ratToReal (sparsePolynomial p11)
theorem identity_11 : q11=rawInvariantPowerSum 11 := by
  rw [rawInvariantPowerSum]
  rw [← identity_10,← identity_09,← identity_08]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q11,p11,q10,p10,q09,p09,q08,p08]
  all_goals ring
#print axioms identity_11

def p12 : SparsePoly := [((0,0,4),(3:ℚ)),((0,3,2),(-24:ℚ)),((0,6,0),(2:ℚ)),((1,1,3),(-48:ℚ)),((1,4,1),(60:ℚ)),((2,2,2),(180:ℚ)),((2,5,0),(-36:ℚ)),((3,0,3),(40:ℚ)),((3,3,1),(-240:ℚ)),((4,1,2),(-180:ℚ)),((4,4,0),(105:ℚ)),((5,2,1),(252:ℚ)),((6,0,2),(42:ℚ)),((6,3,0),(-112:ℚ)),((7,1,1),(-96:ℚ)),((8,2,0),(54:ℚ)),((9,0,1),(12:ℚ)),((10,1,0),(-12:ℚ)),((12,0,0),(1:ℚ))]
def q12 : Poly3 := ratToReal (sparsePolynomial p12)
theorem identity_12 : q12=rawInvariantPowerSum 12 := by
  rw [rawInvariantPowerSum]
  rw [← identity_11,← identity_10,← identity_09]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q12,p12,q11,p11,q10,p10,q09,p09]
  all_goals ring
#print axioms identity_12

def p13 : SparsePoly := [((0,2,3),(26:ℚ)),((0,5,1),(-13:ℚ)),((1,0,4),(13:ℚ)),((1,3,2),(-130:ℚ)),((1,6,0),(13:ℚ)),((2,1,3),(-130:ℚ)),((2,4,1),(195:ℚ)),((3,2,2),(390:ℚ)),((3,5,0),(-91:ℚ)),((4,0,3),(65:ℚ)),((4,3,1),(-455:ℚ)),((5,1,2),(-273:ℚ)),((5,4,0),(182:ℚ)),((6,2,1),(364:ℚ)),((7,0,2),(52:ℚ)),((7,3,0),(-156:ℚ)),((8,1,1),(-117:ℚ)),((9,2,0),(65:ℚ)),((10,0,1),(13:ℚ)),((11,1,0),(-13:ℚ)),((13,0,0),(1:ℚ))]
def q13 : Poly3 := ratToReal (sparsePolynomial p13)
theorem identity_13 : q13=rawInvariantPowerSum 13 := by
  rw [rawInvariantPowerSum]
  rw [← identity_12,← identity_11,← identity_10]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q13,p13,q12,p12,q11,p11,q10,p10]
  all_goals ring
#print axioms identity_13

def p14 : SparsePoly := [((0,1,4),(-14:ℚ)),((0,4,2),(35:ℚ)),((0,7,0),(-2:ℚ)),((1,2,3),(140:ℚ)),((1,5,1),(-84:ℚ)),((2,0,4),(35:ℚ)),((2,3,2),(-420:ℚ)),((2,6,0),(49:ℚ)),((3,1,3),(-280:ℚ)),((3,4,1),(490:ℚ)),((4,2,2),(735:ℚ)),((4,5,0),(-196:ℚ)),((5,0,3),(98:ℚ)),((5,3,1),(-784:ℚ)),((6,1,2),(-392:ℚ)),((6,4,0),(294:ℚ)),((7,2,1),(504:ℚ)),((8,0,2),(63:ℚ)),((8,3,0),(-210:ℚ)),((9,1,1),(-140:ℚ)),((10,2,0),(77:ℚ)),((11,0,1),(14:ℚ)),((12,1,0),(-14:ℚ)),((14,0,0),(1:ℚ))]
def q14 : Poly3 := ratToReal (sparsePolynomial p14)
theorem identity_14 : q14=rawInvariantPowerSum 14 := by
  rw [rawInvariantPowerSum]
  rw [← identity_13,← identity_12,← identity_11]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q14,p14,q13,p13,q12,p12,q11,p11]
  all_goals ring
#print axioms identity_14

def p15 : SparsePoly := [((0,0,5),(3:ℚ)),((0,3,3),(-50:ℚ)),((0,6,1),(15:ℚ)),((1,1,4),(-75:ℚ)),((1,4,2),(225:ℚ)),((1,7,0),(-15:ℚ)),((2,2,3),(450:ℚ)),((2,5,1),(-315:ℚ)),((3,0,4),(75:ℚ)),((3,3,2),(-1050:ℚ)),((3,6,0),(140:ℚ)),((4,1,3),(-525:ℚ)),((4,4,1),(1050:ℚ)),((5,2,2),(1260:ℚ)),((5,5,0),(-378:ℚ)),((6,0,3),(140:ℚ)),((6,3,1),(-1260:ℚ)),((7,1,2),(-540:ℚ)),((7,4,0),(450:ℚ)),((8,2,1),(675:ℚ)),((9,0,2),(75:ℚ)),((9,3,0),(-275:ℚ)),((10,1,1),(-165:ℚ)),((11,2,0),(90:ℚ)),((12,0,1),(15:ℚ)),((13,1,0),(-15:ℚ)),((15,0,0),(1:ℚ))]
def q15 : Poly3 := ratToReal (sparsePolynomial p15)
theorem identity_15 : q15=rawInvariantPowerSum 15 := by
  rw [rawInvariantPowerSum]
  rw [← identity_14,← identity_13,← identity_12]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q15,p15,q14,p14,q13,p13,q12,p12]
  all_goals ring
#print axioms identity_15

def p16 : SparsePoly := [((0,2,4),(40:ℚ)),((0,5,2),(-48:ℚ)),((0,8,0),(2:ℚ)),((1,0,5),(16:ℚ)),((1,3,3),(-320:ℚ)),((1,6,1),(112:ℚ)),((2,1,4),(-240:ℚ)),((2,4,2),(840:ℚ)),((2,7,0),(-64:ℚ)),((3,2,3),(1120:ℚ)),((3,5,1),(-896:ℚ)),((4,0,4),(140:ℚ)),((4,3,2),(-2240:ℚ)),((4,6,0),(336:ℚ)),((5,1,3),(-896:ℚ)),((5,4,1),(2016:ℚ)),((6,2,2),(2016:ℚ)),((6,5,0),(-672:ℚ)),((7,0,3),(192:ℚ)),((7,3,1),(-1920:ℚ)),((8,1,2),(-720:ℚ)),((8,4,0),(660:ℚ)),((9,2,1),(880:ℚ)),((10,0,2),(88:ℚ)),((10,3,0),(-352:ℚ)),((11,1,1),(-192:ℚ)),((12,2,0),(104:ℚ)),((13,0,1),(16:ℚ)),((14,1,0),(-16:ℚ)),((16,0,0),(1:ℚ))]
def q16 : Poly3 := ratToReal (sparsePolynomial p16)
theorem identity_16 : q16=rawInvariantPowerSum 16 := by
  rw [rawInvariantPowerSum]
  rw [← identity_15,← identity_14,← identity_13]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q16,p16,q15,p15,q14,p14,q13,p13]
  all_goals ring
#print axioms identity_16

def p17 : SparsePoly := [((0,1,5),(-17:ℚ)),((0,4,3),(85:ℚ)),((0,7,1),(-17:ℚ)),((1,2,4),(255:ℚ)),((1,5,2),(-357:ℚ)),((1,8,0),(17:ℚ)),((2,0,5),(51:ℚ)),((2,3,3),(-1190:ℚ)),((2,6,1),(476:ℚ)),((3,1,4),(-595:ℚ)),((3,4,2),(2380:ℚ)),((3,7,0),(-204:ℚ)),((4,2,3),(2380:ℚ)),((4,5,1),(-2142:ℚ)),((5,0,4),(238:ℚ)),((5,3,2),(-4284:ℚ)),((5,6,0),(714:ℚ)),((6,1,3),(-1428:ℚ)),((6,4,1),(3570:ℚ)),((7,2,2),(3060:ℚ)),((7,5,0),(-1122:ℚ)),((8,0,3),(255:ℚ)),((8,3,1),(-2805:ℚ)),((9,1,2),(-935:ℚ)),((9,4,0),(935:ℚ)),((10,2,1),(1122:ℚ)),((11,0,2),(102:ℚ)),((11,3,0),(-442:ℚ)),((12,1,1),(-221:ℚ)),((13,2,0),(119:ℚ)),((14,0,1),(17:ℚ)),((15,1,0),(-17:ℚ)),((17,0,0),(1:ℚ))]
def q17 : Poly3 := ratToReal (sparsePolynomial p17)
theorem identity_17 : q17=rawInvariantPowerSum 17 := by
  rw [rawInvariantPowerSum]
  rw [← identity_16,← identity_15,← identity_14]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q17,p17,q16,p16,q15,p15,q14,p14]
  all_goals ring
#print axioms identity_17

def p18 : SparsePoly := [((0,0,6),(3:ℚ)),((0,3,4),(-90:ℚ)),((0,6,2),(63:ℚ)),((0,9,0),(-2:ℚ)),((1,1,5),(-108:ℚ)),((1,4,3),(630:ℚ)),((1,7,1),(-144:ℚ)),((2,2,4),(945:ℚ)),((2,5,2),(-1512:ℚ)),((2,8,0),(81:ℚ)),((3,0,5),(126:ℚ)),((3,3,3),(-3360:ℚ)),((3,6,1),(1512:ℚ)),((4,1,4),(-1260:ℚ)),((4,4,2),(5670:ℚ)),((4,7,0),(-540:ℚ)),((5,2,3),(4536:ℚ)),((5,5,1),(-4536:ℚ)),((6,0,4),(378:ℚ)),((6,3,2),(-7560:ℚ)),((6,6,0),(1386:ℚ)),((7,1,3),(-2160:ℚ)),((7,4,1),(5940:ℚ)),((8,2,2),(4455:ℚ)),((8,5,0),(-1782:ℚ)),((9,0,3),(330:ℚ)),((9,3,1),(-3960:ℚ)),((10,1,2),(-1188:ℚ)),((10,4,0),(1287:ℚ)),((11,2,1),(1404:ℚ)),((12,0,2),(117:ℚ)),((12,3,0),(-546:ℚ)),((13,1,1),(-252:ℚ)),((14,2,0),(135:ℚ)),((15,0,1),(18:ℚ)),((16,1,0),(-18:ℚ)),((18,0,0),(1:ℚ))]
def q18 : Poly3 := ratToReal (sparsePolynomial p18)
theorem identity_18 : q18=rawInvariantPowerSum 18 := by
  rw [rawInvariantPowerSum]
  rw [← identity_17,← identity_16,← identity_15]
  apply MvPolynomial.funext
  intro x
  norm_num [ratToReal,sparsePolynomial,q18,p18,q17,p17,q16,p16,q15,p15]
  all_goals ring
#print axioms identity_18

def sourcePowerSum : Fin 19 → Poly3 := ![q00,q01,q02,q03,q04,q05,q06,q07,q08,q09,q10,q11,q12,q13,q14,q15,q16,q17,q18]
theorem source_power_sum (n : Fin 19) : sourcePowerSum n=rawInvariantPowerSum n.val := by
  fin_cases n
  · exact identity_00
  · exact identity_01
  · exact identity_02
  · exact identity_03
  · exact identity_04
  · exact identity_05
  · exact identity_06
  · exact identity_07
  · exact identity_08
  · exact identity_09
  · exact identity_10
  · exact identity_11
  · exact identity_12
  · exact identity_13
  · exact identity_14
  · exact identity_15
  · exact identity_16
  · exact identity_17
  · exact identity_18
#print axioms source_power_sum
end Blueprint.Thomson.Finite.PowerSumCatalogue
