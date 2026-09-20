import Coulomb8.InverseBounds.R00
import Coulomb8.InverseBounds.R01
import Coulomb8.InverseBounds.R02
import Coulomb8.InverseBounds.R03
import Coulomb8.InverseBounds.R04
import Coulomb8.InverseBounds.R05
import Coulomb8.InverseBounds.R06
import Coulomb8.InverseBounds.R07
import Coulomb8.InverseBounds.R08
import Coulomb8.InverseBounds.R09
import Coulomb8.InverseBounds.R10
import Coulomb8.InverseBounds.R11
import Coulomb8.InverseBounds.R12
import Coulomb8.InverseBounds.R13
import Coulomb8.InverseBounds.R14
import Coulomb8.InverseBounds.R15
import Coulomb8.InverseBounds.R16
import Coulomb8.InverseBounds.R17
import Coulomb8.InverseBounds.R18
import Coulomb8.InverseBounds.R19
import Coulomb8.InverseBounds.R20
import Coulomb8.InverseBounds.R21
import Coulomb8.InverseBounds.R22
import Coulomb8.InverseBounds.R23
import Coulomb8.InverseBounds.R24
import Coulomb8.InverseBounds.R25
import Coulomb8.InverseBounds.R26
import Coulomb8.InverseBounds.R27
import Coulomb8.InverseBounds.R28
import Coulomb8.InverseBounds.R29
import Coulomb8.InverseBounds.R30
import Coulomb8.InverseBounds.R31
import Coulomb8.InverseBounds.R32
import Coulomb8.InverseBounds.R33
import Coulomb8.InverseBounds.R34
import Coulomb8.InverseBounds.R35
import Coulomb8.InverseBounds.R36
import Coulomb8.InverseBounds.R37
import Coulomb8.InverseBounds.R38
import Coulomb8.InverseBounds.R39
import Coulomb8.InverseBounds.R40
import Coulomb8.InverseBounds.R41
import Coulomb8.InverseBounds.R42
import Coulomb8.InverseBounds.R43
import Coulomb8.InverseBounds.R44
import Coulomb8.InverseBounds.R45
import Coulomb8.InverseBounds.R46
import Coulomb8.InverseBounds.R47
import Coulomb8.InverseBounds.R48
import Coulomb8.InverseBounds.R49
import Coulomb8.InverseBounds.R50
import Coulomb8.InverseBounds.R51
import Coulomb8.InverseBounds.R52
import Coulomb8.InverseBounds.R53
import Coulomb8.InverseBounds.R54
import Coulomb8.InverseBounds.R55
import Coulomb8.InverseBounds.R56
import Coulomb8.InverseBounds.R57
import Coulomb8.InverseBounds.R58
import Coulomb8.InverseBounds.R59
import Coulomb8.InverseBounds.R60
import Coulomb8.InverseBounds.R61
import Coulomb8.InverseBounds.R62
import Coulomb8.InverseBounds.R63
import Coulomb8.InverseBounds.R64
import Coulomb8.InverseBounds.R65
import Coulomb8.InverseBounds.R66
import Coulomb8.InverseBounds.R67
import Coulomb8.InverseBounds.R68
import Coulomb8.InverseBounds.R69
import Coulomb8.InverseBounds.R70
import Coulomb8.InverseBounds.R71
import Coulomb8.InverseBounds.R72
import Coulomb8.InverseBounds.R73
import Coulomb8.InverseBounds.R74
import Coulomb8.InverseBounds.R75
import Coulomb8.InverseBounds.R76
import Coulomb8.InverseBounds.R77
import Coulomb8.InverseBounds.R78
import Coulomb8.InverseBounds.R79
import Coulomb8.InverseBounds.R80
import Coulomb8.InverseBounds.R81
import Coulomb8.InverseBounds.R82
import Coulomb8.InverseBounds.R83
import Coulomb8.InverseBounds.R84
import Coulomb8.InverseBounds.R85
import Coulomb8.InverseBounds.R86
import Coulomb8.InverseBounds.R87
import Coulomb8.InverseBounds.R88
import Coulomb8.InverseBounds.R89
import Coulomb8.InverseBounds.R90
import Coulomb8.InverseBounds.R91
import Coulomb8.InverseBounds.R92
import Coulomb8.InverseBounds.R93
import Coulomb8.InverseBounds.R94
import Coulomb8.InverseBounds.R95
import Coulomb8.InverseBounds.R96
import Coulomb8.InverseBounds.R97
import Coulomb8.InverseBounds.R98

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.InverseBounds
open scoped BigOperators

theorem entry_bound (i j : Fin 99) :
    |((1-Witness.preconditioner*selectedMatrix) i j)| ≤ (1/256 : ℝ) := by
  fin_cases i
  · exact row0_bound j
  · exact row1_bound j
  · exact row2_bound j
  · exact row3_bound j
  · exact row4_bound j
  · exact row5_bound j
  · exact row6_bound j
  · exact row7_bound j
  · exact row8_bound j
  · exact row9_bound j
  · exact row10_bound j
  · exact row11_bound j
  · exact row12_bound j
  · exact row13_bound j
  · exact row14_bound j
  · exact row15_bound j
  · exact row16_bound j
  · exact row17_bound j
  · exact row18_bound j
  · exact row19_bound j
  · exact row20_bound j
  · exact row21_bound j
  · exact row22_bound j
  · exact row23_bound j
  · exact row24_bound j
  · exact row25_bound j
  · exact row26_bound j
  · exact row27_bound j
  · exact row28_bound j
  · exact row29_bound j
  · exact row30_bound j
  · exact row31_bound j
  · exact row32_bound j
  · exact row33_bound j
  · exact row34_bound j
  · exact row35_bound j
  · exact row36_bound j
  · exact row37_bound j
  · exact row38_bound j
  · exact row39_bound j
  · exact row40_bound j
  · exact row41_bound j
  · exact row42_bound j
  · exact row43_bound j
  · exact row44_bound j
  · exact row45_bound j
  · exact row46_bound j
  · exact row47_bound j
  · exact row48_bound j
  · exact row49_bound j
  · exact row50_bound j
  · exact row51_bound j
  · exact row52_bound j
  · exact row53_bound j
  · exact row54_bound j
  · exact row55_bound j
  · exact row56_bound j
  · exact row57_bound j
  · exact row58_bound j
  · exact row59_bound j
  · exact row60_bound j
  · exact row61_bound j
  · exact row62_bound j
  · exact row63_bound j
  · exact row64_bound j
  · exact row65_bound j
  · exact row66_bound j
  · exact row67_bound j
  · exact row68_bound j
  · exact row69_bound j
  · exact row70_bound j
  · exact row71_bound j
  · exact row72_bound j
  · exact row73_bound j
  · exact row74_bound j
  · exact row75_bound j
  · exact row76_bound j
  · exact row77_bound j
  · exact row78_bound j
  · exact row79_bound j
  · exact row80_bound j
  · exact row81_bound j
  · exact row82_bound j
  · exact row83_bound j
  · exact row84_bound j
  · exact row85_bound j
  · exact row86_bound j
  · exact row87_bound j
  · exact row88_bound j
  · exact row89_bound j
  · exact row90_bound j
  · exact row91_bound j
  · exact row92_bound j
  · exact row93_bound j
  · exact row94_bound j
  · exact row95_bound j
  · exact row96_bound j
  · exact row97_bound j
  · exact row98_bound j

theorem row_bound (i : Fin 99) :
    ∑ j, |((1-Witness.preconditioner*selectedMatrix) i j)| ≤ (1/2 : ℝ) := by
  calc
    _ ≤ ∑ j : Fin 99, (1/256 : ℝ) := Finset.sum_le_sum (fun j _ => entry_bound i j)
    _ ≤ 1/2 := by norm_num

end Coulomb8.InverseBounds

#print axioms Coulomb8.InverseBounds.row_bound
