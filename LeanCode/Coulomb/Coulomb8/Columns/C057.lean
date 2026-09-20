import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C057

def r0 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -4800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 53568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -347520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1414656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -3595392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 5094144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -1820160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -5631168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 7917888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1908288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -249216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 276480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -20928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 9472, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -808320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 2677632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -5658624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 944256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -1211072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -1072640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 9083328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -2691200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -831360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 1856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -22080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 21568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -675072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 2062208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -4161280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 4649088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -445632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -5533376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 5529408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -180160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 37056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -196864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 606080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -132352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 2134784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -2274880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -499584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1348288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -5760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 62464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -347264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 1082752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -1792384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 924160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 222592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -2360384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 714240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -3200, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 16512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -606336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 56448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 475264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -89088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -32384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 16640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -165248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -24320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 234624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -5888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 47616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 82176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -17152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 145280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -101376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -4077056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 4081920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -4703360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 720640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -252800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 7872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -6784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 457472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -1290880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 1581056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -20288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -229760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 170560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -21248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 72448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -934656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 699648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 451840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -1156352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 559360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -73856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 221824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -325760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 82560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 53120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -50560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -145920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 406272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -556544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 136704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -138368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 17920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -11520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 58880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -280576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 312576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 103424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -38528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 55808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -56704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 18304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -4096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 121344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -217088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 73216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 212992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -164352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -62208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 90624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 151296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -70656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 218880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 25344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -58112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 196864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -320256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 26624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 76032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -174336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 23808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 590592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -960768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -2400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 26784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -173760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 707328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -1797696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 2547072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -910080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -2815584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 3958944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -954144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -124608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 138240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -10464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 4736, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -404160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 1338816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -2829312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 472128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -605536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -536320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 4541664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -1345600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -415680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -11040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 10784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -337536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 1031104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -2080640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 2324544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -222816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -2766688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 2764704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -90080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 18528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 303040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -66176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1067392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -1137440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -249792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 674144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -2880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -173632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 541376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -896192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 462080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 111296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1180192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 357120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -1600, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 8256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -303168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 28224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 237632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -44544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -16192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 8320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -82624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -12160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 117312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -2944, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 41088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -8576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 72640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -50688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -2038528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 2040960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -2351680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 360320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -126400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 3936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -3392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 228736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -645440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 790528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -10144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -114880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 85280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -10624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 36224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -467328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 349824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 225920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -578176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 279680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -36928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 110912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -162880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 41280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 26560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -25280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -72960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 203136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -278272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 68352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -69184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 29440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -140288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 156288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 51712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -19264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 27904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 9152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 60672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -108544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 36608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 106496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -82176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -31104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 45312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 75648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -35328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 109440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -29056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -160128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 38016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -87168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 11904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 295296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -480384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[r13,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36],[r0,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46],[r0,r47,r48,r49,r50,r51,r52,r53,r54,r55],[r56,r57,r57,r58,r59,r60,r61,r62,r63],[r56,r64,r65,r66,r67,r68,r69,r70],[0,r71,r72,r73,-512,r68,r74],[],[],[],[],[],[0,r75,r76,r77,r78,18176,r79,r80,r81,r82,r83,r84],[r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95],[0,r96,r97,r98,r99,r100,r101,r102,r103,r104],[0,r105,r106,r107,r108,r109,r110,r111,r112],[],[],[],[],[],[],[],[r113,r114,r115,r116,r117,r118,r119,r120,r121,r122],[r56,r123,r124,r125,r126,r127,r128,r129,r130],[r56,r131,r132,r133,r134,-512,r135,r136],[],[],[],[],[],[],[0,r131,r137,r138,r139,r140,r141,r142],[0,r71,r72,r73,-512,r68,r74],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r143,r144,r145,r146,r147,r148,r149,1536],[r150,r151,r152,r153,r154,r155,r156,1280],[r150,r157,r158,r159,r160,r161,-1792],[r162,r163,r164,r114,r165,-512],[r162,r166,r167,r168,512],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r169,r72,r170,r171,r172,r173,r174,3840],[r150,r157,r158,r159,r160,r161,-1792],[r162,r163,r164,r114,r165,-512],[r162,r166,r167,r168,512],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187]),(⟨0,0,1⟩,[r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨0,0,2⟩,[r188,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211]),(⟨0,0,3⟩,[r175,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨0,0,4⟩,[r175,r222,r223,r224,r225,r226,r227,r228,r229,r230]),(⟨0,0,5⟩,[r13,r231,r231,r232,r233,r234,r235,r236,r237]),(⟨0,0,6⟩,[r13,r238,r239,r240,r241,r242,r243,r244]),(⟨0,0,7⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨0,1,0⟩,[r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨0,1,1⟩,[0,r248,r249,r250,r251,9088,r252,r253,r254,r255,r256,r257]),(⟨0,1,2⟩,[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,1,3⟩,[0,r143,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,1,4⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨0,2,0⟩,[r188,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211]),(⟨0,2,1⟩,[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,2,2⟩,[r85,r96,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,2,3⟩,[r13,r293,r47,r294,r295,r296,r297,r298,r299]),(⟨0,2,4⟩,[r13,r71,r300,r301,r302,-256,r303,r304]),(⟨0,3,0⟩,[r175,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨0,3,1⟩,[0,r143,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,3,2⟩,[r13,r293,r47,r294,r295,r296,r297,r298,r299]),(⟨0,3,3⟩,[0,r71,r305,r306,r307,r308,r309,r310]),(⟨0,3,4⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨0,4,0⟩,[r175,r222,r223,r224,r225,r226,r227,r228,r229,r230]),(⟨0,4,1⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨0,4,2⟩,[r13,r71,r300,r301,r302,-256,r303,r304]),(⟨0,4,3⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨0,5,0⟩,[r13,r231,r231,r232,r233,r234,r235,r236,r237]),(⟨0,6,0⟩,[r13,r238,r239,r240,r241,r242,r243,r244]),(⟨0,7,0⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨1,0,0⟩,[r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨1,0,1⟩,[0,r248,r249,r250,r251,9088,r252,r253,r254,r255,r256,r257]),(⟨1,0,2⟩,[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨1,0,3⟩,[0,r143,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨1,0,4⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨1,1,0⟩,[0,r248,r249,r250,r251,9088,r252,r253,r254,r255,r256,r257]),(⟨1,2,0⟩,[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨1,2,2⟩,[0,r311,r166,r312,r313,r314,r315,r316,768]),(⟨1,2,3⟩,[r113,r317,r106,r318,r319,r320,r321,640]),(⟨1,2,4⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨1,2,5⟩,[r326,r327,r328,r96,r329,-256]),(⟨1,2,6⟩,[r326,r330,r331,r332,256]),(⟨1,3,0⟩,[0,r143,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨1,3,2⟩,[r113,r317,r106,r318,r319,r320,r321,640]),(⟨1,4,0⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨1,4,2⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨1,5,2⟩,[r326,r327,r328,r96,r329,-256]),(⟨1,6,2⟩,[r326,r330,r331,r332,256]),(⟨2,0,0⟩,[r188,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211]),(⟨2,0,1⟩,[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨2,0,2⟩,[r85,r96,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨2,0,3⟩,[r13,r293,r47,r294,r295,r296,r297,r298,r299]),(⟨2,0,4⟩,[r13,r71,r300,r301,r302,-256,r303,r304]),(⟨2,1,0⟩,[r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨2,1,2⟩,[0,r311,r166,r312,r313,r314,r315,r316,768]),(⟨2,1,3⟩,[r113,r317,r106,r318,r319,r320,r321,640]),(⟨2,1,4⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨2,1,5⟩,[r326,r327,r328,r96,r329,-256]),(⟨2,1,6⟩,[r326,r330,r331,r332,256]),(⟨2,2,0⟩,[r85,r96,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨2,2,1⟩,[0,r311,r166,r312,r313,r314,r315,r316,768]),(⟨2,2,2⟩,[r333,r246,r334,r335,r336,r337,r338,1920]),(⟨2,2,3⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨2,2,4⟩,[r326,r327,r328,r96,r329,-256]),(⟨2,2,5⟩,[r326,r330,r331,r332,256]),(⟨2,3,0⟩,[r13,r293,r47,r294,r295,r296,r297,r298,r299]),(⟨2,3,1⟩,[r113,r317,r106,r318,r319,r320,r321,640]),(⟨2,3,2⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨2,4,0⟩,[r13,r71,r300,r301,r302,-256,r303,r304]),(⟨2,4,1⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨2,4,2⟩,[r326,r327,r328,r96,r329,-256]),(⟨2,5,1⟩,[r326,r327,r328,r96,r329,-256]),(⟨2,5,2⟩,[r326,r330,r331,r332,256]),(⟨2,6,1⟩,[r326,r330,r331,r332,256]),(⟨3,0,0⟩,[r175,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨3,0,1⟩,[0,r143,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨3,0,2⟩,[r13,r293,r47,r294,r295,r296,r297,r298,r299]),(⟨3,0,3⟩,[0,r71,r305,r306,r307,r308,r309,r310]),(⟨3,0,4⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨3,1,0⟩,[0,r143,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨3,1,2⟩,[r113,r317,r106,r318,r319,r320,r321,640]),(⟨3,2,0⟩,[r13,r293,r47,r294,r295,r296,r297,r298,r299]),(⟨3,2,1⟩,[r113,r317,r106,r318,r319,r320,r321,640]),(⟨3,2,2⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨3,3,0⟩,[0,r71,r305,r306,r307,r308,r309,r310]),(⟨3,4,0⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨4,0,0⟩,[r175,r222,r223,r224,r225,r226,r227,r228,r229,r230]),(⟨4,0,1⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨4,0,2⟩,[r13,r71,r300,r301,r302,-256,r303,r304]),(⟨4,0,3⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨4,1,0⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284]),(⟨4,1,2⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨4,2,0⟩,[r13,r71,r300,r301,r302,-256,r303,r304]),(⟨4,2,1⟩,[r113,r322,r323,r164,r324,r325,-896]),(⟨4,2,2⟩,[r326,r327,r328,r96,r329,-256]),(⟨4,3,0⟩,[0,r245,r246,r172,-256,r242,r247]),(⟨5,0,0⟩,[r13,r231,r231,r232,r233,r234,r235,r236,r237]),(⟨5,1,2⟩,[r326,r327,r328,r96,r329,-256]),(⟨5,2,1⟩,[r326,r327,r328,r96,r329,-256]),(⟨5,2,2⟩,[r326,r330,r331,r332,256]),(⟨6,0,0⟩,[r13,r238,r239,r240,r241,r242,r243,r244]),(⟨6,1,2⟩,[r326,r330,r331,r332,256]),(⟨6,2,1⟩,[r326,r330,r331,r332,256]),(⟨7,0,0⟩,[0,r245,r246,r172,-256,r242,r247])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r339) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r340) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[256,-5376,49152,-251136,744960,-1158912,423936,1255680,-1439488,184320]),(⟨4,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,0,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,0,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨6,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2])]

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[256,-5376,49152,-251136,744960,-1158912,423936,1255680,-1439488,184320]),(⟨0,4,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,4,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,4,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,5,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,6,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,7,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨1,0,0⟩,[-128,3328,-39168,273280,-1234944,3694848,-7089408,7509504,-946048,-8281600,10077696,-4428160,460800]),(⟨1,0,1⟩,[0,896,-17152,145280,-709632,2162944,-4077056,4081920,-158720,-4703360,5044480,-1769600]),(⟨1,0,2⟩,[128,-3200,32000,-169728,510976,-815104,356608,923392,-1547392,801920,-89600]),(⟨1,0,3⟩,[0,-1280,19456,-124416,422912,-774144,582656,325120,-861184,410880]),(⟨1,1,0⟩,[0,896,-17152,145280,-709632,2162944,-4077056,4081920,-158720,-4703360,5044480,-1769600]),(⟨1,2,0⟩,[128,-3200,32000,-169728,510976,-815104,356608,923392,-1547392,801920,-89600]),(⟨1,3,0⟩,[0,-1280,19456,-124416,422912,-774144,582656,325120,-861184,410880]),(⟨1,4,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[-128,4096,-53376,387968,-1756416,5111296,-9214208,8358144,1588608,-12069376,10451328,-2414720]),(⟨2,0,1⟩,[0,896,-16256,130816,-605952,1730048,-2938368,2238720,1263360,-4018560,2477440]),(⟨2,0,2⟩,[128,-3072,29184,-145920,406272,-556544,25088,956928,-968576,125440]),(⟨2,0,3⟩,[0,-1280,18176,-108800,342784,-552704,247040,498944,-575232]),(⟨2,1,0⟩,[0,896,-16256,130816,-605952,1730048,-2938368,2238720,1263360,-4018560,2477440]),(⟨2,2,0⟩,[128,-3072,29184,-145920,406272,-556544,25088,956928,-968576,125440]),(⟨2,2,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,3,0⟩,[0,-1280,18176,-108800,342784,-552704,247040,498944,-575232]),(⟨2,4,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,5,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,6,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[384,-7936,70272,-339200,901120,-988928,-998912,3993856,-2979200,-1592832,2203520]),(⟨3,0,1⟩,[0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨3,0,2⟩,[-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨3,0,3⟩,[0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨3,1,0⟩,[0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨3,1,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨3,2,0⟩,[-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨3,2,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨3,2,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨3,3,0⟩,[0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨3,4,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,0,0⟩,[384,-11520,124928,-694528,2165504,-3584768,1848320,3116288,-4720768,1428480]),(⟨4,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,1,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,2,1⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨4,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,0,0⟩,[-256,2304,2304,-108800,561408,-1212672,790272,950528,-1247232]),(⟨5,1,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨5,2,1⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨5,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,0,0⟩,[-256,7680,-64768,232960,-330496,-48640,469248,-200192]),(⟨6,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2])]

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[256,-5376,49152,-251136,744960,-1158912,423936,1255680,-1439488,184320]),(⟨0,0,5⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,0,6⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,0,7⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,1,0⟩,[-128,3328,-39168,273280,-1234944,3694848,-7089408,7509504,-946048,-8281600,10077696,-4428160,460800]),(⟨0,1,1⟩,[0,896,-17152,145280,-709632,2162944,-4077056,4081920,-158720,-4703360,5044480,-1769600]),(⟨0,1,2⟩,[128,-3200,32000,-169728,510976,-815104,356608,923392,-1547392,801920,-89600]),(⟨0,1,3⟩,[0,-1280,19456,-124416,422912,-774144,582656,325120,-861184,410880]),(⟨0,1,4⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,2,0⟩,[-128,4096,-53376,387968,-1756416,5111296,-9214208,8358144,1588608,-12069376,10451328,-2414720]),(⟨0,2,1⟩,[0,896,-16256,130816,-605952,1730048,-2938368,2238720,1263360,-4018560,2477440]),(⟨0,2,2⟩,[128,-3072,29184,-145920,406272,-556544,25088,956928,-968576,125440]),(⟨0,2,3⟩,[0,-1280,18176,-108800,342784,-552704,247040,498944,-575232]),(⟨0,2,4⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,3,0⟩,[384,-7936,70272,-339200,901120,-988928,-998912,3993856,-2979200,-1592832,2203520]),(⟨0,3,1⟩,[0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨0,3,2⟩,[-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨0,3,3⟩,[0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨0,3,4⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,4,0⟩,[384,-11520,124928,-694528,2165504,-3584768,1848320,3116288,-4720768,1428480]),(⟨0,4,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,4,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,4,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,5,0⟩,[-256,2304,2304,-108800,561408,-1212672,790272,950528,-1247232]),(⟨0,6,0⟩,[-256,7680,-64768,232960,-330496,-48640,469248,-200192]),(⟨0,7,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨1,0,0⟩,[-128,3328,-39168,273280,-1234944,3694848,-7089408,7509504,-946048,-8281600,10077696,-4428160,460800]),(⟨1,0,1⟩,[0,896,-17152,145280,-709632,2162944,-4077056,4081920,-158720,-4703360,5044480,-1769600]),(⟨1,0,2⟩,[128,-3200,32000,-169728,510976,-815104,356608,923392,-1547392,801920,-89600]),(⟨1,0,3⟩,[0,-1280,19456,-124416,422912,-774144,582656,325120,-861184,410880]),(⟨1,0,4⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,1,0⟩,[0,1792,-34304,290560,-1419264,4325888,-8154112,8163840,-317440,-9406720,10088960,-3539200]),(⟨1,2,0⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨1,2,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,3,0⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨1,3,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨1,4,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,4,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨1,5,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨1,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[-128,4096,-53376,387968,-1756416,5111296,-9214208,8358144,1588608,-12069376,10451328,-2414720]),(⟨2,0,1⟩,[0,896,-16256,130816,-605952,1730048,-2938368,2238720,1263360,-4018560,2477440]),(⟨2,0,2⟩,[128,-3072,29184,-145920,406272,-556544,25088,956928,-968576,125440]),(⟨2,0,3⟩,[0,-1280,18176,-108800,342784,-552704,247040,498944,-575232]),(⟨2,0,4⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,1,0⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨2,1,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,2,0⟩,[256,-6144,58368,-291840,812544,-1113088,50176,1913856,-1937152,250880]),(⟨2,2,2⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨2,2,5⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,3,0⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨2,3,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,3,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,4,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,4,1⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,4,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨2,5,1⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨2,5,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,6,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[384,-7936,70272,-339200,901120,-988928,-998912,3993856,-2979200,-1592832,2203520]),(⟨3,0,1⟩,[0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨3,0,2⟩,[-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨3,0,3⟩,[0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨3,0,4⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨3,1,0⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨3,1,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨3,2,0⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨3,2,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨3,2,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨3,3,0⟩,[0,5120,-57344,242688,-434176,146432,425984,-328704]),(⟨3,4,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,0,0⟩,[384,-11520,124928,-694528,2165504,-3584768,1848320,3116288,-4720768,1428480]),(⟨4,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,1,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,2,1⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨4,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,0,0⟩,[-256,2304,2304,-108800,561408,-1212672,790272,950528,-1247232]),(⟨5,1,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨5,2,1⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨5,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,0,0⟩,[-256,7680,-64768,232960,-330496,-48640,469248,-200192]),(⟨6,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,384,-9600,107136,-695040,2829312,-7190784,10188288,-3640320,-11262336,15835776,-3816576,-3489024,552960]),(⟨0,0,1⟩,[-128,3328,-41856,322048,-1616640,5355264,-11317248,13219584,-2422144,-15016960,18166656,-5382400,-1662720]),(⟨0,0,2⟩,[-128,3712,-44160,301952,-1350144,4124416,-8322560,9298176,-891264,-11066752,11058816,-2522240]),(⟨0,0,3⟩,[384,-7936,74112,-393728,1212160,-1852928,9472,4269568,-4549760,-999168,2696576]),(⟨0,0,4⟩,[384,-11520,124928,-694528,2165504,-3584768,1848320,3116288,-4720768,1428480]),(⟨0,0,5⟩,[-256,2304,2304,-108800,561408,-1212672,790272,950528,-1247232]),(⟨0,0,6⟩,[-256,7680,-64768,232960,-330496,-48640,469248,-200192]),(⟨0,0,7⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,1,0⟩,[-128,3328,-41856,322048,-1616640,5355264,-11317248,13219584,-2422144,-15016960,18166656,-5382400,-1662720]),(⟨0,1,1⟩,[0,1792,-34304,290560,-1419264,4325888,-8154112,8163840,-317440,-9406720,10088960,-3539200]),(⟨0,1,2⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨0,1,3⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨0,1,4⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,2,0⟩,[-128,3712,-44160,301952,-1350144,4124416,-8322560,9298176,-891264,-11066752,11058816,-2522240]),(⟨0,2,1⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨0,2,2⟩,[256,-6144,58368,-291840,812544,-1113088,50176,1913856,-1937152,250880]),(⟨0,2,3⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨0,2,4⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,3,0⟩,[384,-7936,74112,-393728,1212160,-1852928,9472,4269568,-4549760,-999168,2696576]),(⟨0,3,1⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨0,3,2⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨0,3,3⟩,[0,5120,-57344,242688,-434176,146432,425984,-328704]),(⟨0,3,4⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,4,0⟩,[384,-11520,124928,-694528,2165504,-3584768,1848320,3116288,-4720768,1428480]),(⟨0,4,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,4,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,4,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,5,0⟩,[-256,2304,2304,-108800,561408,-1212672,790272,950528,-1247232]),(⟨0,6,0⟩,[-256,7680,-64768,232960,-330496,-48640,469248,-200192]),(⟨0,7,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨1,0,0⟩,[-128,3328,-41856,322048,-1616640,5355264,-11317248,13219584,-2422144,-15016960,18166656,-5382400,-1662720]),(⟨1,0,1⟩,[0,1792,-34304,290560,-1419264,4325888,-8154112,8163840,-317440,-9406720,10088960,-3539200]),(⟨1,0,2⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨1,0,3⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨1,0,4⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,1,0⟩,[0,1792,-34304,290560,-1419264,4325888,-8154112,8163840,-317440,-9406720,10088960,-3539200]),(⟨1,2,0⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨1,2,2⟩,[0,-1536,24576,-124416,181248,302592,-989184,437760,365568]),(⟨1,2,3⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨1,2,4⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨1,2,5⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨1,2,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,3,0⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨1,3,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨1,4,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,4,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨1,5,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨1,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[-128,3712,-44160,301952,-1350144,4124416,-8322560,9298176,-891264,-11066752,11058816,-2522240]),(⟨2,0,1⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨2,0,2⟩,[256,-6144,58368,-291840,812544,-1113088,50176,1913856,-1937152,250880]),(⟨2,0,3⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨2,0,4⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,1,0⟩,[128,-2304,15744,-38912,-94976,914944,-2581760,3162112,-284032,-3216640,2387840]),(⟨2,1,2⟩,[0,-1536,24576,-124416,181248,302592,-989184,437760,365568]),(⟨2,1,3⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,1,4⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,1,5⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨2,1,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,2,0⟩,[256,-6144,58368,-291840,812544,-1113088,50176,1913856,-1937152,250880]),(⟨2,2,1⟩,[0,-1536,24576,-124416,181248,302592,-989184,437760,365568]),(⟨2,2,2⟩,[1536,-26112,152064,-348672,47616,1181184,-1921536,913920]),(⟨2,2,3⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,2,4⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨2,2,5⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,3,0⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨2,3,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,3,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,4,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,4,1⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,4,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨2,5,1⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨2,5,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,6,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[384,-7936,74112,-393728,1212160,-1852928,9472,4269568,-4549760,-999168,2696576]),(⟨3,0,1⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨3,0,2⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨3,0,3⟩,[0,5120,-57344,242688,-434176,146432,425984,-328704]),(⟨3,0,4⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨3,1,0⟩,[0,-3072,46592,-297472,1014272,-1869312,1399296,903680,-2312704,1118720]),(⟨3,1,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨3,2,0⟩,[-256,4096,-23040,38912,117760,-561152,625152,206848,-539392]),(⟨3,2,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨3,2,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨3,3,0⟩,[0,5120,-57344,242688,-434176,146432,425984,-328704]),(⟨3,4,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,0,0⟩,[384,-11520,124928,-694528,2165504,-3584768,1848320,3116288,-4720768,1428480]),(⟨4,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨4,1,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨4,2,1⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨4,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,0,0⟩,[-256,2304,2304,-108800,561408,-1212672,790272,950528,-1247232]),(⟨5,1,2⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨5,2,1⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨5,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,0,0⟩,[-256,7680,-64768,232960,-330496,-48640,469248,-200192]),(⟨6,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


theorem partial_checked0 :
    (Poly.add (Poly.add (Poly.mul chunk0 sourceRight) partial4)
      (Poly.scale (K.ofRat (-1)) partial0)).isZero := by decide +kernel

theorem partial_sound0 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 0)
      sourceRight).eval u v t=partial0.eval u v t := by
  change (Poly.mul (chunk0++(sourceLeft.drop 4))
    sourceRight).eval u v t=partial0.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound4 partial_checked0 u v t


theorem weighted_checked :
    (Poly.add (Poly.scale (K.ofRat r341) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r339*r340 : ℚ)=r341 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 12 r339 r340 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C057

#print axioms Coulomb8.Columns.C057.sound
