import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C075

def r0 : ℚ := { num := 144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 1392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 22368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2163744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 13351776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -51253344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 19078272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -241927920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 299492736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -13778544, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 86339040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 17440128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -26079072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 634176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 1056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -6960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -3392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 705184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 27373056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -90155648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 212082704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -359110112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 428902736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -340040640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 152152192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -2390080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -1492960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 1312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -8800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 382464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -472640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 16336960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -54698176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 129712192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -219191328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 258713632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -202088576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 13210624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -2512832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -1952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 172512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1671072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 8209472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -25008512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 49493184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -61480064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 38793312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 5446688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -27503520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 2076000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -176, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 13472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 79056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -170432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 935456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -3061312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 46331360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -67673440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 64945872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -5329184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1362480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 4560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -86528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 420256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -127680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 348640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 155648, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -6579792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 996576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -440272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -24256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 22464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -540672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 1292800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -2112576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 2212320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -161760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 27008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -15040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 943360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -1884224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 296576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -153216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -54912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 194112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -323840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 37184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 197696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -331136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 37952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 2208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -18720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 53792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 307008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -3947008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 20817472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -69432640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 160738976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -15585504, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 307972832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -34447392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 113793664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -3401280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 19280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -719552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 2021792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -2077888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -5850784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 28559968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -58205680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 9904832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -6812400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 2141888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 9552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 91376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -162208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 5836384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -18248800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 2239200, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -53971248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 50441648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -4028304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 987728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -1056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -17792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 55360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -511936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -332608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 2317696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -525632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 396320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -45824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 76864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -4544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -254208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 77056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -72800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 9280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -202240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 943808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -2077760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -179872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 2496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -8256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 33984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -54720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -7104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 1696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 36544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -63552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 2427648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -7855808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 2322432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -3101856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 2528960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -1067808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 109760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 2624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -27264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 1255168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -4244224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 8795520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -11388544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 8690112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -417472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -26816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 53440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -27648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 46144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 59008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -212864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 340096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 203904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -928896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 2492160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -3548928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -174336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 12410112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -28212096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 4841088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -3260544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 30592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -23552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 502016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -747520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -136448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 406528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -807552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 766976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 277504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -408064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -97792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 1570816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -2972672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 2710784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -91648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 153728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -508416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 154112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -145600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 51712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -177152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -15424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 29504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -106432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 170048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 72, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 11184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -1081872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 6675888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -25626672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 9539136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -120963960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 149746368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -6889272, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 43169520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 8720064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -13039536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 317088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -24, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -3480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -1696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 352592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 13686528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -45077824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 106041352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -179555056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 214451368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -170020320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 76076096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -1195040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -746480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -4400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 191232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -236320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 8168480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -27349088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 64856096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -109595664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 129356816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -101044288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 6605312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1256416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 86256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -835536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 4104736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -12504256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 24746592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -30740032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 19396656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 2723344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -13751760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 1038000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -88, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 6736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 39528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -85216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 467728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -1530656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 23165680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -33836720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 32472936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -2664592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 681240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -40, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 2280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -43264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 210128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -63840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 174320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 77824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -3289896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 498288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -220136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -12128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 11232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -270336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 646400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1056288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 1106160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -80880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -7520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 471680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -942112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 148288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -76608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -27456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 97056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -161920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 18592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -27264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 98848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -165568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 18976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -9360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 26896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 153504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -1973504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 10408736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -34716320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 80369488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -7792752, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 153986416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -17223696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 56896832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -1700640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 40, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 9640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -359776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 1010896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -1038944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -2925392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 14279984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -29102840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 4952416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -3406200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1070944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 4776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 45688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -81104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 2918192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -9124400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1119600, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -26985624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 25220824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -2014152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 493864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 9472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -8896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 27680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -255968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -166304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 1158848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -262816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 198160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -22912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 38432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -2272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -127104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 38528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -36400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 4640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -101120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 471904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -1038880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -89936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 1248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -4128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 16992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -27360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -3552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 18272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -31776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 1213824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -3927904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 1161216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -1550928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 1264480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -533904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 54880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -13632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 627584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -2122112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 4397760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -5694272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 4345056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -208736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -13408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 26720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -13824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 23072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -1728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 101952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -464448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 1246080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -1774464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -87168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 6205056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -14106048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 2420544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -1630272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 15296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -11776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 251008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -373760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -68224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 203264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -403776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 383488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -44032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 138752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -204032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -48896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 785408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -1486336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 1355392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 25856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -88576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 1504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -7712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 14752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -53216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 85024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[r15,r16,r17,r18,r19,-47744,r20,r21,r22,r23,r24,r25,r26,r27,r28],[r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42],[r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55],[r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67],[r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78],[r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[r89,r90,r91,r92,r93,r94,r95,r96,r97],[r29,r98,r99,r100,r101,r102,r103,r104],[r29,r105,r106,r107,r108,r109,r110],[],[],[],[r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124],[r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137],[r0,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[0,r149,r150,r151,r152,r153,r154,r155,r156,r157,-6720],[r158,r159,r160,r161,r162,r163,r164,r165,r166,1568],[r158,r167,r168,r169,r170,r171,r172,20160,r173],[r174,r175,r176,r177,r178,r179,r180,832],[],[],[r181,r182,r183,r184,128],[],[r125,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195],[r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78],[r158,r159,r160,r161,r162,r163,r164,r165,r166,1568],[],[r29,r98,r99,r100,r101,r102,r103,r104],[],[],[],[],[r174,r196,r197,r198,r199,r200,r201,r202,r203,r204],[r125,r205,r206,r207,r208,r209,r210,r211,-1568],[],[r29,r105,r106,r107,r108,r109,r110],[],[],[],[r212,r213,r214,r215,r216,r217,r218,-1408],[],[],[r181,r182,r183,r184,128],[],[],[],[],[],[0,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,56448],[0,r43,r230,r231,r232,r233,r234,r235,r236,r237,r238,-18816],[0,r239,r240,r241,r242,r243,r244,r245,r246,r247,-8448],[r169,r248,r249,r250,r251,r252,r253,r254,r255,3136],[],[0,r81,r256,r257,r258,r259,r260,1536],[],[],[],[],[],[],[r125,r205,r206,r207,r208,r209,r210,r211,-1568],[],[],[],[],[],[],[r174,r261,r262,r263,r264,r265,r266,-704],[],[],[],[],[],[],[r181,r182,r183,r184,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281]),(⟨0,0,1⟩,[r282,r283,r284,r285,r286,-23872,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,0,2⟩,[r79,r296,r297,r69,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨0,0,3⟩,[r89,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319]),(⟨0,0,4⟩,[r126,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,0,5⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,0,6⟩,[r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,0,7⟩,[r125,r81,r352,r353,r354,r355,r356,r357,r358]),(⟨0,0,8⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨0,0,9⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨0,1,0⟩,[r282,r283,r284,r285,r286,-23872,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,1,1⟩,[r15,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨0,1,2⟩,[r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨0,1,3⟩,[r267,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406]),(⟨0,1,4⟩,[0,r407,r408,r409,r410,r411,r412,r413,r414,r415,-3360]),(⟨0,1,5⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨0,1,6⟩,[r416,r424,r425,r158,r426,r427,r428,10080,r429]),(⟨0,1,7⟩,[r111,r430,r431,r56,r432,r433,r434,416]),(⟨0,1,10⟩,[r29,r435,r436,r437,64]),(⟨0,2,0⟩,[r79,r296,r297,r69,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨0,2,1⟩,[r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨0,2,2⟩,[r383,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448]),(⟨0,2,3⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,2,4⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨0,2,6⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨0,3,0⟩,[r89,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319]),(⟨0,3,1⟩,[r267,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406]),(⟨0,3,2⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,3,3⟩,[r111,r30,r449,r450,r451,r452,r453,r454,r455,r456]),(⟨0,3,4⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨0,3,6⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨0,4,0⟩,[r126,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,4,1⟩,[0,r407,r408,r409,r410,r411,r412,r413,r414,r415,-3360]),(⟨0,4,2⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨0,4,3⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨0,4,4⟩,[r174,r261,r262,r263,r264,r265,r266,-704]),(⟨0,4,7⟩,[r29,r435,r436,r437,64]),(⟨0,5,0⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,5,1⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨0,6,0⟩,[r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,6,1⟩,[r416,r424,r425,r158,r426,r427,r428,10080,r429]),(⟨0,6,2⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨0,6,3⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨0,7,0⟩,[r125,r81,r352,r353,r354,r355,r356,r357,r358]),(⟨0,7,1⟩,[r111,r430,r431,r56,r432,r433,r434,416]),(⟨0,7,4⟩,[r29,r435,r436,r437,64]),(⟨0,8,0⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨0,9,0⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨0,10,1⟩,[r29,r435,r436,r437,64]),(⟨1,0,0⟩,[r282,r283,r284,r285,r286,-23872,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨1,0,1⟩,[r15,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨1,0,2⟩,[r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨1,0,3⟩,[r267,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406]),(⟨1,0,4⟩,[0,r407,r408,r409,r410,r411,r412,r413,r414,r415,-3360]),(⟨1,0,5⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨1,0,6⟩,[r416,r424,r425,r158,r426,r427,r428,10080,r429]),(⟨1,0,7⟩,[r111,r430,r431,r56,r432,r433,r434,416]),(⟨1,0,10⟩,[r29,r435,r436,r437,64]),(⟨1,1,0⟩,[r15,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨1,1,1⟩,[0,r464,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,28224]),(⟨1,1,2⟩,[0,r89,r475,r476,r477,r478,r479,r480,r481,r482,r483,-9408]),(⟨1,1,3⟩,[0,r212,r484,r485,r486,r487,r488,r489,r490,r491,-4224]),(⟨1,1,4⟩,[r158,r159,r160,r161,r162,r163,r164,r165,r166,1568]),(⟨1,1,6⟩,[0,r344,r492,r493,r494,r495,r496,768]),(⟨1,2,0⟩,[r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨1,2,1⟩,[0,r89,r475,r476,r477,r478,r479,r480,r481,r482,r483,-9408]),(⟨1,2,4⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨1,3,0⟩,[r267,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406]),(⟨1,3,1⟩,[0,r212,r484,r485,r486,r487,r488,r489,r490,r491,-4224]),(⟨1,3,4⟩,[r111,r497,r498,r499,r500,r501,r502,-352]),(⟨1,4,0⟩,[0,r407,r408,r409,r410,r411,r412,r413,r414,r415,-3360]),(⟨1,4,1⟩,[r158,r159,r160,r161,r162,r163,r164,r165,r166,1568]),(⟨1,4,2⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨1,4,3⟩,[r111,r497,r498,r499,r500,r501,r502,-352]),(⟨1,4,6⟩,[r29,r435,r436,r437,64]),(⟨1,5,0⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨1,6,0⟩,[r416,r424,r425,r158,r426,r427,r428,10080,r429]),(⟨1,6,1⟩,[0,r344,r492,r493,r494,r495,r496,768]),(⟨1,6,4⟩,[r29,r435,r436,r437,64]),(⟨1,7,0⟩,[r111,r430,r431,r56,r432,r433,r434,416]),(⟨1,10,0⟩,[r29,r435,r436,r437,64]),(⟨2,0,0⟩,[r79,r296,r297,r69,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨2,0,1⟩,[r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨2,0,2⟩,[r383,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448]),(⟨2,0,3⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,0,4⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨2,0,6⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨2,1,0⟩,[r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395]),(⟨2,1,1⟩,[0,r89,r475,r476,r477,r478,r479,r480,r481,r482,r483,-9408]),(⟨2,1,4⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨2,2,0⟩,[r383,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448]),(⟨2,3,0⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,4,0⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨2,4,1⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨2,6,0⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨3,0,0⟩,[r89,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319]),(⟨3,0,1⟩,[r267,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406]),(⟨3,0,2⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨3,0,3⟩,[r111,r30,r449,r450,r451,r452,r453,r454,r455,r456]),(⟨3,0,4⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨3,0,6⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨3,1,0⟩,[r267,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405,r406]),(⟨3,1,1⟩,[0,r212,r484,r485,r486,r487,r488,r489,r490,r491,-4224]),(⟨3,1,4⟩,[r111,r497,r498,r499,r500,r501,r502,-352]),(⟨3,2,0⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨3,3,0⟩,[r111,r30,r449,r450,r451,r452,r453,r454,r455,r456]),(⟨3,4,0⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨3,4,1⟩,[r111,r497,r498,r499,r500,r501,r502,-352]),(⟨3,6,0⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨4,0,0⟩,[r126,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨4,0,1⟩,[0,r407,r408,r409,r410,r411,r412,r413,r414,r415,-3360]),(⟨4,0,2⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨4,0,3⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨4,0,4⟩,[r174,r261,r262,r263,r264,r265,r266,-704]),(⟨4,0,7⟩,[r29,r435,r436,r437,64]),(⟨4,1,0⟩,[0,r407,r408,r409,r410,r411,r412,r413,r414,r415,-3360]),(⟨4,1,1⟩,[r158,r159,r160,r161,r162,r163,r164,r165,r166,1568]),(⟨4,1,2⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨4,1,3⟩,[r111,r497,r498,r499,r500,r501,r502,-352]),(⟨4,1,6⟩,[r29,r435,r436,r437,64]),(⟨4,2,0⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨4,2,1⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨4,3,0⟩,[r383,r457,r458,r459,r460,r461,r462,r463,-784]),(⟨4,3,1⟩,[r111,r497,r498,r499,r500,r501,r502,-352]),(⟨4,4,0⟩,[r174,r261,r262,r263,r264,r265,r266,-704]),(⟨4,6,1⟩,[r29,r435,r436,r437,64]),(⟨4,7,0⟩,[r29,r435,r436,r437,64]),(⟨5,0,0⟩,[r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨5,0,1⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨5,1,0⟩,[r416,r417,r216,r418,r419,r420,r421,r422,r423,784]),(⟨6,0,0⟩,[r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨6,0,1⟩,[r416,r424,r425,r158,r426,r427,r428,10080,r429]),(⟨6,0,2⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨6,0,3⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨6,1,0⟩,[r416,r424,r425,r158,r426,r427,r428,10080,r429]),(⟨6,1,1⟩,[0,r344,r492,r493,r494,r495,r496,768]),(⟨6,1,4⟩,[r29,r435,r436,r437,64]),(⟨6,2,0⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨6,3,0⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨6,4,1⟩,[r29,r435,r436,r437,64]),(⟨7,0,0⟩,[r125,r81,r352,r353,r354,r355,r356,r357,r358]),(⟨7,0,1⟩,[r111,r430,r431,r56,r432,r433,r434,416]),(⟨7,0,4⟩,[r29,r435,r436,r437,64]),(⟨7,1,0⟩,[r111,r430,r431,r56,r432,r433,r434,416]),(⟨7,4,0⟩,[r29,r435,r436,r437,64]),(⟨8,0,0⟩,[r79,r359,r112,r360,r361,r362,r363,r364]),(⟨9,0,0⟩,[r79,r177,r365,r366,r367,r368,r369]),(⟨10,0,1⟩,[r29,r435,r436,r437,64]),(⟨10,1,0⟩,[r29,r435,r436,r437,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r503) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 5 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r504) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[256,-3072,-7424,284672,-1881344,6325760,-12419840,14326784,-8530944,1315328]),(⟨6,0,1⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨6,0,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,0,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,1,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨6,1,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨6,1,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,3,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨7,0,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨9,0,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨10,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨10,1,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22])]

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[256,-3072,-7424,284672,-1881344,6325760,-12419840,14326784,-8530944,1315328]),(⟨0,6,1⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,6,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,6,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,7,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,7,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨0,7,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,9,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,10,1⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[-192,3648,-14784,-194240,2929792,-19442944,82148352,-244383872,532608320,-859788992,1017286976,-851730624,468100864,-143635072,16112768]),(⟨1,0,1⟩,[-192,4416,-35136,59968,998784,-9486848,45101696,-141289088,314238784,-506667456,586204864,-465931200,229354496,-52553088]),(⟨1,0,2⟩,[192,-2880,1728,216128,-1958912,9129088,-27372928,56589696,-81840704,80832192,-50542912,16485952,-1536640]),(⟨1,0,3⟩,[192,-3264,6720,190400,-1895808,9095040,-27635840,57429632,-82805568,80440640,-47839680,13017536]),(⟨1,1,0⟩,[-192,4416,-35136,59968,998784,-9486848,45101696,-141289088,314238784,-506667456,586204864,-465931200,229354496,-52553088]),(⟨1,1,1⟩,[0,1536,-32256,271872,-1238528,3322880,-4731904,-232448,16546816,-37616128,45183488,-30431744,8956416]),(⟨1,1,4⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,2,0⟩,[192,-2880,1728,216128,-1958912,9129088,-27372928,56589696,-81840704,80832192,-50542912,16485952,-1536640]),(⟨1,3,0⟩,[192,-3264,6720,190400,-1895808,9095040,-27635840,57429632,-82805568,80440640,-47839680,13017536]),(⟨1,4,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,6,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨1,6,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,6,4⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,10,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-256,5824,-43648,6976,2201856,-18852992,88847872,-278751616,616344064,-973592640,1081929856,-804536768,356876800,-68665856]),(⟨2,0,1⟩,[-64,3200,-48320,323712,-919296,-1041920,19061376,-79992832,196080576,-313654912,327878208,-207233152,61509504]),(⟨2,0,2⟩,[64,-1152,3392,73088,-889728,4855296,-15711616,32514048,-43425984,35405440,-14949312,1536640]),(⟨2,0,3⟩,[64,-1280,5440,59648,-848256,4822272,-15875968,33074944,-44024512,34822144,-13017536]),(⟨2,0,4⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨2,1,0⟩,[-64,3200,-48320,323712,-919296,-1041920,19061376,-79992832,196080576,-313654912,327878208,-207233152,61509504]),(⟨2,1,1⟩,[0,512,-12288,122368,-659456,2008064,-2990080,-545792,11382784,-22611456,21475328,-8956416]),(⟨2,1,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[64,-1152,3392,73088,-889728,4855296,-15711616,32514048,-43425984,35405440,-14949312,1536640]),(⟨2,3,0⟩,[64,-1280,5440,59648,-848256,4822272,-15875968,33074944,-44024512,34822144,-13017536]),(⟨2,4,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨2,4,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,6,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨3,0,0⟩,[512,-7232,-6144,705216,-6081024,27345536,-76439552,137070720,-146680832,58100160,65076224,-100899648,43782144]),(⟨3,0,1⟩,[384,-7040,31488,175104,-2646016,14250496,-45359360,94835968,-133079424,121325952,-64952832,14638848]),(⟨3,0,2⟩,[-384,4480,12800,-405760,2529280,-8397312,17270528,-22490880,17705344,-6918016,689920]),(⟨3,0,3⟩,[-384,5248,5376,-381696,2510336,-8488448,17591040,-22777088,17380224,-5844608]),(⟨3,0,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,1,0⟩,[384,-7040,31488,175104,-2646016,14250496,-45359360,94835968,-133079424,121325952,-64952832,14638848]),(⟨3,1,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨3,1,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[-384,4480,12800,-405760,2529280,-8397312,17270528,-22490880,17705344,-6918016,689920]),(⟨3,3,0⟩,[-384,5248,5376,-381696,2510336,-8488448,17591040,-22777088,17380224,-5844608]),(⟨3,4,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,4,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,6,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨4,0,0⟩,[640,-11968,53888,316224,-4772096,26192768,-85716736,185325440,-270693760,259783488,-149217152,38149440]),(⟨4,0,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨4,0,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨4,4,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨4,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨5,0,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨5,1,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨6,0,0⟩,[-128,2176,-2048,-97024,628992,-2162688,5171200,-8450304,8849280,-4529280]),(⟨6,0,1⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨6,0,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,0,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,1,0⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨6,1,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨6,1,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,3,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨7,0,1⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨9,0,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨10,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨10,1,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22])]

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[256,-3072,-7424,284672,-1881344,6325760,-12419840,14326784,-8530944,1315328]),(⟨0,0,7⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,0,8⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,0,9⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,1,0⟩,[-192,3648,-14784,-194240,2929792,-19442944,82148352,-244383872,532608320,-859788992,1017286976,-851730624,468100864,-143635072,16112768]),(⟨0,1,1⟩,[-192,4416,-35136,59968,998784,-9486848,45101696,-141289088,314238784,-506667456,586204864,-465931200,229354496,-52553088]),(⟨0,1,2⟩,[192,-2880,1728,216128,-1958912,9129088,-27372928,56589696,-81840704,80832192,-50542912,16485952,-1536640]),(⟨0,1,3⟩,[192,-3264,6720,190400,-1895808,9095040,-27635840,57429632,-82805568,80440640,-47839680,13017536]),(⟨0,1,6⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,1,7⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨0,1,10⟩,[-512,6144,-15360,-18432,60928]),(⟨0,2,0⟩,[-256,5824,-43648,6976,2201856,-18852992,88847872,-278751616,616344064,-973592640,1081929856,-804536768,356876800,-68665856]),(⟨0,2,1⟩,[-64,3200,-48320,323712,-919296,-1041920,19061376,-79992832,196080576,-313654912,327878208,-207233152,61509504]),(⟨0,2,2⟩,[64,-1152,3392,73088,-889728,4855296,-15711616,32514048,-43425984,35405440,-14949312,1536640]),(⟨0,2,3⟩,[64,-1280,5440,59648,-848256,4822272,-15875968,33074944,-44024512,34822144,-13017536]),(⟨0,2,4⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨0,2,6⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,3,0⟩,[512,-7232,-6144,705216,-6081024,27345536,-76439552,137070720,-146680832,58100160,65076224,-100899648,43782144]),(⟨0,3,1⟩,[384,-7040,31488,175104,-2646016,14250496,-45359360,94835968,-133079424,121325952,-64952832,14638848]),(⟨0,3,2⟩,[-384,4480,12800,-405760,2529280,-8397312,17270528,-22490880,17705344,-6918016,689920]),(⟨0,3,3⟩,[-384,5248,5376,-381696,2510336,-8488448,17591040,-22777088,17380224,-5844608]),(⟨0,3,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨0,3,6⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,4,0⟩,[640,-11968,53888,316224,-4772096,26192768,-85716736,185325440,-270693760,259783488,-149217152,38149440]),(⟨0,4,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨0,4,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,4,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,5,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨0,5,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨0,6,0⟩,[-128,2176,-2048,-97024,628992,-2162688,5171200,-8450304,8849280,-4529280]),(⟨0,6,1⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨0,6,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,6,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,7,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,7,1⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨0,7,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,9,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,10,1⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[-192,3648,-14784,-194240,2929792,-19442944,82148352,-244383872,532608320,-859788992,1017286976,-851730624,468100864,-143635072,16112768]),(⟨1,0,1⟩,[-192,4416,-35136,59968,998784,-9486848,45101696,-141289088,314238784,-506667456,586204864,-465931200,229354496,-52553088]),(⟨1,0,2⟩,[192,-2880,1728,216128,-1958912,9129088,-27372928,56589696,-81840704,80832192,-50542912,16485952,-1536640]),(⟨1,0,3⟩,[192,-3264,6720,190400,-1895808,9095040,-27635840,57429632,-82805568,80440640,-47839680,13017536]),(⟨1,0,6⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨1,0,7⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,0,10⟩,[-512,6144,-15360,-18432,60928]),(⟨1,1,0⟩,[-384,8832,-70272,119936,1997568,-18973696,90203392,-282578176,628477568,-1013334912,1172409728,-931862400,458708992,-105106176]),(⟨1,1,1⟩,[0,3072,-64512,543744,-2477056,6645760,-9463808,-464896,33093632,-75232256,90366976,-60863488,17912832]),(⟨1,1,4⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,1,6⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,2,0⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨1,2,1⟩,[0,512,-12288,122368,-659456,2008064,-2990080,-545792,11382784,-22611456,21475328,-8956416]),(⟨1,2,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,3,0⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨1,3,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨1,3,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,4,0⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨1,4,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,4,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,5,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,6,0⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨1,6,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,6,4⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨1,10,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-256,5824,-43648,6976,2201856,-18852992,88847872,-278751616,616344064,-973592640,1081929856,-804536768,356876800,-68665856]),(⟨2,0,1⟩,[-64,3200,-48320,323712,-919296,-1041920,19061376,-79992832,196080576,-313654912,327878208,-207233152,61509504]),(⟨2,0,2⟩,[64,-1152,3392,73088,-889728,4855296,-15711616,32514048,-43425984,35405440,-14949312,1536640]),(⟨2,0,3⟩,[64,-1280,5440,59648,-848256,4822272,-15875968,33074944,-44024512,34822144,-13017536]),(⟨2,0,4⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨2,0,6⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨2,1,0⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨2,1,1⟩,[0,512,-12288,122368,-659456,2008064,-2990080,-545792,11382784,-22611456,21475328,-8956416]),(⟨2,1,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[128,-2304,6784,146176,-1779456,9710592,-31423232,65028096,-86851968,70810880,-29898624,3073280]),(⟨2,3,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨2,4,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨2,4,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,6,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨3,0,0⟩,[512,-7232,-6144,705216,-6081024,27345536,-76439552,137070720,-146680832,58100160,65076224,-100899648,43782144]),(⟨3,0,1⟩,[384,-7040,31488,175104,-2646016,14250496,-45359360,94835968,-133079424,121325952,-64952832,14638848]),(⟨3,0,2⟩,[-384,4480,12800,-405760,2529280,-8397312,17270528,-22490880,17705344,-6918016,689920]),(⟨3,0,3⟩,[-384,5248,5376,-381696,2510336,-8488448,17591040,-22777088,17380224,-5844608]),(⟨3,0,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,0,6⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨3,1,0⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨3,1,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨3,1,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨3,3,0⟩,[-768,10496,10752,-763392,5020672,-16976896,35182080,-45554176,34760448,-11689216]),(⟨3,4,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,4,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,6,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨4,0,0⟩,[640,-11968,53888,316224,-4772096,26192768,-85716736,185325440,-270693760,259783488,-149217152,38149440]),(⟨4,0,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨4,0,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨4,1,0⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨4,1,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨4,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨4,2,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨4,2,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨4,3,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨4,3,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,4,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨4,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨4,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨5,0,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨5,1,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨6,0,0⟩,[-128,2176,-2048,-97024,628992,-2162688,5171200,-8450304,8849280,-4529280]),(⟨6,0,1⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨6,0,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,0,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,1,0⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨6,1,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨6,1,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,3,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨7,0,1⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨9,0,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨10,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨10,1,0⟩,[-512,6144,-15360,-18432,60928])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,576,-10752,38976,626304,-8654976,53407104,-205013376,534191616,-967711680,1197970944,-936940992,345356160,69760512,-104316288,17756928]),(⟨0,0,1⟩,[-192,4224,-27840,-94976,2820736,-22726144,109492224,-360622592,848330816,-1436440448,1715610944,-1360162560,608608768,-66922240,-41802880]),(⟨0,0,2⟩,[-256,5248,-35200,6400,1529856,-13233920,65347840,-218792704,518848768,-876765312,1034854528,-808354304,369897472,-70359296]),(⟨0,0,3⟩,[512,-7808,3456,690048,-6684288,32837888,-100034048,197972736,-245920256,155173248,21786752,-110014080,58128000]),(⟨0,0,4⟩,[640,-11968,53888,316224,-4772096,26192768,-85716736,185325440,-270693760,259783488,-149217152,38149440]),(⟨0,0,5⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨0,0,6⟩,[-128,2176,-2048,-97024,628992,-2162688,5171200,-8450304,8849280,-4529280]),(⟨0,0,7⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,0,8⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,0,9⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,1,0⟩,[-192,4224,-27840,-94976,2820736,-22726144,109492224,-360622592,848330816,-1436440448,1715610944,-1360162560,608608768,-66922240,-41802880]),(⟨0,1,1⟩,[-384,8832,-74880,215168,1228032,-15788032,83269888,-277730560,642955904,-1059814272,1231891328,-964526976,455174656,-95235840]),(⟨0,1,2⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨0,1,3⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨0,1,4⟩,[0,-4224,75776,-498176,1550080,-2047744,-1330432,9270784,-14717696,11096960,-3198720]),(⟨0,1,5⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨0,1,6⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨0,1,7⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨0,1,10⟩,[-512,6144,-15360,-18432,60928]),(⟨0,2,0⟩,[-256,5248,-35200,6400,1529856,-13233920,65347840,-218792704,518848768,-876765312,1034854528,-808354304,369897472,-70359296]),(⟨0,2,1⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨0,2,2⟩,[128,-2304,6784,146176,-1779456,9710592,-31423232,65028096,-86851968,70810880,-29898624,3073280]),(⟨0,2,3⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨0,2,4⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨0,2,6⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,3,0⟩,[512,-7808,3456,690048,-6684288,32837888,-100034048,197972736,-245920256,155173248,21786752,-110014080,58128000]),(⟨0,3,1⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨0,3,2⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨0,3,3⟩,[-768,10496,10752,-763392,5020672,-16976896,35182080,-45554176,34760448,-11689216]),(⟨0,3,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨0,3,6⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,4,0⟩,[640,-11968,53888,316224,-4772096,26192768,-85716736,185325440,-270693760,259783488,-149217152,38149440]),(⟨0,4,1⟩,[0,-4224,75776,-498176,1550080,-2047744,-1330432,9270784,-14717696,11096960,-3198720]),(⟨0,4,2⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨0,4,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨0,4,4⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨0,4,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,5,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨0,5,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨0,6,0⟩,[-128,2176,-2048,-97024,628992,-2162688,5171200,-8450304,8849280,-4529280]),(⟨0,6,1⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨0,6,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,6,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,7,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨0,7,1⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨0,7,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨0,9,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨0,10,1⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[-192,4224,-27840,-94976,2820736,-22726144,109492224,-360622592,848330816,-1436440448,1715610944,-1360162560,608608768,-66922240,-41802880]),(⟨1,0,1⟩,[-384,8832,-74880,215168,1228032,-15788032,83269888,-277730560,642955904,-1059814272,1231891328,-964526976,455174656,-95235840]),(⟨1,0,2⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨1,0,3⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨1,0,4⟩,[0,-4224,75776,-498176,1550080,-2047744,-1330432,9270784,-14717696,11096960,-3198720]),(⟨1,0,5⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,0,6⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨1,0,7⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨1,0,10⟩,[-512,6144,-15360,-18432,60928]),(⟨1,1,0⟩,[-384,8832,-74880,215168,1228032,-15788032,83269888,-277730560,642955904,-1059814272,1231891328,-964526976,455174656,-95235840]),(⟨1,1,1⟩,[0,4608,-96768,815616,-3715584,9968640,-14195712,-697344,49640448,-112848384,135550464,-91295232,26869248]),(⟨1,1,2⟩,[0,512,-12288,122368,-659456,2008064,-2990080,-545792,11382784,-22611456,21475328,-8956416]),(⟨1,1,3⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨1,1,4⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,1,6⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,2,0⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨1,2,1⟩,[0,512,-12288,122368,-659456,2008064,-2990080,-545792,11382784,-22611456,21475328,-8956416]),(⟨1,2,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,3,0⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨1,3,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨1,3,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,4,0⟩,[0,-4224,75776,-498176,1550080,-2047744,-1330432,9270784,-14717696,11096960,-3198720]),(⟨1,4,1⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,4,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,4,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,4,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,5,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,6,0⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨1,6,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨1,6,4⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨1,10,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-256,5248,-35200,6400,1529856,-13233920,65347840,-218792704,518848768,-876765312,1034854528,-808354304,369897472,-70359296]),(⟨2,0,1⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨2,0,2⟩,[128,-2304,6784,146176,-1779456,9710592,-31423232,65028096,-86851968,70810880,-29898624,3073280]),(⟨2,0,3⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨2,0,4⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨2,0,6⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨2,1,0⟩,[128,320,-46592,539840,-2878208,8087168,-8311552,-23403136,114239872,-232822720,277335296,-190747200,59972864]),(⟨2,1,1⟩,[0,512,-12288,122368,-659456,2008064,-2990080,-545792,11382784,-22611456,21475328,-8956416]),(⟨2,1,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[128,-2304,6784,146176,-1779456,9710592,-31423232,65028096,-86851968,70810880,-29898624,3073280]),(⟨2,3,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨2,4,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨2,4,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,6,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨3,0,0⟩,[512,-7808,3456,690048,-6684288,32837888,-100034048,197972736,-245920256,155173248,21786752,-110014080,58128000]),(⟨3,0,1⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨3,0,2⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨3,0,3⟩,[-768,10496,10752,-763392,5020672,-16976896,35182080,-45554176,34760448,-11689216]),(⟨3,0,4⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,0,6⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨3,1,0⟩,[576,-10304,38208,365504,-4541824,23345536,-72995200,152265600,-215884992,201766592,-112792512,27656384]),(⟨3,1,1⟩,[0,-3072,54272,-352256,1110016,-1632256,-391168,6283264,-11890688,10843136,-4021248]),(⟨3,1,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨3,3,0⟩,[-768,10496,10752,-763392,5020672,-16976896,35182080,-45554176,34760448,-11689216]),(⟨3,4,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,4,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,6,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨4,0,0⟩,[640,-11968,53888,316224,-4772096,26192768,-85716736,185325440,-270693760,259783488,-149217152,38149440]),(⟨4,0,1⟩,[0,-4224,75776,-498176,1550080,-2047744,-1330432,9270784,-14717696,11096960,-3198720]),(⟨4,0,2⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨4,0,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨4,0,4⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨4,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨4,1,0⟩,[0,-4224,75776,-498176,1550080,-2047744,-1330432,9270784,-14717696,11096960,-3198720]),(⟨4,1,1⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨4,1,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨4,1,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨4,2,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨4,2,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨4,3,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨4,3,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,4,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨4,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨4,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-320,3200,18240,-346112,1681024,-3575040,1394560,10584064,-26319168,27904128,-12327616]),(⟨5,0,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨5,1,0⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨6,0,0⟩,[-128,2176,-2048,-97024,628992,-2162688,5171200,-8450304,8849280,-4529280]),(⟨6,0,1⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨6,0,2⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,0,3⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,1,0⟩,[384,-6912,37120,768,-808960,3775232,-8311040,9596160,-5036416]),(⟨6,1,1⟩,[0,-2048,28672,-116736,122880,206848,-708608,731136]),(⟨6,1,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨6,3,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨6,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-4096,12544,108032,-1022720,3773440,-7536896,8304128,-4290048]),(⟨7,0,1⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨7,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[-768,9984,-33024,1280,135936,-218880,-28416,396032]),(⟨7,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-256,2048,17664,-219648,776448,-1295360,1041152,-125440]),(⟨9,0,0⟩,[-256,2560,14592,-218112,790784,-1324544,1062656]),(⟨10,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨10,1,0⟩,[-512,6144,-15360,-18432,60928])]


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
    (Poly.add (Poly.scale (K.ofRat r505) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 5).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r503*r504 : ℚ)=r505 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 5 r503 r504 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=5 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 5).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C075

#print axioms Coulomb8.Columns.C075.sound
