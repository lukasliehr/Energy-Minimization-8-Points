import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C068

def r0 : ℚ := { num := -24, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -3240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 13488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -33480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 47856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -32760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 1968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 7296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 8, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 1248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -48880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 63616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -44024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 9440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 3200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -1400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 6512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 26880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -19592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 6000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -3280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 11800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -24176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 26168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -11360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -1968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -15808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 17328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -8720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 40, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -4192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 3096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -3872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 3392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 1232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -6960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 22112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -41824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 47024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -30480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 10016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -8, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 1672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -5328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 7088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -3960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -1952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 7456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -14976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 16272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -8288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 48, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -3616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -1760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 24, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -1712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -4224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 1440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -7248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 16896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -19872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 12192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -3168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 4944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -4976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -2752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -48, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 3616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -12, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -1620, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 6744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -16740, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 23928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -16380, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 3648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 4, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -72, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -24440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 31808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -22012, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 4720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 1600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -700, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 3256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 13440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -9796, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 3000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 252, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -1640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 5900, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -12088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 13084, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -5680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -452, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -7904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 8664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -4360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 20, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -268, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 1120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -2096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 1548, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 188, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -1936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 88, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -56, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -3480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 11056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -20912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 23512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -15240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 5008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -4, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 56, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 172, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 836, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -2664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 3544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -1980, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 3728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -7488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 8136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -4144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -1808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 12, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -164, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 444, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -2112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 1728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -3624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 8448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -9936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 6096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 2472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -2488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -1376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -1120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 1808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 1, den := 68, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9],[r10,r11,r12,-392,1336,r13,r14,r15,r16,r17],[0,r0,r18,r19,r20,-1064,r21,r22,r23],[r24,r25,r26,r27,r28,r29,r30,r31],[0,r32,r33,r34,r35,r36,r37],[r38,r39,r40,r41,r42,r43],[0,r44,r45,r46,r47],[r48,r49,r50,r51],[0,r52,r53],[],[],[],[],[0,r54,r55,r56,r57,r58,r59,r60,r61],[r62,r63,r64,r65,r66,r67,r68,r69],[0,r32,r70,r71,r72,r73,r74],[0,r75,r76,r40,r77,144],[0,r54,r78,r79,r80],[0,r24,r81,-32],[],[],[],[],[],[0,0,r24,r82,r83,r82,r18],[r84,r85,r55,r86,24,r87],[],[r48,r49,r50,r51],[],[],[],[],[],[0,r53,128,r88,r89],[],[0,r52,r53],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r54,r90,r91,r92,r93,r94,-240],[r95,r96,r55,r97,r98,r99,144],[0,r75,r100,r101,r102,112],[r103,r104,r105,r106,-144],[0,r24,r81,-32],[r107,r108,32],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118]),(⟨0,0,1⟩,[r119,r120,r121,-196,668,r122,r123,r124,r125,r126]),(⟨0,0,2⟩,[0,r109,r63,r127,r128,-532,r129,r130,r131]),(⟨0,0,3⟩,[r48,r132,r133,r134,r135,r136,r137,r138]),(⟨0,0,4⟩,[0,r139,r140,r141,r142,r143,r144]),(⟨0,0,5⟩,[r145,r146,r147,r148,r149,r150]),(⟨0,0,6⟩,[0,r11,r151,r152,r153]),(⟨0,0,7⟩,[r62,r154,r155,r156]),(⟨0,0,8⟩,[0,r157,r158]),(⟨0,1,0⟩,[r119,r120,r121,-196,668,r122,r123,r124,r125,r126]),(⟨0,1,1⟩,[0,r103,r159,r160,r161,r162,r163,r164,r165]),(⟨0,1,2⟩,[r166,r167,r168,r169,r170,r171,r172,r173]),(⟨0,1,3⟩,[0,r139,r174,r175,r176,r177,r178]),(⟨0,1,4⟩,[0,r84,r50,r147,r179,72]),(⟨0,1,5⟩,[0,r103,r180,r181,r182]),(⟨0,1,6⟩,[0,r48,r183,-16]),(⟨0,2,0⟩,[0,r109,r63,r127,r128,-532,r129,r130,r131]),(⟨0,2,1⟩,[r166,r167,r168,r169,r170,r171,r172,r173]),(⟨0,2,2⟩,[0,0,r48,r184,r185,r184,r63]),(⟨0,2,3⟩,[r186,r187,r159,r188,12,r189]),(⟨0,2,5⟩,[r62,r154,r155,r156]),(⟨0,3,0⟩,[r48,r132,r133,r134,r135,r136,r137,r138]),(⟨0,3,1⟩,[0,r139,r174,r175,r176,r177,r178]),(⟨0,3,2⟩,[r186,r187,r159,r188,12,r189]),(⟨0,3,3⟩,[0,r158,64,r190,r191]),(⟨0,3,5⟩,[0,r157,r158]),(⟨0,4,0⟩,[0,r139,r140,r141,r142,r143,r144]),(⟨0,4,1⟩,[0,r84,r50,r147,r179,72]),(⟨0,5,0⟩,[r145,r146,r147,r148,r149,r150]),(⟨0,5,1⟩,[0,r103,r180,r181,r182]),(⟨0,5,2⟩,[r62,r154,r155,r156]),(⟨0,5,3⟩,[0,r157,r158]),(⟨0,6,0⟩,[0,r11,r151,r152,r153]),(⟨0,6,1⟩,[0,r48,r183,-16]),(⟨0,7,0⟩,[r62,r154,r155,r156]),(⟨0,8,0⟩,[0,r157,r158]),(⟨1,0,0⟩,[r119,r120,r121,-196,668,r122,r123,r124,r125,r126]),(⟨1,0,1⟩,[0,r103,r159,r160,r161,r162,r163,r164,r165]),(⟨1,0,2⟩,[r166,r167,r168,r169,r170,r171,r172,r173]),(⟨1,0,3⟩,[0,r139,r174,r175,r176,r177,r178]),(⟨1,0,4⟩,[0,r84,r50,r147,r179,72]),(⟨1,0,5⟩,[0,r103,r180,r181,r182]),(⟨1,0,6⟩,[0,r48,r183,-16]),(⟨1,1,0⟩,[0,r103,r159,r160,r161,r162,r163,r164,r165]),(⟨1,1,1⟩,[0,r103,r192,r193,r194,r195,r196,-120]),(⟨1,1,2⟩,[r10,r197,r159,r198,r199,r200,72]),(⟨1,1,3⟩,[0,r84,r44,r201,r202,56]),(⟨1,1,4⟩,[r0,r203,r204,r205,-72]),(⟨1,1,5⟩,[0,r48,r183,-16]),(⟨1,1,6⟩,[r95,r206,16]),(⟨1,2,0⟩,[r166,r167,r168,r169,r170,r171,r172,r173]),(⟨1,2,1⟩,[r10,r197,r159,r198,r199,r200,72]),(⟨1,3,0⟩,[0,r139,r174,r175,r176,r177,r178]),(⟨1,3,1⟩,[0,r84,r44,r201,r202,56]),(⟨1,4,0⟩,[0,r84,r50,r147,r179,72]),(⟨1,4,1⟩,[r0,r203,r204,r205,-72]),(⟨1,5,0⟩,[0,r103,r180,r181,r182]),(⟨1,5,1⟩,[0,r48,r183,-16]),(⟨1,6,0⟩,[0,r48,r183,-16]),(⟨1,6,1⟩,[r95,r206,16]),(⟨2,0,0⟩,[0,r109,r63,r127,r128,-532,r129,r130,r131]),(⟨2,0,1⟩,[r166,r167,r168,r169,r170,r171,r172,r173]),(⟨2,0,2⟩,[0,0,r48,r184,r185,r184,r63]),(⟨2,0,3⟩,[r186,r187,r159,r188,12,r189]),(⟨2,0,5⟩,[r62,r154,r155,r156]),(⟨2,1,0⟩,[r166,r167,r168,r169,r170,r171,r172,r173]),(⟨2,1,1⟩,[r10,r197,r159,r198,r199,r200,72]),(⟨2,2,0⟩,[0,0,r48,r184,r185,r184,r63]),(⟨2,3,0⟩,[r186,r187,r159,r188,12,r189]),(⟨2,5,0⟩,[r62,r154,r155,r156]),(⟨3,0,0⟩,[r48,r132,r133,r134,r135,r136,r137,r138]),(⟨3,0,1⟩,[0,r139,r174,r175,r176,r177,r178]),(⟨3,0,2⟩,[r186,r187,r159,r188,12,r189]),(⟨3,0,3⟩,[0,r158,64,r190,r191]),(⟨3,0,5⟩,[0,r157,r158]),(⟨3,1,0⟩,[0,r139,r174,r175,r176,r177,r178]),(⟨3,1,1⟩,[0,r84,r44,r201,r202,56]),(⟨3,2,0⟩,[r186,r187,r159,r188,12,r189]),(⟨3,3,0⟩,[0,r158,64,r190,r191]),(⟨3,5,0⟩,[0,r157,r158]),(⟨4,0,0⟩,[0,r139,r140,r141,r142,r143,r144]),(⟨4,0,1⟩,[0,r84,r50,r147,r179,72]),(⟨4,1,0⟩,[0,r84,r50,r147,r179,72]),(⟨4,1,1⟩,[r0,r203,r204,r205,-72]),(⟨5,0,0⟩,[r145,r146,r147,r148,r149,r150]),(⟨5,0,1⟩,[0,r103,r180,r181,r182]),(⟨5,0,2⟩,[r62,r154,r155,r156]),(⟨5,0,3⟩,[0,r157,r158]),(⟨5,1,0⟩,[0,r103,r180,r181,r182]),(⟨5,1,1⟩,[0,r48,r183,-16]),(⟨5,2,0⟩,[r62,r154,r155,r156]),(⟨5,3,0⟩,[0,r157,r158]),(⟨6,0,0⟩,[0,r11,r151,r152,r153]),(⟨6,0,1⟩,[0,r48,r183,-16]),(⟨6,1,0⟩,[0,r48,r183,-16]),(⟨6,1,1⟩,[r95,r206,16]),(⟨7,0,0⟩,[r62,r154,r155,r156]),(⟨8,0,0⟩,[0,r157,r158])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r207) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r208) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[32,-416,2016,-4960,5376,-1024]),(⟨5,0,1⟩,[0,-192,1408,-3520,3328]),(⟨5,0,2⟩,[-32,352,-608,-224]),(⟨5,0,3⟩,[0,256,-768]),(⟨5,1,0⟩,[0,-192,1408,-3520,3328]),(⟨5,1,1⟩,[0,-64,640,-1088]),(⟨5,2,0⟩,[-32,352,-608,-224]),(⟨5,3,0⟩,[0,256,-768]),(⟨6,0,0⟩,[0,-192,1408,-3520,3328]),(⟨6,0,1⟩,[0,-64,640,-1088]),(⟨6,1,0⟩,[0,-64,640,-1088]),(⟨6,1,1⟩,[64,-640,1088]),(⟨7,0,0⟩,[-32,352,-608,-224]),(⟨8,0,0⟩,[0,256,-768])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9])]

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[32,-416,2016,-4960,5376,-1024]),(⟨0,5,1⟩,[0,-192,1408,-3520,3328]),(⟨0,5,2⟩,[-32,352,-608,-224]),(⟨0,5,3⟩,[0,256,-768]),(⟨0,6,0⟩,[0,-192,1408,-3520,3328]),(⟨0,6,1⟩,[0,-64,640,-1088]),(⟨0,7,0⟩,[-32,352,-608,-224]),(⟨0,8,0⟩,[0,256,-768]),(⟨1,0,0⟩,[16,-288,2208,-9776,27568,-51296,63776,-52048,24448,-3584]),(⟨1,0,1⟩,[0,-96,1184,-6240,18560,-34336,40928,-30624,11648]),(⟨1,0,2⟩,[-16,256,-1344,3344,-4528,3456,-896,-784]),(⟨1,0,3⟩,[0,128,-1024,3200,-5248,5120,-2688]),(⟨1,1,0⟩,[0,-96,1184,-6240,18560,-34336,40928,-30624,11648]),(⟨1,1,1⟩,[0,-32,480,-2464,6272,-9184,8224,-3808]),(⟨1,2,0⟩,[-16,256,-1344,3344,-4528,3456,-896,-784]),(⟨1,3,0⟩,[0,128,-1024,3200,-5248,5120,-2688]),(⟨1,5,0⟩,[0,-192,1408,-3520,3328]),(⟨1,5,1⟩,[0,-64,640,-1088]),(⟨1,6,0⟩,[0,-64,640,-1088]),(⟨1,6,1⟩,[64,-640,1088]),(⟨2,0,0⟩,[0,-96,1216,-6688,20992,-41312,51264,-37024,12672]),(⟨2,0,1⟩,[0,-32,480,-2656,7872,-14112,15072,-7136]),(⟨2,0,2⟩,[0,0,-32,384,-960,384,224]),(⟨2,0,3⟩,[0,0,0,256,-1024,768]),(⟨2,1,0⟩,[0,-32,480,-2656,7872,-14112,15072,-7136]),(⟨2,1,1⟩,[32,-480,2464,-6336,9888,-9952,4896]),(⟨2,2,0⟩,[0,0,-32,384,-960,384,224]),(⟨2,3,0⟩,[0,0,0,256,-1024,768]),(⟨2,5,0⟩,[-32,352,-608,-224]),(⟨3,0,0⟩,[-64,1008,-6176,20528,-39904,43888,-22336,496]),(⟨3,0,1⟩,[0,288,-2880,11712,-24704,27424,-13888]),(⟨3,0,2⟩,[48,-656,2464,-3680,1840,1008]),(⟨3,0,3⟩,[0,-384,2176,-4224,3456]),(⟨3,1,0⟩,[0,288,-2880,11712,-24704,27424,-13888]),(⟨3,1,1⟩,[0,96,-1152,3776,-5504,3808]),(⟨3,2,0⟩,[48,-656,2464,-3680,1840,1008]),(⟨3,3,0⟩,[0,-384,2176,-4224,3456]),(⟨3,5,0⟩,[0,256,-768]),(⟨4,0,0⟩,[0,416,-3936,15360,-31616,34656,-17440]),(⟨4,0,1⟩,[0,96,-1216,4480,-7232,4896]),(⟨4,1,0⟩,[0,96,-1216,4480,-7232,4896]),(⟨4,1,1⟩,[-96,1216,-4480,7232,-4896]),(⟨5,0,0⟩,[80,-1072,4480,-8384,6192,752]),(⟨5,0,1⟩,[0,-192,1408,-3520,3328]),(⟨5,0,2⟩,[-32,352,-608,-224]),(⟨5,0,3⟩,[0,256,-768]),(⟨5,1,0⟩,[0,-192,1408,-3520,3328]),(⟨5,1,1⟩,[0,-64,640,-1088]),(⟨5,2,0⟩,[-32,352,-608,-224]),(⟨5,3,0⟩,[0,256,-768]),(⟨6,0,0⟩,[0,-576,3584,-7744,6784]),(⟨6,0,1⟩,[0,-64,640,-1088]),(⟨6,1,0⟩,[0,-64,640,-1088]),(⟨6,1,1⟩,[64,-640,1088]),(⟨7,0,0⟩,[-32,352,-608,-224]),(⟨8,0,0⟩,[0,256,-768])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9])]

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[32,-416,2016,-4960,5376,-1024]),(⟨0,0,6⟩,[0,-192,1408,-3520,3328]),(⟨0,0,7⟩,[-32,352,-608,-224]),(⟨0,0,8⟩,[0,256,-768]),(⟨0,1,0⟩,[16,-288,2208,-9776,27568,-51296,63776,-52048,24448,-3584]),(⟨0,1,1⟩,[0,-96,1184,-6240,18560,-34336,40928,-30624,11648]),(⟨0,1,2⟩,[-16,256,-1344,3344,-4528,3456,-896,-784]),(⟨0,1,3⟩,[0,128,-1024,3200,-5248,5120,-2688]),(⟨0,1,5⟩,[0,-192,1408,-3520,3328]),(⟨0,1,6⟩,[0,-64,640,-1088]),(⟨0,2,0⟩,[0,-96,1216,-6688,20992,-41312,51264,-37024,12672]),(⟨0,2,1⟩,[0,-32,480,-2656,7872,-14112,15072,-7136]),(⟨0,2,2⟩,[0,0,-32,384,-960,384,224]),(⟨0,2,3⟩,[0,0,0,256,-1024,768]),(⟨0,2,5⟩,[-32,352,-608,-224]),(⟨0,3,0⟩,[-64,1008,-6176,20528,-39904,43888,-22336,496]),(⟨0,3,1⟩,[0,288,-2880,11712,-24704,27424,-13888]),(⟨0,3,2⟩,[48,-656,2464,-3680,1840,1008]),(⟨0,3,3⟩,[0,-384,2176,-4224,3456]),(⟨0,3,5⟩,[0,256,-768]),(⟨0,4,0⟩,[0,416,-3936,15360,-31616,34656,-17440]),(⟨0,4,1⟩,[0,96,-1216,4480,-7232,4896]),(⟨0,5,0⟩,[80,-1072,4480,-8384,6192,752]),(⟨0,5,1⟩,[0,-192,1408,-3520,3328]),(⟨0,5,2⟩,[-32,352,-608,-224]),(⟨0,5,3⟩,[0,256,-768]),(⟨0,6,0⟩,[0,-576,3584,-7744,6784]),(⟨0,6,1⟩,[0,-64,640,-1088]),(⟨0,7,0⟩,[-32,352,-608,-224]),(⟨0,8,0⟩,[0,256,-768]),(⟨1,0,0⟩,[16,-288,2208,-9776,27568,-51296,63776,-52048,24448,-3584]),(⟨1,0,1⟩,[0,-96,1184,-6240,18560,-34336,40928,-30624,11648]),(⟨1,0,2⟩,[-16,256,-1344,3344,-4528,3456,-896,-784]),(⟨1,0,3⟩,[0,128,-1024,3200,-5248,5120,-2688]),(⟨1,0,5⟩,[0,-192,1408,-3520,3328]),(⟨1,0,6⟩,[0,-64,640,-1088]),(⟨1,1,0⟩,[0,-192,2368,-12480,37120,-68672,81856,-61248,23296]),(⟨1,1,1⟩,[0,-64,960,-4928,12544,-18368,16448,-7616]),(⟨1,1,5⟩,[0,-64,640,-1088]),(⟨1,1,6⟩,[64,-640,1088]),(⟨1,2,0⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨1,2,1⟩,[32,-480,2464,-6336,9888,-9952,4896]),(⟨1,3,0⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨1,3,1⟩,[0,96,-1152,3776,-5504,3808]),(⟨1,4,0⟩,[0,96,-1216,4480,-7232,4896]),(⟨1,4,1⟩,[-96,1216,-4480,7232,-4896]),(⟨1,5,0⟩,[0,-192,1408,-3520,3328]),(⟨1,5,1⟩,[0,-64,640,-1088]),(⟨1,6,0⟩,[0,-64,640,-1088]),(⟨1,6,1⟩,[64,-640,1088]),(⟨2,0,0⟩,[0,-96,1216,-6688,20992,-41312,51264,-37024,12672]),(⟨2,0,1⟩,[0,-32,480,-2656,7872,-14112,15072,-7136]),(⟨2,0,2⟩,[0,0,-32,384,-960,384,224]),(⟨2,0,3⟩,[0,0,0,256,-1024,768]),(⟨2,0,5⟩,[-32,352,-608,-224]),(⟨2,1,0⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨2,1,1⟩,[32,-480,2464,-6336,9888,-9952,4896]),(⟨2,2,0⟩,[0,0,-64,768,-1920,768,448]),(⟨2,3,0⟩,[48,-656,2464,-3424,816,1776]),(⟨2,5,0⟩,[-32,352,-608,-224]),(⟨3,0,0⟩,[-64,1008,-6176,20528,-39904,43888,-22336,496]),(⟨3,0,1⟩,[0,288,-2880,11712,-24704,27424,-13888]),(⟨3,0,2⟩,[48,-656,2464,-3680,1840,1008]),(⟨3,0,3⟩,[0,-384,2176,-4224,3456]),(⟨3,0,5⟩,[0,256,-768]),(⟨3,1,0⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨3,1,1⟩,[0,96,-1152,3776,-5504,3808]),(⟨3,2,0⟩,[48,-656,2464,-3424,816,1776]),(⟨3,3,0⟩,[0,-768,4352,-8448,6912]),(⟨3,5,0⟩,[0,256,-768]),(⟨4,0,0⟩,[0,416,-3936,15360,-31616,34656,-17440]),(⟨4,0,1⟩,[0,96,-1216,4480,-7232,4896]),(⟨4,1,0⟩,[0,96,-1216,4480,-7232,4896]),(⟨4,1,1⟩,[-96,1216,-4480,7232,-4896]),(⟨5,0,0⟩,[80,-1072,4480,-8384,6192,752]),(⟨5,0,1⟩,[0,-192,1408,-3520,3328]),(⟨5,0,2⟩,[-32,352,-608,-224]),(⟨5,0,3⟩,[0,256,-768]),(⟨5,1,0⟩,[0,-192,1408,-3520,3328]),(⟨5,1,1⟩,[0,-64,640,-1088]),(⟨5,2,0⟩,[-32,352,-608,-224]),(⟨5,3,0⟩,[0,256,-768]),(⟨6,0,0⟩,[0,-576,3584,-7744,6784]),(⟨6,0,1⟩,[0,-64,640,-1088]),(⟨6,1,0⟩,[0,-64,640,-1088]),(⟨6,1,1⟩,[64,-640,1088]),(⟨7,0,0⟩,[-32,352,-608,-224]),(⟨8,0,0⟩,[0,256,-768])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-48,864,-6480,26976,-66960,95712,-65520,3936,14592,-3072]),(⟨0,0,1⟩,[16,-288,2496,-13328,45424,-97760,127232,-88048,18880,6400]),(⟨0,0,2⟩,[0,-48,448,-2800,13024,-36176,53760,-39184,12000]),(⟨0,0,3⟩,[-64,1008,-6560,23600,-48352,52336,-22720,-1808]),(⟨0,0,4⟩,[0,416,-3936,15360,-31616,34656,-17440]),(⟨0,0,5⟩,[80,-1072,4480,-8384,6192,752]),(⟨0,0,6⟩,[0,-576,3584,-7744,6784]),(⟨0,0,7⟩,[-32,352,-608,-224]),(⟨0,0,8⟩,[0,256,-768]),(⟨0,1,0⟩,[16,-288,2496,-13328,45424,-97760,127232,-88048,18880,6400]),(⟨0,1,1⟩,[0,-192,2464,-13920,44224,-83648,94048,-60960,20032]),(⟨0,1,2⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨0,1,3⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨0,1,4⟩,[0,96,-1216,4480,-7232,4896]),(⟨0,1,5⟩,[0,-192,1408,-3520,3328]),(⟨0,1,6⟩,[0,-64,640,-1088]),(⟨0,2,0⟩,[0,-48,448,-2800,13024,-36176,53760,-39184,12000]),(⟨0,2,1⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨0,2,2⟩,[0,0,-64,768,-1920,768,448]),(⟨0,2,3⟩,[48,-656,2464,-3424,816,1776]),(⟨0,2,5⟩,[-32,352,-608,-224]),(⟨0,3,0⟩,[-64,1008,-6560,23600,-48352,52336,-22720,-1808]),(⟨0,3,1⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨0,3,2⟩,[48,-656,2464,-3424,816,1776]),(⟨0,3,3⟩,[0,-768,4352,-8448,6912]),(⟨0,3,5⟩,[0,256,-768]),(⟨0,4,0⟩,[0,416,-3936,15360,-31616,34656,-17440]),(⟨0,4,1⟩,[0,96,-1216,4480,-7232,4896]),(⟨0,5,0⟩,[80,-1072,4480,-8384,6192,752]),(⟨0,5,1⟩,[0,-192,1408,-3520,3328]),(⟨0,5,2⟩,[-32,352,-608,-224]),(⟨0,5,3⟩,[0,256,-768]),(⟨0,6,0⟩,[0,-576,3584,-7744,6784]),(⟨0,6,1⟩,[0,-64,640,-1088]),(⟨0,7,0⟩,[-32,352,-608,-224]),(⟨0,8,0⟩,[0,256,-768]),(⟨1,0,0⟩,[16,-288,2496,-13328,45424,-97760,127232,-88048,18880,6400]),(⟨1,0,1⟩,[0,-192,2464,-13920,44224,-83648,94048,-60960,20032]),(⟨1,0,2⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨1,0,3⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨1,0,4⟩,[0,96,-1216,4480,-7232,4896]),(⟨1,0,5⟩,[0,-192,1408,-3520,3328]),(⟨1,0,6⟩,[0,-64,640,-1088]),(⟨1,1,0⟩,[0,-192,2464,-13920,44224,-83648,94048,-60960,20032]),(⟨1,1,1⟩,[0,-192,2880,-14496,33792,-39744,24384,-8160]),(⟨1,1,2⟩,[32,-480,2464,-6336,9888,-9952,4896]),(⟨1,1,3⟩,[0,96,-1152,3776,-5504,3808]),(⟨1,1,4⟩,[-96,1216,-4480,7232,-4896]),(⟨1,1,5⟩,[0,-64,640,-1088]),(⟨1,1,6⟩,[64,-640,1088]),(⟨1,2,0⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨1,2,1⟩,[32,-480,2464,-6336,9888,-9952,4896]),(⟨1,3,0⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨1,3,1⟩,[0,96,-1152,3776,-5504,3808]),(⟨1,4,0⟩,[0,96,-1216,4480,-7232,4896]),(⟨1,4,1⟩,[-96,1216,-4480,7232,-4896]),(⟨1,5,0⟩,[0,-192,1408,-3520,3328]),(⟨1,5,1⟩,[0,-64,640,-1088]),(⟨1,6,0⟩,[0,-64,640,-1088]),(⟨1,6,1⟩,[64,-640,1088]),(⟨2,0,0⟩,[0,-48,448,-2800,13024,-36176,53760,-39184,12000]),(⟨2,0,1⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨2,0,2⟩,[0,0,-64,768,-1920,768,448]),(⟨2,0,3⟩,[48,-656,2464,-3424,816,1776]),(⟨2,0,5⟩,[-32,352,-608,-224]),(⟨2,1,0⟩,[-16,224,-864,688,3344,-10656,14176,-7920]),(⟨2,1,1⟩,[32,-480,2464,-6336,9888,-9952,4896]),(⟨2,2,0⟩,[0,0,-64,768,-1920,768,448]),(⟨2,3,0⟩,[48,-656,2464,-3424,816,1776]),(⟨2,5,0⟩,[-32,352,-608,-224]),(⟨3,0,0⟩,[-64,1008,-6560,23600,-48352,52336,-22720,-1808]),(⟨3,0,1⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨3,0,2⟩,[48,-656,2464,-3424,816,1776]),(⟨3,0,3⟩,[0,-768,4352,-8448,6912]),(⟨3,0,5⟩,[0,256,-768]),(⟨3,1,0⟩,[0,416,-3904,14912,-29952,32544,-16576]),(⟨3,1,1⟩,[0,96,-1152,3776,-5504,3808]),(⟨3,2,0⟩,[48,-656,2464,-3424,816,1776]),(⟨3,3,0⟩,[0,-768,4352,-8448,6912]),(⟨3,5,0⟩,[0,256,-768]),(⟨4,0,0⟩,[0,416,-3936,15360,-31616,34656,-17440]),(⟨4,0,1⟩,[0,96,-1216,4480,-7232,4896]),(⟨4,1,0⟩,[0,96,-1216,4480,-7232,4896]),(⟨4,1,1⟩,[-96,1216,-4480,7232,-4896]),(⟨5,0,0⟩,[80,-1072,4480,-8384,6192,752]),(⟨5,0,1⟩,[0,-192,1408,-3520,3328]),(⟨5,0,2⟩,[-32,352,-608,-224]),(⟨5,0,3⟩,[0,256,-768]),(⟨5,1,0⟩,[0,-192,1408,-3520,3328]),(⟨5,1,1⟩,[0,-64,640,-1088]),(⟨5,2,0⟩,[-32,352,-608,-224]),(⟨5,3,0⟩,[0,256,-768]),(⟨6,0,0⟩,[0,-576,3584,-7744,6784]),(⟨6,0,1⟩,[0,-64,640,-1088]),(⟨6,1,0⟩,[0,-64,640,-1088]),(⟨6,1,1⟩,[64,-640,1088]),(⟨7,0,0⟩,[-32,352,-608,-224]),(⟨8,0,0⟩,[0,256,-768])]


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
    (Poly.add (Poly.scale (K.ofRat r209) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r207*r208 : ℚ)=r209 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 10 r207 r208 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C068

#print axioms Coulomb8.Columns.C068.sound
