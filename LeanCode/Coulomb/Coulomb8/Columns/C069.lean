import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C069

def r0 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -35712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 184704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -679680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 2076672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -5406336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 10654080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -13466688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 8523840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -23040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -1905408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 442368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 12864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -76800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 332800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -1159552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 3419904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -8250624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 14798016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -17554240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 11587776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -2481408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -103680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 42880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -261760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 939520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -2513664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 5118080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -6822208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 5021888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1636608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 4800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -37568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 174464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -603392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 254464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -4317056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 7320704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -7287296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 3223872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -30144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 81408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -320000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 1033728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -2603008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 638976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -4560384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 312448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 30976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -99968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 274304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -698752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 1197312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -981888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 119104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 15872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -67968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 230400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -634240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 1058304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -813696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 79616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 14848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 88832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -51328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 218752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -762752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 142208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -363392, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 10887552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -12093056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 7947904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -374784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -130688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 45440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -464256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 11008, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 591040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -1137984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 98112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 79488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -311936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1023872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -2581632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 4347776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -621184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 297472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -16896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 74880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -92160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -144000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 489984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 72704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -233472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 477184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -59136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -23040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -27648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -17664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -107264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 240896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -186112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 18304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -7808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 138240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -320384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 457344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -273024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -92416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 45056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -801536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 1162240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -799488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -115200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 40320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -23040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -623232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 1585152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -256896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 37248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -77184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -20352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 290688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -361344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 14464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 56960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -161408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 32128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 290176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -71040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 135680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -25600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -138496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 352256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -57088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -17856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 92352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -339840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 1038336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -2703168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 5327040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -6733344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 4261920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -11520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -952704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 221184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 6432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -38400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 166400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -579776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 1709952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -4125312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 7399008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -8777120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 5793888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -1240704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -51840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 21440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -130880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 469760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -1256832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 2559040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -3411104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 2510944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -818304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 2400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -18784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 87232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -301696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 127232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -2158528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 3660352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -3643648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 1611936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -15072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 40704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -160000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 516864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -1301504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 319488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -2280192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 156224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -2624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 15488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -49984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 137152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -349376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 598656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -490944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 59552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -33984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 115200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -317120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 529152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -406848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -20416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 39808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 7424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 44416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -25664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 109376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -381376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 71104, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -181696, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 5443776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -6046528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 3973952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -187392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -4512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -65344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 22720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -232128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 5504, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 295520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -568992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 49056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -7104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 39744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -155968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 511936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -1290816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 2173888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -310592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 148736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -8448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 37440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -46080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -72000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 244992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 36352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -116736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 238592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -29568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -11520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -8832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 120448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -93056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 9152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -3904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 69120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -160192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 228672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -136512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -14176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -46208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 22528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -400768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 581120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -399744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -57600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 20160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -11520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -311616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 792576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -128448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 18624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -38592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -10176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 145344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -180672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 7232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 28480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -80704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 16064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 145088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 1728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -35520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 67840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -69248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 176128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -28544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[0,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36],[r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[0,r48,r49,r50,r51,r52,r53,r54,r55,r56],[r27,r57,r58,r59,r60,r61,r62,r63,r64],[0,r65,r66,r67,r68,r69,r70,r71],[r72,r73,r74,r75,r76,r77,r78],[0,r79,r80,r81,r82,r83],[],[],[],[],[0,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[r26,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104],[0,r48,r105,r106,r107,r108,r109,r110,r111,r112],[0,0,r48,r113,r114,r115,r116,r117,-3456],[0,r84,r118,r119,r120,r121,r122,r123],[0,0,r124,r125,r126,r127,768],[],[],[],[],[],[0,0,r37,r128,r129,r97,r130,r131,r132,r133],[r134,r135,r136,r137,r138,r139,r140,r141,r142],[],[r72,r73,r74,r75,r76,r77,r78],[],[],[],[],[],[0,r143,r144,r145,r146,r147,r148,r149],[],[0,r79,r80,r81,r82,r83],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r150,r151,r152,r153,r154,r155,r156,r157,8064],[0,r158,r159,r160,r161,r162,r163,r164,1152],[r72,r165,r166,r167,r168,r169,r170,r171,-2560],[0,0,r37,r172,r173,r174,r97,-256],[r158,r175,r176,r177,r178,r179,-384],[],[r37,r180,r181,r182,256],[],[],[],[r37,r183,r184,r185,r186,r187,r188,r189,1792],[0,0,r37,r172,r173,r174,r97,-256],[r158,r175,r190,r191,r192,r193,-1152],[],[r37,r180,r181,r182,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206]),(⟨0,0,1⟩,[r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219]),(⟨0,0,2⟩,[0,r220,r221,r174,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨0,0,3⟩,[r72,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239]),(⟨0,0,4⟩,[0,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,0,5⟩,[r221,r249,r250,r251,r252,r253,r254,r255,r256]),(⟨0,0,6⟩,[0,r257,r258,r259,r260,r261,r262,r263]),(⟨0,0,7⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨0,0,8⟩,[0,r158,r270,r271,r272,r273]),(⟨0,1,0⟩,[r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219]),(⟨0,1,1⟩,[0,r37,r128,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,1,2⟩,[r220,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,1,3⟩,[0,r240,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,1,4⟩,[0,0,r240,r301,r302,r303,r304,r305,-1728]),(⟨0,1,5⟩,[0,r37,r306,r307,r308,r309,r310,r311]),(⟨0,1,6⟩,[0,0,r312,r313,r314,r315,384]),(⟨0,2,0⟩,[0,r220,r221,r174,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨0,2,1⟩,[r220,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,2,2⟩,[0,0,r72,r316,r317,r285,r318,r319,r320,r321]),(⟨0,2,3⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,2,5⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨0,3,0⟩,[r72,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239]),(⟨0,3,1⟩,[0,r240,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,3,2⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,3,3⟩,[0,r150,r331,r332,r333,r334,r335,r336]),(⟨0,3,5⟩,[0,r158,r270,r271,r272,r273]),(⟨0,4,0⟩,[0,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,4,1⟩,[0,0,r240,r301,r302,r303,r304,r305,-1728]),(⟨0,5,0⟩,[r221,r249,r250,r251,r252,r253,r254,r255,r256]),(⟨0,5,1⟩,[0,r37,r306,r307,r308,r309,r310,r311]),(⟨0,5,2⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨0,5,3⟩,[0,r158,r270,r271,r272,r273]),(⟨0,6,0⟩,[0,r257,r258,r259,r260,r261,r262,r263]),(⟨0,6,1⟩,[0,0,r312,r313,r314,r315,384]),(⟨0,7,0⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨0,8,0⟩,[0,r158,r270,r271,r272,r273]),(⟨1,0,0⟩,[r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219]),(⟨1,0,1⟩,[0,r37,r128,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨1,0,2⟩,[r220,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨1,0,3⟩,[0,r240,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨1,0,4⟩,[0,0,r240,r301,r302,r303,r304,r305,-1728]),(⟨1,0,5⟩,[0,r37,r306,r307,r308,r309,r310,r311]),(⟨1,0,6⟩,[0,0,r312,r313,r314,r315,384]),(⟨1,1,0⟩,[0,r37,r128,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨1,1,1⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344,4032]),(⟨1,1,2⟩,[0,r134,r345,r346,r347,r348,r349,r350,576]),(⟨1,1,3⟩,[r26,r351,r352,r353,r354,r355,r356,r357,-1280]),(⟨1,1,4⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨1,1,5⟩,[r134,r360,r361,r173,r362,r363,-192]),(⟨1,1,7⟩,[r72,r364,r365,r366,128]),(⟨1,2,0⟩,[r220,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨1,2,1⟩,[0,r134,r345,r346,r347,r348,r349,r350,576]),(⟨1,2,2⟩,[r72,r165,r367,r368,r369,r370,r371,r372,896]),(⟨1,2,3⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨1,2,4⟩,[r134,r360,r373,r374,r375,r376,-576]),(⟨1,2,6⟩,[r72,r364,r365,r366,128]),(⟨1,3,0⟩,[0,r240,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨1,3,1⟩,[r26,r351,r352,r353,r354,r355,r356,r357,-1280]),(⟨1,3,2⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨1,4,0⟩,[0,0,r240,r301,r302,r303,r304,r305,-1728]),(⟨1,4,1⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨1,4,2⟩,[r134,r360,r373,r374,r375,r376,-576]),(⟨1,5,0⟩,[0,r37,r306,r307,r308,r309,r310,r311]),(⟨1,5,1⟩,[r134,r360,r361,r173,r362,r363,-192]),(⟨1,6,0⟩,[0,0,r312,r313,r314,r315,384]),(⟨1,6,2⟩,[r72,r364,r365,r366,128]),(⟨1,7,1⟩,[r72,r364,r365,r366,128]),(⟨2,0,0⟩,[0,r220,r221,r174,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨2,0,1⟩,[r220,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨2,0,2⟩,[0,0,r72,r316,r317,r285,r318,r319,r320,r321]),(⟨2,0,3⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨2,0,5⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨2,1,0⟩,[r220,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨2,1,1⟩,[0,r134,r345,r346,r347,r348,r349,r350,576]),(⟨2,1,2⟩,[r72,r165,r367,r368,r369,r370,r371,r372,896]),(⟨2,1,3⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨2,1,4⟩,[r134,r360,r373,r374,r375,r376,-576]),(⟨2,1,6⟩,[r72,r364,r365,r366,128]),(⟨2,2,0⟩,[0,0,r72,r316,r317,r285,r318,r319,r320,r321]),(⟨2,2,1⟩,[r72,r165,r367,r368,r369,r370,r371,r372,896]),(⟨2,3,0⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨2,3,1⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨2,4,1⟩,[r134,r360,r373,r374,r375,r376,-576]),(⟨2,5,0⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨2,6,1⟩,[r72,r364,r365,r366,128]),(⟨3,0,0⟩,[r72,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239]),(⟨3,0,1⟩,[0,r240,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨3,0,2⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨3,0,3⟩,[0,r150,r331,r332,r333,r334,r335,r336]),(⟨3,0,5⟩,[0,r158,r270,r271,r272,r273]),(⟨3,1,0⟩,[0,r240,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨3,1,1⟩,[r26,r351,r352,r353,r354,r355,r356,r357,-1280]),(⟨3,1,2⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨3,2,0⟩,[r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨3,2,1⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨3,3,0⟩,[0,r150,r331,r332,r333,r334,r335,r336]),(⟨3,5,0⟩,[0,r158,r270,r271,r272,r273]),(⟨4,0,0⟩,[0,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨4,0,1⟩,[0,0,r240,r301,r302,r303,r304,r305,-1728]),(⟨4,1,0⟩,[0,0,r240,r301,r302,r303,r304,r305,-1728]),(⟨4,1,1⟩,[0,0,r72,r358,r359,r124,r285,-128]),(⟨4,1,2⟩,[r134,r360,r373,r374,r375,r376,-576]),(⟨4,2,1⟩,[r134,r360,r373,r374,r375,r376,-576]),(⟨5,0,0⟩,[r221,r249,r250,r251,r252,r253,r254,r255,r256]),(⟨5,0,1⟩,[0,r37,r306,r307,r308,r309,r310,r311]),(⟨5,0,2⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨5,0,3⟩,[0,r158,r270,r271,r272,r273]),(⟨5,1,0⟩,[0,r37,r306,r307,r308,r309,r310,r311]),(⟨5,1,1⟩,[r134,r360,r361,r173,r362,r363,-192]),(⟨5,2,0⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨5,3,0⟩,[0,r158,r270,r271,r272,r273]),(⟨6,0,0⟩,[0,r257,r258,r259,r260,r261,r262,r263]),(⟨6,0,1⟩,[0,0,r312,r313,r314,r315,384]),(⟨6,1,0⟩,[0,0,r312,r313,r314,r315,384]),(⟨6,1,2⟩,[r72,r364,r365,r366,128]),(⟨6,2,1⟩,[r72,r364,r365,r366,128]),(⟨7,0,0⟩,[r26,r264,r265,r266,r267,r268,r269]),(⟨7,1,1⟩,[r72,r364,r365,r366,128]),(⟨8,0,0⟩,[0,r158,r270,r271,r272,r273])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r377) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r378) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[256,-4096,25344,-90624,272128,-756736,1479936,-1417728,294912]),(⟨5,0,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,1,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,1,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨6,0,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨6,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨7,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[256,-4096,25344,-90624,272128,-756736,1479936,-1417728,294912]),(⟨0,5,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,5,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,5,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,6,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,6,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,7,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,8,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨1,0,0⟩,[128,-2688,24192,-130560,512768,-1665536,4579584,-10006272,16205952,-18614144,14451840,-6584064,1032192]),(⟨1,0,1⟩,[0,-512,7680,-52480,238336,-874496,2646784,-6086656,9918720,-11022848,7893760,-2897664]),(⟨1,0,2⟩,[-128,2432,-17280,67328,-195840,501760,-1009920,1402112,-1296000,705152,-94080]),(⟨1,0,3⟩,[0,768,-8960,48128,-184064,549888,-1145088,1544192,-1328384,621824]),(⟨1,1,0⟩,[0,-512,7680,-52480,238336,-874496,2646784,-6086656,9918720,-11022848,7893760,-2897664]),(⟨1,1,1⟩,[0,0,-768,13056,-76800,188160,-107520,-415488,1056768,-1198848,639744]),(⟨1,2,0⟩,[-128,2432,-17280,67328,-195840,501760,-1009920,1402112,-1296000,705152,-94080]),(⟨1,3,0⟩,[0,768,-8960,48128,-184064,549888,-1145088,1544192,-1328384,621824]),(⟨1,5,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,5,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,6,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[0,-512,7936,-56832,267776,-990464,3009536,-7115520,12155392,-13920512,9606400,-3192576]),(⟨2,0,1⟩,[0,0,-768,12032,-65536,134400,81408,-1027840,2478080,-2981120,1467648]),(⟨2,0,2⟩,[0,0,-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨2,0,3⟩,[0,0,0,1536,-11776,39936,-130048,278016,-177664]),(⟨2,1,0⟩,[0,0,-768,12032,-65536,134400,81408,-1027840,2478080,-2981120,1467648]),(⟨2,1,1⟩,[0,0,0,0,-1536,19968,-64512,-9216,238080,-182784]),(⟨2,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,2,0⟩,[0,0,-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨2,2,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,3,0⟩,[0,0,0,1536,-11776,39936,-130048,278016,-177664]),(⟨2,5,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-512,9600,-72832,322048,-1069312,3079424,-7292416,12241408,-12647680,6482304,-593280]),(⟨3,0,1⟩,[0,1536,-19456,110848,-439808,1497856,-4018176,7151360,-7368192,3542784]),(⟨3,0,2⟩,[384,-6400,36608,-110848,288256,-680704,1044736,-824064,120960]),(⟨3,0,3⟩,[0,-2304,21504,-92416,315392,-801536,1162240,-799488]),(⟨3,1,0⟩,[0,1536,-19456,110848,-439808,1497856,-4018176,7151360,-7368192,3542784]),(⟨3,1,1⟩,[-256,4352,-23296,28928,113920,-322816,64256,580352,-609280]),(⟨3,1,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,2,0⟩,[384,-6400,36608,-110848,288256,-680704,1044736,-824064,120960]),(⟨3,2,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[0,-2304,21504,-92416,315392,-801536,1162240,-799488]),(⟨3,5,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,0,0⟩,[0,2304,-28672,162816,-640000,2067456,-5206016,8945664,-9120768,4374272]),(⟨4,0,1⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨4,1,0⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨4,1,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,2,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,0,0⟩,[640,-10496,61952,-199936,548608,-1397504,2394624,-1963776,238208]),(⟨5,0,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,1,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,1,1⟩,[768,-11264,48384,-43008,-142080,271360,-91392]),(⟨5,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨6,0,0⟩,[0,-3328,31744,-135936,460800,-1268480,2116608,-1627392]),(⟨6,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨7,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[256,-4096,25344,-90624,272128,-756736,1479936,-1417728,294912]),(⟨0,0,6⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,0,7⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,0,8⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,1,0⟩,[128,-2688,24192,-130560,512768,-1665536,4579584,-10006272,16205952,-18614144,14451840,-6584064,1032192]),(⟨0,1,1⟩,[0,-512,7680,-52480,238336,-874496,2646784,-6086656,9918720,-11022848,7893760,-2897664]),(⟨0,1,2⟩,[-128,2432,-17280,67328,-195840,501760,-1009920,1402112,-1296000,705152,-94080]),(⟨0,1,3⟩,[0,768,-8960,48128,-184064,549888,-1145088,1544192,-1328384,621824]),(⟨0,1,5⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,1,6⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,2,0⟩,[0,-512,7936,-56832,267776,-990464,3009536,-7115520,12155392,-13920512,9606400,-3192576]),(⟨0,2,1⟩,[0,0,-768,12032,-65536,134400,81408,-1027840,2478080,-2981120,1467648]),(⟨0,2,2⟩,[0,0,-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨0,2,3⟩,[0,0,0,1536,-11776,39936,-130048,278016,-177664]),(⟨0,2,5⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,3,0⟩,[-512,9600,-72832,322048,-1069312,3079424,-7292416,12241408,-12647680,6482304,-593280]),(⟨0,3,1⟩,[0,1536,-19456,110848,-439808,1497856,-4018176,7151360,-7368192,3542784]),(⟨0,3,2⟩,[384,-6400,36608,-110848,288256,-680704,1044736,-824064,120960]),(⟨0,3,3⟩,[0,-2304,21504,-92416,315392,-801536,1162240,-799488]),(⟨0,3,5⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,4,0⟩,[0,2304,-28672,162816,-640000,2067456,-5206016,8945664,-9120768,4374272]),(⟨0,4,1⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨0,5,0⟩,[640,-10496,61952,-199936,548608,-1397504,2394624,-1963776,238208]),(⟨0,5,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,5,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,5,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,6,0⟩,[0,-3328,31744,-135936,460800,-1268480,2116608,-1627392]),(⟨0,6,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,7,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,8,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨1,0,0⟩,[128,-2688,24192,-130560,512768,-1665536,4579584,-10006272,16205952,-18614144,14451840,-6584064,1032192]),(⟨1,0,1⟩,[0,-512,7680,-52480,238336,-874496,2646784,-6086656,9918720,-11022848,7893760,-2897664]),(⟨1,0,2⟩,[-128,2432,-17280,67328,-195840,501760,-1009920,1402112,-1296000,705152,-94080]),(⟨1,0,3⟩,[0,768,-8960,48128,-184064,549888,-1145088,1544192,-1328384,621824]),(⟨1,0,5⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,0,6⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,1,0⟩,[0,-1024,15360,-104960,476672,-1748992,5293568,-12173312,19837440,-22045696,15787520,-5795328]),(⟨1,1,1⟩,[0,0,-1536,26112,-153600,376320,-215040,-830976,2113536,-2397696,1279488]),(⟨1,1,5⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,1,7⟩,[-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨1,2,1⟩,[0,0,0,0,-1536,19968,-64512,-9216,238080,-182784]),(⟨1,2,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,2,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,3,0⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨1,3,1⟩,[-256,4352,-23296,28928,113920,-322816,64256,580352,-609280]),(⟨1,3,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,4,0⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨1,4,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,4,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨1,5,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,5,1⟩,[768,-11264,48384,-43008,-142080,271360,-91392]),(⟨1,6,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[0,-512,7936,-56832,267776,-990464,3009536,-7115520,12155392,-13920512,9606400,-3192576]),(⟨2,0,1⟩,[0,0,-768,12032,-65536,134400,81408,-1027840,2478080,-2981120,1467648]),(⟨2,0,2⟩,[0,0,-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨2,0,3⟩,[0,0,0,1536,-11776,39936,-130048,278016,-177664]),(⟨2,0,5⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,1,0⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨2,1,1⟩,[0,0,0,0,-1536,19968,-64512,-9216,238080,-182784]),(⟨2,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,0⟩,[0,0,-512,7680,-35328,79360,-214528,481792,-372224,53760]),(⟨2,2,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,3,0⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨2,3,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,5,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-512,9600,-72832,322048,-1069312,3079424,-7292416,12241408,-12647680,6482304,-593280]),(⟨3,0,1⟩,[0,1536,-19456,110848,-439808,1497856,-4018176,7151360,-7368192,3542784]),(⟨3,0,2⟩,[384,-6400,36608,-110848,288256,-680704,1044736,-824064,120960]),(⟨3,0,3⟩,[0,-2304,21504,-92416,315392,-801536,1162240,-799488]),(⟨3,0,5⟩,[0,1536,-10240,29696,-100352,177664]),(⟨3,1,0⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨3,1,1⟩,[-256,4352,-23296,28928,113920,-322816,64256,580352,-609280]),(⟨3,1,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,2,0⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨3,2,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[0,-4608,43008,-184832,630784,-1603072,2324480,-1598976]),(⟨3,5,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,0,0⟩,[0,2304,-28672,162816,-640000,2067456,-5206016,8945664,-9120768,4374272]),(⟨4,0,1⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨4,1,0⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨4,1,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,2,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,0,0⟩,[640,-10496,61952,-199936,548608,-1397504,2394624,-1963776,238208]),(⟨5,0,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,1,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,1,1⟩,[768,-11264,48384,-43008,-142080,271360,-91392]),(⟨5,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨6,0,0⟩,[0,-3328,31744,-135936,460800,-1268480,2116608,-1627392]),(⟨6,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨7,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-384,8064,-71424,369408,-1359360,4153344,-10812672,21308160,-26933376,17047680,-783360,-3810816,884736]),(⟨0,0,1⟩,[128,-2688,25728,-153600,665600,-2319104,6839808,-16501248,29596032,-35108480,23175552,-4962816,-1451520]),(⟨0,0,2⟩,[0,-128,640,-6144,85760,-523520,1879040,-5027328,10236160,-13644416,10043776,-3273216]),(⟨0,0,3⟩,[-512,9600,-75136,348928,-1206784,3562496,-8634112,14641408,-14574592,6447744,-60288]),(⟨0,0,4⟩,[0,2304,-28672,162816,-640000,2067456,-5206016,8945664,-9120768,4374272]),(⟨0,0,5⟩,[640,-10496,61952,-199936,548608,-1397504,2394624,-1963776,238208]),(⟨0,0,6⟩,[0,-3328,31744,-135936,460800,-1268480,2116608,-1627392]),(⟨0,0,7⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,0,8⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,1,0⟩,[128,-2688,25728,-153600,665600,-2319104,6839808,-16501248,29596032,-35108480,23175552,-4962816,-1451520]),(⟨0,1,1⟩,[0,-1024,15360,-102656,437504,-1525504,4835072,-12355328,21775104,-24186112,15895808,-5246976]),(⟨0,1,2⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨0,1,3⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨0,1,4⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨0,1,5⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,1,6⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,2,0⟩,[0,-128,640,-6144,85760,-523520,1879040,-5027328,10236160,-13644416,10043776,-3273216]),(⟨0,2,1⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨0,2,2⟩,[0,0,-512,7680,-35328,79360,-214528,481792,-372224,53760]),(⟨0,2,3⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨0,2,5⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,3,0⟩,[-512,9600,-75136,348928,-1206784,3562496,-8634112,14641408,-14574592,6447744,-60288]),(⟨0,3,1⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨0,3,2⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨0,3,3⟩,[0,-4608,43008,-184832,630784,-1603072,2324480,-1598976]),(⟨0,3,5⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,4,0⟩,[0,2304,-28672,162816,-640000,2067456,-5206016,8945664,-9120768,4374272]),(⟨0,4,1⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨0,5,0⟩,[640,-10496,61952,-199936,548608,-1397504,2394624,-1963776,238208]),(⟨0,5,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,5,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,5,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,6,0⟩,[0,-3328,31744,-135936,460800,-1268480,2116608,-1627392]),(⟨0,6,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,7,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,8,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨1,0,0⟩,[128,-2688,25728,-153600,665600,-2319104,6839808,-16501248,29596032,-35108480,23175552,-4962816,-1451520]),(⟨1,0,1⟩,[0,-1024,15360,-102656,437504,-1525504,4835072,-12355328,21775104,-24186112,15895808,-5246976]),(⟨1,0,2⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨1,0,3⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨1,0,4⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨1,0,5⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,0,6⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,1,0⟩,[0,-1024,15360,-102656,437504,-1525504,4835072,-12355328,21775104,-24186112,15895808,-5246976]),(⟨1,1,1⟩,[0,0,-2304,39168,-230400,564480,-322560,-1246464,3170304,-3596544,1919232]),(⟨1,1,2⟩,[0,768,-13056,74496,-154368,-40704,581376,-722688,274176]),(⟨1,1,3⟩,[-256,4352,-23296,28928,113920,-322816,64256,580352,-609280]),(⟨1,1,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,1,5⟩,[768,-11264,48384,-43008,-142080,271360,-91392]),(⟨1,1,7⟩,[-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨1,2,1⟩,[0,768,-13056,74496,-154368,-40704,581376,-722688,274176]),(⟨1,2,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨1,2,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,2,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨1,2,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,3,0⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨1,3,1⟩,[-256,4352,-23296,28928,113920,-322816,64256,580352,-609280]),(⟨1,3,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,4,0⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨1,4,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,4,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨1,5,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,5,1⟩,[768,-11264,48384,-43008,-142080,271360,-91392]),(⟨1,6,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[0,-128,640,-6144,85760,-523520,1879040,-5027328,10236160,-13644416,10043776,-3273216]),(⟨2,0,1⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨2,0,2⟩,[0,0,-512,7680,-35328,79360,-214528,481792,-372224,53760]),(⟨2,0,3⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨2,0,5⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,1,0⟩,[-128,2432,-18048,79360,-261376,636160,-928512,374272,1182080,-2275968,1373568]),(⟨2,1,1⟩,[0,768,-13056,74496,-154368,-40704,581376,-722688,274176]),(⟨2,1,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,1,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,1,4⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,0⟩,[0,0,-512,7680,-35328,79360,-214528,481792,-372224,53760]),(⟨2,2,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,3,0⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨2,3,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,5,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-512,9600,-75136,348928,-1206784,3562496,-8634112,14641408,-14574592,6447744,-60288]),(⟨3,0,1⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨3,0,2⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨3,0,3⟩,[0,-4608,43008,-184832,630784,-1603072,2324480,-1598976]),(⟨3,0,5⟩,[0,1536,-10240,29696,-100352,177664]),(⟨3,1,0⟩,[0,2304,-28416,158976,-623872,2047744,-5163264,8695552,-8696576,4164608]),(⟨3,1,1⟩,[-256,4352,-23296,28928,113920,-322816,64256,580352,-609280]),(⟨3,1,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,2,0⟩,[384,-6400,36608,-109312,276480,-640768,914688,-546048,-56704]),(⟨3,2,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[0,-4608,43008,-184832,630784,-1603072,2324480,-1598976]),(⟨3,5,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,0,0⟩,[0,2304,-28672,162816,-640000,2067456,-5206016,8945664,-9120768,4374272]),(⟨4,0,1⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨4,1,0⟩,[0,0,2304,-33792,149760,-184320,-288000,979968,-822528]),(⟨4,1,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨4,2,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨5,0,0⟩,[640,-10496,61952,-199936,548608,-1397504,2394624,-1963776,238208]),(⟨5,0,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,1,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,1,1⟩,[768,-11264,48384,-43008,-142080,271360,-91392]),(⟨5,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨5,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨6,0,0⟩,[0,-3328,31744,-135936,460800,-1268480,2116608,-1627392]),(⟨6,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨7,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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
    (Poly.add (Poly.scale (K.ofRat r379) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r377*r378 : ℚ)=r379 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 11 r377 r378 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C069

#print axioms Coulomb8.Columns.C069.sound
