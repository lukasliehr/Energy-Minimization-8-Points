import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C076

def r0 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 14640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -23136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 1054224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -656640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 14445600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -4883520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 61751712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -82728384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 10693008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -34956960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -3487920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 10168320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1283904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -5088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 61344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -452320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 2297504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -8562112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 24352448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -7716288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 93325440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -121650656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 110687648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -58735328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 8072224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 772736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -2848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 31488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -222688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1167408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -4670080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 14264960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -33450752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 59828176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -78435680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 69368960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -35197984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 926192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 800, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -129312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 711136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -2581632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 6638848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -12472192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 16427520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1726944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -1500704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 11885728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -7690208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 1120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -85808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 516352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -2017376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 5620544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -11682336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 17996288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -19324560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 12763936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -514000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -1152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 53248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -173568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 302592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -127872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -863488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 2559232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -3316416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 252928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 3712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -26560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 123136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -373568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 661888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -822592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 581440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 1856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -17088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 4544, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -216000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 443584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -645440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 69568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 23616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 73152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -59648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -6848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -40192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 84608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -123008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -3456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 47232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -358016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 1769312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -6310912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 2499072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -39073792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 69207328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -91811456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 83657088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -45296000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 1469408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -2336, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 183264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -505600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 684800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 108288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -6410368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 16677344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -3557280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 3028704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -1149344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -64640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 393728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -1585792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 4637568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -10037248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 15591424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -16339648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 10288064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -384640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -24064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 123392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -236032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 851456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -1360384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 3456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -1888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 183552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -105920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 2187264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -659264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 6296320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -4286752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -89472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 226528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -11712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -37888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 456320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -136960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -1371904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 3638016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -4335616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 306240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 106880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -55296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 92288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 59008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -212864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 340096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -9472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 11264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -344832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 1022208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -2235136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 3402752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -3267840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 1353088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 43776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -18432, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 1099776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -1844736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 109056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 6100992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -1849344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 1747200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 214528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -427520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 221184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -369152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -91648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 153728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -508416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 154112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -145600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -4224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -160896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 320640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -165888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 276864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 7320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -11568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 527112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -328320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 7222800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -2441760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 30875856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -41364192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 5346504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -17478480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -1743960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 5084160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -641952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -2544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 30672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -226160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 1148752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -4281056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 12176224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -3858144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 46662720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -60825328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 55343824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -29367664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 4036112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 386368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 8, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -1424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 15744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -111344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 583704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -2335040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 7132480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -16725376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 29914088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -39217840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 34684480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -17598992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 463096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 400, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -64656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 355568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -1290816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 3319424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -6236096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 8213760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -863472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -750352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 5942864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -3845104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -8, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -42904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 258176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -1008688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 2810272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -5841168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 8998144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -9662280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 6381968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -257000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 26624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -86784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 151296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -63936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -431744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 1279616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -1658208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 126464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -13280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 61568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -186784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 330944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -411296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 290720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -8544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 2272, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -108000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 221792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -322720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 34784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 11808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 36576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -29824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -3424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -20096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 42304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -61504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -179008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 884656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -3155456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1249536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -19536896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 34603664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -45905728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 41828544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -22648000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 734704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -1168, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 91632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -252800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 342400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 54144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -3205184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 8338672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1778640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 1514352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -574672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -32320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 196864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -792896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 2318784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -5018624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 7795712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -8169824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 5144032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -192320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 61696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -118016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 425728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -680192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -944, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 91776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -52960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 1093632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -329632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 3148160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -2143376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -44736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 113264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -5856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -18944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 228160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -68480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -685952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 1819008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -2167808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 153120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -26816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 53440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -27648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 46144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -15424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 29504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -106432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 170048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 5632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -172416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 511104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -1117568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 1701376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -1633920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 676544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 21888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -9216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 549888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -922368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 3050496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -924672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 873600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 107264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -213760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 110592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -184576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -45824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 76864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -4544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -254208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 77056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -72800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -2112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -80448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 160320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -82944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 138432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52],[r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[r74,r75,r76,r77,r78,r79,r80,r81,r82],[r74,r83,r84,r85,r86,r87,r88,r89],[r90,r91,r92,r93,r94,r95,r96],[r97,r98,r99,r100,r101,r102],[],[],[],[r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115],[r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127],[r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138],[0,0,r139,r140,r141,r142,r143,r144,r145,5632],[],[r74,r83,r84,r85,r86,r87,r88,r89],[0,0,r146,r147,r148,r149,-1024],[],[],[],[],[r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160],[r161,r162,r163,r164,r165,r166,r167,r168,r169,r170],[r75,r171,r172,r173,r174,r175,r176,r177,-3136],[r178,r179,r180,r181,r182,r183,r184,-1408],[r90,r91,r92,r93,r94,r95,r96],[],[r185,r186,r187,r188,256],[],[],[r189,r190,r191,r192,r193,r194,r195,r196,r197],[],[],[r97,r98,r99,r100,r101,r102],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r198,r199,r200,r201,r202,r203,r204,r205,r206,-37632],[0,0,r185,r207,r208,r209,r210,r211,r212,r213,12544],[0,0,r139,r140,r141,r142,r143,r144,r145,5632],[],[],[0,0,r146,r147,r148,r149,-1024],[],[],[],[],[r14,r214,r215,r216,r217,r218,r219,r220,r221,3136],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r14,r222,r149,r223,r224,r225,r226,r227,-9408],[r178,r179,r180,r181,r182,r183,r184,-1408],[],[],[r185,r186,r187,r188,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241]),(⟨0,0,1⟩,[r103,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254]),(⟨0,0,2⟩,[r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,0,3⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨0,0,4⟩,[r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290]),(⟨0,0,5⟩,[r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,0,6⟩,[r301,r302,r83,r303,r304,r305,r306,r307,r308]),(⟨0,0,7⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨0,0,8⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨0,0,9⟩,[r75,r323,r324,r325,r326,r327]),(⟨0,1,0⟩,[r103,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254]),(⟨0,1,1⟩,[r328,r329,r92,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨0,1,2⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,1,3⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362]),(⟨0,1,4⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨0,1,6⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨0,1,7⟩,[0,0,r370,r371,r372,r373,-512]),(⟨0,2,0⟩,[r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,2,1⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨0,2,2⟩,[r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨0,2,3⟩,[r90,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,2,4⟩,[r302,r394,r395,r396,r397,r64,r398,r399,-1568]),(⟨0,2,5⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨0,2,6⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨0,2,8⟩,[r406,r139,r407,r408,128]),(⟨0,3,0⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨0,3,1⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362]),(⟨0,3,2⟩,[r90,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,3,3⟩,[r14,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,3,6⟩,[r75,r323,r324,r325,r326,r327]),(⟨0,4,0⟩,[r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290]),(⟨0,4,1⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨0,4,2⟩,[r302,r394,r395,r396,r397,r64,r398,r399,-1568]),(⟨0,5,0⟩,[r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,5,2⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨0,6,0⟩,[r301,r302,r83,r303,r304,r305,r306,r307,r308]),(⟨0,6,1⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨0,6,2⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨0,6,3⟩,[r75,r323,r324,r325,r326,r327]),(⟨0,7,0⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨0,7,1⟩,[0,0,r370,r371,r372,r373,-512]),(⟨0,8,0⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨0,8,2⟩,[r406,r139,r407,r408,128]),(⟨0,9,0⟩,[r75,r323,r324,r325,r326,r327]),(⟨1,0,0⟩,[r103,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254]),(⟨1,0,1⟩,[r328,r329,r92,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨1,0,2⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨1,0,3⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362]),(⟨1,0,4⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨1,0,6⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨1,0,7⟩,[0,0,r370,r371,r372,r373,-512]),(⟨1,1,0⟩,[r328,r329,r92,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨1,1,1⟩,[0,0,r417,r418,r419,r420,r421,r422,r423,r424,r425,-18816]),(⟨1,1,2⟩,[0,0,r406,r426,r427,r428,r429,r430,r431,r432,6272]),(⟨1,1,3⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨1,1,6⟩,[0,0,r370,r371,r372,r373,-512]),(⟨1,2,0⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨1,2,1⟩,[0,0,r406,r426,r427,r428,r429,r430,r431,r432,6272]),(⟨1,2,2⟩,[r103,r433,r434,r435,r436,r437,r438,r439,r440,1568]),(⟨1,3,0⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362]),(⟨1,3,1⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨1,4,0⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨1,6,0⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨1,6,1⟩,[0,0,r370,r371,r372,r373,-512]),(⟨1,7,0⟩,[0,0,r370,r371,r372,r373,-512]),(⟨2,0,0⟩,[r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨2,0,1⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨2,0,2⟩,[r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨2,0,3⟩,[r90,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨2,0,4⟩,[r302,r394,r395,r396,r397,r64,r398,r399,-1568]),(⟨2,0,5⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨2,0,6⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨2,0,8⟩,[r406,r139,r407,r408,128]),(⟨2,1,0⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351]),(⟨2,1,1⟩,[0,0,r406,r426,r427,r428,r429,r430,r431,r432,6272]),(⟨2,1,2⟩,[r103,r433,r434,r435,r436,r437,r438,r439,r440,1568]),(⟨2,2,0⟩,[r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨2,2,1⟩,[r103,r433,r434,r435,r436,r437,r438,r439,r440,1568]),(⟨2,2,2⟩,[r103,r441,r373,r442,r443,r444,r445,r446,-4704]),(⟨2,2,3⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨2,2,6⟩,[r406,r139,r407,r408,128]),(⟨2,3,0⟩,[r90,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨2,3,2⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨2,4,0⟩,[r302,r394,r395,r396,r397,r64,r398,r399,-1568]),(⟨2,5,0⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨2,6,0⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨2,6,2⟩,[r406,r139,r407,r408,128]),(⟨2,8,0⟩,[r406,r139,r407,r408,128]),(⟨3,0,0⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨3,0,1⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362]),(⟨3,0,2⟩,[r90,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨3,0,3⟩,[r14,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨3,0,6⟩,[r75,r323,r324,r325,r326,r327]),(⟨3,1,0⟩,[r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362]),(⟨3,1,1⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨3,2,0⟩,[r90,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨3,2,2⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨3,3,0⟩,[r14,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨3,6,0⟩,[r75,r323,r324,r325,r326,r327]),(⟨4,0,0⟩,[r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r290]),(⟨4,0,1⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨4,0,2⟩,[r302,r394,r395,r396,r397,r64,r398,r399,-1568]),(⟨4,1,0⟩,[0,0,r363,r364,r365,r366,r367,r368,r369,2816]),(⟨4,2,0⟩,[r302,r394,r395,r396,r397,r64,r398,r399,-1568]),(⟨5,0,0⟩,[r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨5,0,2⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨5,2,0⟩,[r128,r400,r401,r402,r403,r404,r405,-704]),(⟨6,0,0⟩,[r301,r302,r83,r303,r304,r305,r306,r307,r308]),(⟨6,0,1⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨6,0,2⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨6,0,3⟩,[r75,r323,r324,r325,r326,r327]),(⟨6,1,0⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨6,1,1⟩,[0,0,r370,r371,r372,r373,-512]),(⟨6,2,0⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨6,2,2⟩,[r406,r139,r407,r408,128]),(⟨6,3,0⟩,[r75,r323,r324,r325,r326,r327]),(⟨7,0,0⟩,[r301,r309,r310,r311,r312,r313,r314,r315]),(⟨7,0,1⟩,[0,0,r370,r371,r372,r373,-512]),(⟨7,1,0⟩,[0,0,r370,r371,r372,r373,-512]),(⟨8,0,0⟩,[r316,r317,r318,r319,r320,r321,r322]),(⟨8,0,2⟩,[r406,r139,r407,r408,128]),(⟨8,2,0⟩,[r406,r139,r407,r408,128]),(⟨9,0,0⟩,[r75,r323,r324,r325,r326,r327])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r447) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r448) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[-1024,19200,-142848,583424,-1551872,2976000,-4157952,3245312,-380416]),(⟨6,0,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,0,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,0,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨6,1,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,1,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨6,2,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,3,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨7,0,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨7,0,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨7,1,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨8,0,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨8,0,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,2,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[512,-10752,62464,-160768,338432,-492032])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[-1024,19200,-142848,583424,-1551872,2976000,-4157952,3245312,-380416]),(⟨0,6,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,6,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,6,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,7,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,7,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨0,8,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,8,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨0,9,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨1,0,0⟩,[768,-19776,224832,-1534528,7180736,-24803584,66044288,-138254208,227036544,-285750848,262168640,-158705216,51072448,-4660096]),(⟨1,0,1⟩,[192,-6912,94464,-720640,3624640,-13205504,36747264,-79809536,134657600,-171672832,156006144,-89576704,23861824]),(⟨1,0,2⟩,[-960,21312,-194112,1005248,-3443840,8407936,-14906240,18690176,-15038400,5026112,2781632,-2348864]),(⟨1,0,3⟩,[-384,10752,-111744,641024,-2460928,6967296,-14899968,23650304,-26552704,18783744,-6027392]),(⟨1,1,0⟩,[192,-6912,94464,-720640,3624640,-13205504,36747264,-79809536,134657600,-171672832,156006144,-89576704,23861824]),(⟨1,1,1⟩,[0,0,-3072,58368,-417792,1466368,-2459648,145408,8134656,-17260544,16307200,-5970944]),(⟨1,2,0⟩,[-960,21312,-194112,1005248,-3443840,8407936,-14906240,18690176,-15038400,5026112,2781632,-2348864]),(⟨1,2,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,3,0⟩,[-384,10752,-111744,641024,-2460928,6967296,-14899968,23650304,-26552704,18783744,-6027392]),(⟨1,6,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨1,6,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,7,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[448,-14272,188928,-1443136,7319616,-26690176,73481216,-156568448,257614912,-315919808,267728384,-135989056,28521920]),(⟨2,0,1⟩,[64,-2496,35264,-272192,1421440,-5668736,17938304,-44331648,81747776,-104629952,82022080,-29832768]),(⟨2,0,2⟩,[-320,8064,-85696,513024,-1922944,4790016,-8290432,9605120,-5746496,-432768,2348864]),(⟨2,0,3⟩,[-128,3968,-47872,318208,-1336832,3881984,-8362240,13058304,-12756352,6027392]),(⟨2,1,0⟩,[64,-2496,35264,-272192,1421440,-5668736,17938304,-44331648,81747776,-104629952,82022080,-29832768]),(⟨2,1,1⟩,[0,0,-1024,22528,-196608,858112,-1710080,-14336,6193152,-10336256,5970944]),(⟨2,2,0⟩,[-320,8064,-85696,513024,-1922944,4790016,-8290432,9605120,-5746496,-432768,2348864]),(⟨2,2,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,3,0⟩,[-128,3968,-47872,318208,-1336832,3881984,-8362240,13058304,-12756352,6027392]),(⟨2,6,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨2,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,8,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[-2432,53248,-485376,2523520,-8603904,20600320,-35064832,38757120,-15713664,-26551808,47033344,-24118400]),(⟨3,0,1⟩,[-384,12544,-146816,933888,-3882240,11582976,-25249024,38715392,-38805888,22368512,-4742528]),(⟨3,0,2⟩,[2688,-50816,365312,-1379072,3162112,-4429824,2874624,1493760,-4586112,2547328]),(⟨3,0,3⟩,[768,-18944,157696,-689664,2044416,-4470272,6805504,-6535680,2706176]),(⟨3,1,0⟩,[-384,12544,-146816,933888,-3882240,11582976,-25249024,38715392,-38805888,22368512,-4742528]),(⟨3,1,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨3,2,0⟩,[2688,-50816,365312,-1379072,3162112,-4429824,2874624,1493760,-4586112,2547328]),(⟨3,2,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨3,3,0⟩,[768,-18944,157696,-689664,2044416,-4470272,6805504,-6535680,2706176]),(⟨3,6,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨4,0,0⟩,[-1088,31360,-343232,2065408,-8069504,22482176,-46729344,71985152,-77298240,51055744,-14392000]),(⟨4,0,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨4,0,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨4,1,0⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨4,2,0⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨5,0,0⟩,[1792,-32256,212992,-694272,1210368,-511488,-3453952,10236928,-13265664,7081984]),(⟨5,0,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨5,2,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨6,0,0⟩,[-256,256,14848,-106240,492544,-1494272,2647552,-3290368,2325760]),(⟨6,0,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,0,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,0,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨6,1,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,1,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨6,2,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,3,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨7,0,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨7,0,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨7,1,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨8,0,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨8,0,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,2,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[512,-10752,62464,-160768,338432,-492032])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[-1024,19200,-142848,583424,-1551872,2976000,-4157952,3245312,-380416]),(⟨0,0,7⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,0,8⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,0,9⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,1,0⟩,[768,-19776,224832,-1534528,7180736,-24803584,66044288,-138254208,227036544,-285750848,262168640,-158705216,51072448,-4660096]),(⟨0,1,1⟩,[192,-6912,94464,-720640,3624640,-13205504,36747264,-79809536,134657600,-171672832,156006144,-89576704,23861824]),(⟨0,1,2⟩,[-960,21312,-194112,1005248,-3443840,8407936,-14906240,18690176,-15038400,5026112,2781632,-2348864]),(⟨0,1,3⟩,[-384,10752,-111744,641024,-2460928,6967296,-14899968,23650304,-26552704,18783744,-6027392]),(⟨0,1,6⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,1,7⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[448,-14272,188928,-1443136,7319616,-26690176,73481216,-156568448,257614912,-315919808,267728384,-135989056,28521920]),(⟨0,2,1⟩,[64,-2496,35264,-272192,1421440,-5668736,17938304,-44331648,81747776,-104629952,82022080,-29832768]),(⟨0,2,2⟩,[-320,8064,-85696,513024,-1922944,4790016,-8290432,9605120,-5746496,-432768,2348864]),(⟨0,2,3⟩,[-128,3968,-47872,318208,-1336832,3881984,-8362240,13058304,-12756352,6027392]),(⟨0,2,6⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,2,8⟩,[-1024,12288,-30720,-36864,121856]),(⟨0,3,0⟩,[-2432,53248,-485376,2523520,-8603904,20600320,-35064832,38757120,-15713664,-26551808,47033344,-24118400]),(⟨0,3,1⟩,[-384,12544,-146816,933888,-3882240,11582976,-25249024,38715392,-38805888,22368512,-4742528]),(⟨0,3,2⟩,[2688,-50816,365312,-1379072,3162112,-4429824,2874624,1493760,-4586112,2547328]),(⟨0,3,3⟩,[768,-18944,157696,-689664,2044416,-4470272,6805504,-6535680,2706176]),(⟨0,3,6⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,4,0⟩,[-1088,31360,-343232,2065408,-8069504,22482176,-46729344,71985152,-77298240,51055744,-14392000]),(⟨0,4,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨0,4,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨0,5,0⟩,[1792,-32256,212992,-694272,1210368,-511488,-3453952,10236928,-13265664,7081984]),(⟨0,5,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨0,6,0⟩,[-256,256,14848,-106240,492544,-1494272,2647552,-3290368,2325760]),(⟨0,6,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,6,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,6,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,7,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,7,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨0,8,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,8,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨0,9,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨1,0,0⟩,[768,-19776,224832,-1534528,7180736,-24803584,66044288,-138254208,227036544,-285750848,262168640,-158705216,51072448,-4660096]),(⟨1,0,1⟩,[192,-6912,94464,-720640,3624640,-13205504,36747264,-79809536,134657600,-171672832,156006144,-89576704,23861824]),(⟨1,0,2⟩,[-960,21312,-194112,1005248,-3443840,8407936,-14906240,18690176,-15038400,5026112,2781632,-2348864]),(⟨1,0,3⟩,[-384,10752,-111744,641024,-2460928,6967296,-14899968,23650304,-26552704,18783744,-6027392]),(⟨1,0,6⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨1,0,7⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[384,-13824,188928,-1441280,7249280,-26411008,73494528,-159619072,269315200,-343345664,312012288,-179153408,47723648]),(⟨1,1,1⟩,[0,0,-6144,116736,-835584,2932736,-4919296,290816,16269312,-34521088,32614400,-11941888]),(⟨1,1,6⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,2,0⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨1,2,1⟩,[0,0,-1024,22528,-196608,858112,-1710080,-14336,6193152,-10336256,5970944]),(⟨1,2,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,3,0⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨1,3,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨1,4,0⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨1,6,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨1,6,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,7,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[448,-14272,188928,-1443136,7319616,-26690176,73481216,-156568448,257614912,-315919808,267728384,-135989056,28521920]),(⟨2,0,1⟩,[64,-2496,35264,-272192,1421440,-5668736,17938304,-44331648,81747776,-104629952,82022080,-29832768]),(⟨2,0,2⟩,[-320,8064,-85696,513024,-1922944,4790016,-8290432,9605120,-5746496,-432768,2348864]),(⟨2,0,3⟩,[-128,3968,-47872,318208,-1336832,3881984,-8362240,13058304,-12756352,6027392]),(⟨2,0,6⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨2,0,8⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,1,0⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨2,1,1⟩,[0,0,-1024,22528,-196608,858112,-1710080,-14336,6193152,-10336256,5970944]),(⟨2,1,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨2,2,0⟩,[-640,16128,-171392,1026048,-3845888,9580032,-16580864,19210240,-11492992,-865536,4697728]),(⟨2,2,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,2,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,3,0⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨2,3,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,4,0⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,5,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,6,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨2,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,8,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[-2432,53248,-485376,2523520,-8603904,20600320,-35064832,38757120,-15713664,-26551808,47033344,-24118400]),(⟨3,0,1⟩,[-384,12544,-146816,933888,-3882240,11582976,-25249024,38715392,-38805888,22368512,-4742528]),(⟨3,0,2⟩,[2688,-50816,365312,-1379072,3162112,-4429824,2874624,1493760,-4586112,2547328]),(⟨3,0,3⟩,[768,-18944,157696,-689664,2044416,-4470272,6805504,-6535680,2706176]),(⟨3,0,6⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨3,1,0⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨3,1,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨3,2,0⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨3,2,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨3,3,0⟩,[1536,-37888,315392,-1379328,4088832,-8940544,13611008,-13071360,5412352]),(⟨3,6,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨4,0,0⟩,[-1088,31360,-343232,2065408,-8069504,22482176,-46729344,71985152,-77298240,51055744,-14392000]),(⟨4,0,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨4,0,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨4,1,0⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨4,2,0⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨5,0,0⟩,[1792,-32256,212992,-694272,1210368,-511488,-3453952,10236928,-13265664,7081984]),(⟨5,0,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨5,2,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨6,0,0⟩,[-256,256,14848,-106240,492544,-1494272,2647552,-3290368,2325760]),(⟨6,0,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,0,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,0,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨6,1,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,1,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨6,2,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,3,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨7,0,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨7,0,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨7,1,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨8,0,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨8,0,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,2,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[512,-10752,62464,-160768,338432,-492032])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-2304,58560,-647808,4216896,-18385920,57782400,-136738560,247006848,-330913536,299404224,-139827840,-13951680,40673280,-5135616]),(⟨0,0,1⟩,[768,-20352,245376,-1809280,9190016,-34248448,97409792,-216056064,373301760,-486602624,442750592,-234941312,32288896,21636608]),(⟨0,0,2⟩,[448,-11392,125952,-890752,4669632,-18680320,57059840,-133803008,239312704,-313742720,277475840,-140791936,25933376]),(⟨0,0,3⟩,[-2432,54400,-517248,2844544,-10326528,26555392,-49888768,65710080,-48354432,-6002816,47542912,-30760832]),(⟨0,0,4⟩,[-1088,31360,-343232,2065408,-8069504,22482176,-46729344,71985152,-77298240,51055744,-14392000]),(⟨0,0,5⟩,[1792,-32256,212992,-694272,1210368,-511488,-3453952,10236928,-13265664,7081984]),(⟨0,0,6⟩,[-256,256,14848,-106240,492544,-1494272,2647552,-3290368,2325760]),(⟨0,0,7⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,0,8⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,0,9⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,1,0⟩,[768,-20352,245376,-1809280,9190016,-34248448,97409792,-216056064,373301760,-486602624,442750592,-234941312,32288896,21636608]),(⟨0,1,1⟩,[384,-13824,188928,-1432064,7077248,-25243648,69974016,-156295168,276829312,-367245824,334628352,-181184000,41143424]),(⟨0,1,2⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨0,1,3⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨0,1,4⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨0,1,6⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,1,7⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[448,-11392,125952,-890752,4669632,-18680320,57059840,-133803008,239312704,-313742720,277475840,-140791936,25933376]),(⟨0,2,1⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨0,2,2⟩,[-640,13824,-128384,734208,-2965760,8749056,-18459392,25185280,-17147008,-357888,6342784]),(⟨0,2,3⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨0,2,4⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨0,2,5⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨0,2,6⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,2,8⟩,[-1024,12288,-30720,-36864,121856]),(⟨0,3,0⟩,[-2432,54400,-517248,2844544,-10326528,26555392,-49888768,65710080,-48354432,-6002816,47542912,-30760832]),(⟨0,3,1⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨0,3,2⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨0,3,3⟩,[1536,-37888,315392,-1379328,4088832,-8940544,13611008,-13071360,5412352]),(⟨0,3,6⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,4,0⟩,[-1088,31360,-343232,2065408,-8069504,22482176,-46729344,71985152,-77298240,51055744,-14392000]),(⟨0,4,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨0,4,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨0,5,0⟩,[1792,-32256,212992,-694272,1210368,-511488,-3453952,10236928,-13265664,7081984]),(⟨0,5,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨0,6,0⟩,[-256,256,14848,-106240,492544,-1494272,2647552,-3290368,2325760]),(⟨0,6,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,6,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,6,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨0,7,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨0,7,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨0,8,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨0,8,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨0,9,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨1,0,0⟩,[768,-20352,245376,-1809280,9190016,-34248448,97409792,-216056064,373301760,-486602624,442750592,-234941312,32288896,21636608]),(⟨1,0,1⟩,[384,-13824,188928,-1432064,7077248,-25243648,69974016,-156295168,276829312,-367245824,334628352,-181184000,41143424]),(⟨1,0,2⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨1,0,3⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨1,0,4⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨1,0,6⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨1,0,7⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[384,-13824,188928,-1432064,7077248,-25243648,69974016,-156295168,276829312,-367245824,334628352,-181184000,41143424]),(⟨1,1,1⟩,[0,0,-9216,175104,-1253376,4399104,-7378944,436224,24403968,-51781632,48921600,-17912832]),(⟨1,1,2⟩,[0,0,-1024,22528,-196608,858112,-1710080,-14336,6193152,-10336256,5970944]),(⟨1,1,3⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨1,1,6⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,2,0⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨1,2,1⟩,[0,0,-1024,22528,-196608,858112,-1710080,-14336,6193152,-10336256,5970944]),(⟨1,2,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,3,0⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨1,3,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨1,4,0⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨1,6,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨1,6,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨1,7,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[448,-11392,125952,-890752,4669632,-18680320,57059840,-133803008,239312704,-313742720,277475840,-140791936,25933376]),(⟨2,0,1⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨2,0,2⟩,[-640,13824,-128384,734208,-2965760,8749056,-18459392,25185280,-17147008,-357888,6342784]),(⟨2,0,3⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨2,0,4⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,0,5⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,0,6⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨2,0,8⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,1,0⟩,[-896,18816,-158848,733056,-2022400,2739200,3032064,-25641472,66709376,-99603840,84803712,-32181632]),(⟨2,1,1⟩,[0,0,-1024,22528,-196608,858112,-1710080,-14336,6193152,-10336256,5970944]),(⟨2,1,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨2,2,0⟩,[-640,13824,-128384,734208,-2965760,8749056,-18459392,25185280,-17147008,-357888,6342784]),(⟨2,2,1⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨2,2,2⟩,[768,-16896,147456,-643584,1282560,10752,-4644864,7752192,-4478208]),(⟨2,2,3⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,2,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,3,0⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨2,3,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,4,0⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,5,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,6,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨2,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,8,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[-2432,54400,-517248,2844544,-10326528,26555392,-49888768,65710080,-48354432,-6002816,47542912,-30760832]),(⟨3,0,1⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨3,0,2⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨3,0,3⟩,[1536,-37888,315392,-1379328,4088832,-8940544,13611008,-13071360,5412352]),(⟨3,0,6⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨3,1,0⟩,[-768,23296,-258560,1574912,-6343168,18550272,-40148992,62365696,-65358592,41152256,-10769920]),(⟨3,1,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨3,2,0⟩,[2560,-46848,317440,-1060864,1825280,-547840,-5487616,14552064,-17342464,8574720]),(⟨3,2,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨3,3,0⟩,[1536,-37888,315392,-1379328,4088832,-8940544,13611008,-13071360,5412352]),(⟨3,6,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨4,0,0⟩,[-1088,31360,-343232,2065408,-8069504,22482176,-46729344,71985152,-77298240,51055744,-14392000]),(⟨4,0,1⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨4,0,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨4,1,0⟩,[0,0,6144,-96256,493568,-944128,-104448,3405824,-5441536,2680832]),(⟨4,2,0⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨5,0,0⟩,[1792,-32256,212992,-694272,1210368,-511488,-3453952,10236928,-13265664,7081984]),(⟨5,0,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨5,2,0⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨6,0,0⟩,[-256,256,14848,-106240,492544,-1494272,2647552,-3290368,2325760]),(⟨6,0,1⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,0,2⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,0,3⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨6,1,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨6,1,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨6,2,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨6,3,0⟩,[512,-10752,62464,-160768,338432,-492032]),(⟨7,0,0⟩,[-256,7424,-68352,308992,-864000,1774336,-2581760,1947904]),(⟨7,0,1⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨7,1,0⟩,[0,0,4096,-49152,122880,147456,-487424]),(⟨8,0,0⟩,[1280,-19456,94464,-200704,292608,-238592,-191744]),(⟨8,0,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,2,0⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[512,-10752,62464,-160768,338432,-492032])]


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
    (Poly.add (Poly.scale (K.ofRat r449) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 6).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r447*r448 : ℚ)=r449 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 6 r447 r448 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=6 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 6).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C076

#print axioms Coulomb8.Columns.C076.sound
