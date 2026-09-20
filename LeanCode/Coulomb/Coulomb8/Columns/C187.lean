import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C187

def r0 : ℚ := { num := -256, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 3328, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -16640, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 4864, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 6656, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -221696, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 228864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -509440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 2041600, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -243968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -21248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 512, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -2048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -131072, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 181248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -1298432, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 988160, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 16384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -7851520, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 8464384, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -150016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -24064, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 10240, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -210944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 254976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 2040832, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -2742272, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 4249600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -12276224, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 258560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -2048, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 26624, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -124928, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 2048, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -624640, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 34816, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -1857536, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 247808, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 45056, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 22528, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -88064, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 268288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -2643968, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1378304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -317440, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 256, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -3328, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 16640, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -4864, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -6656, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 221696, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -228864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 509440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -2041600, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 243968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 21248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 128, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 1408, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -16768, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 12032, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -75520, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 1065728, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -41728, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 5760, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -750464, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 837248, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 4864, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -8320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 20480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -54784, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 963328, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -4096, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 6379136, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -7265536, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 238720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 14080, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -38912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 481280, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -786944, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -42496, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 5642240, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -10545152, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 3090176, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -204032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -22528, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 115712, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 2048, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -260096, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 977920, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -4096, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -205312, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1024, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -13312, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -11264, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -199680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 1725440, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -2513920, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 89088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -4864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 834304, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -2589184, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 22016, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 2633216, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -1450496, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 10860800, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -1469184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -128, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 11008, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 4224, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -111744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 177920, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -187904, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -1024256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 4086912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -19765376, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 18089728, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -3100544, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 27264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 2816, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -33536, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 122368, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -507392, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 1470464, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -1165824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 6912512, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -7256320, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 3435776, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -68352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 1536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -6144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -86528, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 626176, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -894464, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -419840, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 5065216, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -4990208, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -123904, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -22528, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -3072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 16384, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -1024, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 321536, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -39936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 942080, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -689152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 158720, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -5120, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -176128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 1354240, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -90112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1804800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 13574144, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -19430144, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 19309568, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -613120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 5888, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -5504, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 62464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -481024, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -51712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 2878208, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -1489920, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 1003648, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 5906176, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -765824, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 13824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -312320, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 281088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -413184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 564736, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 756736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -5332480, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 677120, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -512, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -13824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -128512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 1805824, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -81920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -193024, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 28928, den := 51, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -512, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -16384, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 327680, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1042432, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 1733632, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -2920448, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 425984, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 3584, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -4096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 56320, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -19456, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 9728, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -747520, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 1147904, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -842752, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 16640, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 5120, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -20992, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 256000, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 33280, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 1024, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -512, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 2048, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -45056, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 366592, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -106496, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 260096, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 856064, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -10240, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -10240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 205312, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 3328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -13568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 1280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 107008, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -90624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -833024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 3268096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -931584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 78592, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -10138880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 695040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -13568, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 88576, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -237824, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -18688, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 644608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -941056, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 12417536, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -15353600, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 15946496, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -3682816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -2304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 9984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -4223488, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 4715008, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -9447936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 35693312, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -1099520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 10138880, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -231680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -275456, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 5120, den := 51, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 2575360, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -11052032, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 19337216, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -5647360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 5304832, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 772096, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 3072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -59392, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 31744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 570368, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -3027968, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 2549760, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -4246528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 1446400, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -8192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 360448, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -763904, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -40960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 47104, den := 51, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 5120, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -5888, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 151552, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -75776, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -1773568, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 8923648, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -3008512, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 8923392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -4983808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -4835584, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 640, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -11008, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 20864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -31744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -540928, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 947712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -3984640, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -1620992, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 3121024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -1720576, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 374400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -1024, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 12928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -229120, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 5711872, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -9592064, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 5952512, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 1004672, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -15176704, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 1377920, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -256, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 73216, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -144384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 995840, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -645632, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -174592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -1233920, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 762368, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -471808, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -29696, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 30208, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 59904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -180736, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -455680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 3865088, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -469760, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -512, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 51712, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -38912, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 460800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -4885504, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 4405248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -7493632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 25810432, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -29172224, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 1962496, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -30208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 67072, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -298496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -280576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 7313920, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -11274752, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 4911616, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -354560, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -12800, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 71168, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -27136, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -158720, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 1232384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -5498368, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 2123264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -723200, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 4096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -180224, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 381952, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 20480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -23552, den := 51, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 6144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -335872, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1976320, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -3964928, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 1546240, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 352256, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -2048, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -2048, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -11776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 512, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 45056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -80896, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -575488, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 12288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -128000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 655360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -1855488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 2410496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 1729536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -11341824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 15008256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -1071104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 368640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 23552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -16384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 987136, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -212992, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -8369152, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 3878912, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -45769216, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 6851584, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -3141632, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -13312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 412672, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -527360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 913408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -1672192, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -736256, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 1108992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -216576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 259072, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -1094656, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 558080, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 4725760, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -3406848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 160768, den := 51, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 2048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -349184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 858112, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 76800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 51200, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -247808, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 378880, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 1100800, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -7579648, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 4679680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -8120320, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 9728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 13312, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -63488, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -99328, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 517632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -31744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 8204288, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -8748032, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 319232, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 512, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -128000, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 644608, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -1243136, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1502720, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -873472, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -174592, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 16896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 11776, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -1033216, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 255488, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 2048, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -169984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 1626112, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -1839104, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 1058816, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -67584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -231424, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 1233920, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -216064, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -8192, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 40960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -40960, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 16384, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -163840, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 16384, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 90112, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -1536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 22528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -112640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 391168, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -1373184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 3590144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -7804928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 9168896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -104960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -264192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 503808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -1138688, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -2373632, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 825344, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 15360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -311296, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 259072, den := 357, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -3215360, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 23552, den := 51, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 98304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -1703936, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 3375104, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -16384, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 4096, den := 2499, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -16384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 49152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -4096, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -64, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -4160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 1664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -55424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 171648, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -382080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 510400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -182976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -15936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -7488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 135936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -324608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 247040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 12288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -1962880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 2116096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -112512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -6016, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 2560, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -158208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 191232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 510208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -2056704, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 3187200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -3069056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 193920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 6656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -31232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -156160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 26112, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -464384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 61952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 5632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -22016, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 201216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -660992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 1033728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -1664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 8320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -3328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 110848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -343296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 764160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -1020800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 365952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 31872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 14976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -135936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 324608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -247040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -12288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 1962880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -2116096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 112512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 9088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 297216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -910592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 1414656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -1247744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 70272, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -101760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 2944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 165888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -380160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 71936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 1536512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -3788800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 4535680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -376704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := 16640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -20224, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 128256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -738048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 1804032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -2244864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 151040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -3840, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 24320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -137472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := 802560, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -1713920, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 189184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 1024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -26624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -976896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 47104, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 1284096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -3878912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 535552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -184320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -2432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 24576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -134656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 319232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := 12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := -1980416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 4253184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -4597632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 365440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -12032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 82176, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -391424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 923904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -184064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 1361664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -96512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := -43264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := 189184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -934144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 304896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -255232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -5120, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -22528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 159232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -218112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -27136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 8192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -20480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := -79872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := 529408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := -110592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := 290816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 49664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 18944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -155136, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 221696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 131584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -420352, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 66048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := -73216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 281600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -719872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 1099264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -84480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -4608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := -115712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 616960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -108032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -1024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := 118784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -518144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 1121280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -1762304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 223232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 4608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := 115712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := -616960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 108032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := -61440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := -12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := 122880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := 24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 64, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 3392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -26752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 22656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := 208256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := -817024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := 232896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -19648, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := 2534720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -173760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := -192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -21568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := -31872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 1392256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := -3120640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := 4437312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := -4827392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 459840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := -27136, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 74752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := -433152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := 1284608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := -211968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := 99584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := 70656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := -7936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := 5888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := -65792, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := -121088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := 608000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := -1315072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := 2242816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := -253696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r685 : ℚ := { num := -2816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r686 : ℚ := { num := 7936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r687 : ℚ := { num := 28416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r688 : ℚ := { num := -162048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r689 : ℚ := { num := 60160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r690 : ℚ := { num := 3840, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r691 : ℚ := { num := -7936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r692 : ℚ := { num := -6784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r693 : ℚ := { num := 640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r694 : ℚ := { num := 53504, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r695 : ℚ := { num := -45312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r696 : ℚ := { num := -416512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r697 : ℚ := { num := 1634048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r698 : ℚ := { num := -465792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r699 : ℚ := { num := 39296, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r700 : ℚ := { num := -5069440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r701 : ℚ := { num := 347520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r702 : ℚ := { num := 192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r703 : ℚ := { num := 21568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r704 : ℚ := { num := -512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r705 : ℚ := { num := -1392256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r706 : ℚ := { num := 3120640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r707 : ℚ := { num := -4437312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r708 : ℚ := { num := 4827392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r709 : ℚ := { num := -459840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r710 : ℚ := { num := 179968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r711 : ℚ := { num := -1078528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r712 : ℚ := { num := 3328000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r713 : ℚ := { num := -6268928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r714 : ℚ := { num := 7293056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r715 : ℚ := { num := -490624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r716 : ℚ := { num := 14080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r717 : ℚ := { num := -69120, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r718 : ℚ := { num := 68352, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r719 : ℚ := { num := 598784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r720 : ℚ := { num := -2605824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r721 : ℚ := { num := 4635136, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r722 : ℚ := { num := -4423424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r723 : ℚ := { num := 329600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r724 : ℚ := { num := 2304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r725 : ℚ := { num := -14848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r726 : ℚ := { num := 23808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r727 : ℚ := { num := 142592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r728 : ℚ := { num := -756992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r729 : ℚ := { num := 1912320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r730 : ℚ := { num := -3184896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r731 : ℚ := { num := 361600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r732 : ℚ := { num := 90112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r733 : ℚ := { num := -190976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r734 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r735 : ℚ := { num := 11776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r736 : ℚ := { num := -6400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r737 : ℚ := { num := 46080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r738 : ℚ := { num := -6144, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r739 : ℚ := { num := -47616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r740 : ℚ := { num := 3023360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r741 : ℚ := { num := -1317888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r742 : ℚ := { num := 15505408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r743 : ℚ := { num := -14785280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r744 : ℚ := { num := 49408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r745 : ℚ := { num := 27904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r746 : ℚ := { num := -2560, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r747 : ℚ := { num := -477696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r748 : ℚ := { num := 1997824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r749 : ℚ := { num := -3320064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r750 : ℚ := { num := 2180608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r751 : ℚ := { num := -75904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r752 : ℚ := { num := 4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r753 : ℚ := { num := -494080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r754 : ℚ := { num := 280064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r755 : ℚ := { num := -4197888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r756 : ℚ := { num := 5020160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r757 : ℚ := { num := -332288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r758 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r759 : ℚ := { num := -20480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r760 : ℚ := { num := 361472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r761 : ℚ := { num := -337408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r762 : ℚ := { num := -378368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r763 : ℚ := { num := 123904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r764 : ℚ := { num := -512, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r765 : ℚ := { num := 29696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r766 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r767 : ℚ := { num := -14848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r768 : ℚ := { num := 1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r769 : ℚ := { num := 24064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r770 : ℚ := { num := 646144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r771 : ℚ := { num := -2082816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r772 : ℚ := { num := 4450816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r773 : ℚ := { num := -4584448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r774 : ℚ := { num := 52480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r775 : ℚ := { num := -18944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r776 : ℚ := { num := 136704, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r777 : ℚ := { num := -9216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r778 : ℚ := { num := 528384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r779 : ℚ := { num := 593408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r780 : ℚ := { num := -206336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r781 : ℚ := { num := 44032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r782 : ℚ := { num := -80384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r783 : ℚ := { num := -147456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r784 : ℚ := { num := 851968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r785 : ℚ := { num := -1687552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r786 : ℚ := { num := 8192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r787 : ℚ := { num := -576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r788 : ℚ := { num := -1472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r789 : ℚ := { num := 36544, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r790 : ℚ := { num := -9344, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r791 : ℚ := { num := 14976, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r792 : ℚ := { num := 16256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r793 : ℚ := { num := -598912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r794 : ℚ := { num := 840768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r795 : ℚ := { num := -456768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r796 : ℚ := { num := 15936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r797 : ℚ := { num := 7488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r798 : ℚ := { num := -1152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r799 : ℚ := { num := 7104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r800 : ℚ := { num := -33280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r801 : ℚ := { num := 276736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r802 : ℚ := { num := -719232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r803 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r804 : ℚ := { num := 1060160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r805 : ℚ := { num := -522112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r806 : ℚ := { num := 4148672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r807 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r808 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r809 : ℚ := { num := -49408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r810 : ℚ := { num := -15360, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r811 : ℚ := { num := 2282496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r812 : ℚ := { num := -3933568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r813 : ℚ := { num := 3069056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r814 : ℚ := { num := -193920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r815 : ℚ := { num := -9472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r816 : ℚ := { num := 123904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r817 : ℚ := { num := -363008, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r818 : ℚ := { num := 304384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r819 : ℚ := { num := 398336, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r820 : ℚ := { num := -708480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r821 : ℚ := { num := -61952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r822 : ℚ := { num := -11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r823 : ℚ := { num := -5632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r824 : ℚ := { num := 22016, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r825 : ℚ := { num := -201216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r826 : ℚ := { num := 660992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r827 : ℚ := { num := -1033728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r828 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r829 : ℚ := { num := 1152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r830 : ℚ := { num := -73088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r831 : ℚ := { num := 18688, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r832 : ℚ := { num := -29952, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r833 : ℚ := { num := -32512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r834 : ℚ := { num := 1197824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r835 : ℚ := { num := -1681536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r836 : ℚ := { num := 913536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r837 : ℚ := { num := -14976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r838 : ℚ := { num := -7104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r839 : ℚ := { num := 14848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r840 : ℚ := { num := 33280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r841 : ℚ := { num := -276736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r842 : ℚ := { num := 719232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r843 : ℚ := { num := -13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r844 : ℚ := { num := -1060160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r845 : ℚ := { num := 522112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r846 : ℚ := { num := -4148672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r847 : ℚ := { num := -4736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r848 : ℚ := { num := 36480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r849 : ℚ := { num := -137216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r850 : ℚ := { num := -15104, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r851 : ℚ := { num := -171264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r852 : ℚ := { num := 552960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r853 : ℚ := { num := 181504, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r854 : ℚ := { num := -70272, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r855 : ℚ := { num := 101760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r856 : ℚ := { num := -3456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r857 : ℚ := { num := 41472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r858 : ℚ := { num := -233984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r859 : ℚ := { num := 527616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r860 : ℚ := { num := 28928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r861 : ℚ := { num := -2152960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r862 : ℚ := { num := 4215296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r863 : ℚ := { num := -4535680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r864 : ℚ := { num := 376704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r865 : ℚ := { num := 13568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r866 : ℚ := { num := -84736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r867 : ℚ := { num := 167680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r868 : ℚ := { num := -27392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r869 : ℚ := { num := 121600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r870 : ℚ := { num := -1377536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r871 : ℚ := { num := 2244864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r872 : ℚ := { num := -151040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r873 : ℚ := { num := 3840, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r874 : ℚ := { num := -24320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r875 : ℚ := { num := 4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r876 : ℚ := { num := 137472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r877 : ℚ := { num := -802560, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r878 : ℚ := { num := 1713920, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r879 : ℚ := { num := -189184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r880 : ℚ := { num := -64000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r881 : ℚ := { num := 327680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r882 : ℚ := { num := -927744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r883 : ℚ := { num := 1205248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r884 : ℚ := { num := 864768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r885 : ℚ := { num := -5670912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r886 : ℚ := { num := 7504128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r887 : ℚ := { num := -535552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r888 : ℚ := { num := 184320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r889 : ℚ := { num := -128, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r890 : ℚ := { num := -41472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r891 : ℚ := { num := 110080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r892 : ℚ := { num := -164608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r893 : ℚ := { num := 1754624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r894 : ℚ := { num := -3506816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r895 : ℚ := { num := 4597632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r896 : ℚ := { num := -365440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r897 : ℚ := { num := -9984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r898 : ℚ := { num := 80128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r899 : ℚ := { num := -229632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r900 : ℚ := { num := 290560, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r901 : ℚ := { num := -307456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r902 : ℚ := { num := 123136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r903 : ℚ := { num := -1361664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r904 : ℚ := { num := 96512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r905 : ℚ := { num := 43264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r906 : ℚ := { num := -189184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r907 : ℚ := { num := 934144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r908 : ℚ := { num := -304896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r909 : ℚ := { num := 255232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r910 : ℚ := { num := -159232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r911 : ℚ := { num := 218112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r912 : ℚ := { num := 27136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r913 : ℚ := { num := 79872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r914 : ℚ := { num := -529408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r915 : ℚ := { num := 110592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r916 : ℚ := { num := -290816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r917 : ℚ := { num := 6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r918 : ℚ := { num := -49664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r919 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r920 : ℚ := { num := 155136, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r921 : ℚ := { num := -221696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r922 : ℚ := { num := -131584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r923 : ℚ := { num := 420352, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r924 : ℚ := { num := -66048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r925 : ℚ := { num := 73216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r926 : ℚ := { num := -281600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r927 : ℚ := { num := 719872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r928 : ℚ := { num := -1099264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r929 : ℚ := { num := 84480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r930 : ℚ := { num := -118784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r931 : ℚ := { num := 518144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r932 : ℚ := { num := -1121280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r933 : ℚ := { num := 1762304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r934 : ℚ := { num := -223232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r935 : ℚ := { num := 61440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r936 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r937 : ℚ := { num := -122880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r938 : ℚ := { num := 40960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r939 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r940 : ℚ := { num := -3392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r941 : ℚ := { num := 320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r942 : ℚ := { num := 26752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r943 : ℚ := { num := -22656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r944 : ℚ := { num := -208256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r945 : ℚ := { num := 817024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r946 : ℚ := { num := -232896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r947 : ℚ := { num := 19648, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r948 : ℚ := { num := -2534720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r949 : ℚ := { num := 173760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r950 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r951 : ℚ := { num := 33088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r952 : ℚ := { num := -92160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r953 : ℚ := { num := 73856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r954 : ℚ := { num := 319488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r955 : ℚ := { num := -30592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r956 : ℚ := { num := 3544064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r957 : ℚ := { num := -5031360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r958 : ℚ := { num := 48640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r959 : ℚ := { num := 68608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r960 : ℚ := { num := 680448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r961 : ℚ := { num := -1705472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r962 : ℚ := { num := 238080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r963 : ℚ := { num := -99584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r964 : ℚ := { num := -70656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r965 : ℚ := { num := 15104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r966 : ℚ := { num := -71424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r967 : ℚ := { num := 6400, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r968 : ℚ := { num := 142080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r969 : ℚ := { num := -822016, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r970 : ℚ := { num := 1619712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r971 : ℚ := { num := -2242816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r972 : ℚ := { num := 253696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r973 : ℚ := { num := 2816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r974 : ℚ := { num := -28416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r975 : ℚ := { num := 162048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r976 : ℚ := { num := -60160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r977 : ℚ := { num := -3840, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r978 : ℚ := { num := 7936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r979 : ℚ := { num := 6784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r980 : ℚ := { num := -53504, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r981 : ℚ := { num := 45312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r982 : ℚ := { num := 416512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r983 : ℚ := { num := -1634048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r984 : ℚ := { num := 465792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r985 : ℚ := { num := -39296, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r986 : ℚ := { num := 5069440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r987 : ℚ := { num := -347520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r988 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r989 : ℚ := { num := -33088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r990 : ℚ := { num := 92160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r991 : ℚ := { num := -73856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r992 : ℚ := { num := -319488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r993 : ℚ := { num := 30592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r994 : ℚ := { num := -3544064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r995 : ℚ := { num := 5031360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r996 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r997 : ℚ := { num := -179968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r998 : ℚ := { num := 1078528, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r999 : ℚ := { num := -3328000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1000 : ℚ := { num := 6268928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1001 : ℚ := { num := -7293056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1002 : ℚ := { num := 490624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1003 : ℚ := { num := 128, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1004 : ℚ := { num := -32000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1005 : ℚ := { num := 8448, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1006 : ℚ := { num := -163584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1007 : ℚ := { num := -681984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1008 : ℚ := { num := 3104000, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1009 : ℚ := { num := -5274880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1010 : ℚ := { num := 4423424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1011 : ℚ := { num := -329600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1012 : ℚ := { num := -5888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1013 : ℚ := { num := 30976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1014 : ℚ := { num := -57600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1015 : ℚ := { num := -122368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1016 : ℚ := { num := 52992, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1017 : ℚ := { num := -2186496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1018 : ℚ := { num := 3184896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1019 : ℚ := { num := -361600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1020 : ℚ := { num := -6656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1021 : ℚ := { num := 190976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1022 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1023 : ℚ := { num := -11776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1024 : ℚ := { num := 9472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1025 : ℚ := { num := -89088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1026 : ℚ := { num := 273408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1027 : ℚ := { num := 222720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1028 : ℚ := { num := -3517952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1029 : ℚ := { num := 10066944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1030 : ℚ := { num := -15870976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1031 : ℚ := { num := 14785280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1032 : ℚ := { num := -49408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1033 : ℚ := { num := -72192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1034 : ℚ := { num := 54784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1035 : ℚ := { num := 539904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1036 : ℚ := { num := -2281984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1037 : ℚ := { num := 3655168, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1038 : ℚ := { num := -2180608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1039 : ℚ := { num := 75904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1040 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1041 : ℚ := { num := 494080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1042 : ℚ := { num := -280064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1043 : ℚ := { num := 4197888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1044 : ℚ := { num := -5020160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1045 : ℚ := { num := 332288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1046 : ℚ := { num := -49664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1047 : ℚ := { num := 204800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1048 : ℚ := { num := -287744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1049 : ℚ := { num := 93696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1050 : ℚ := { num := 378368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1051 : ℚ := { num := -123904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1052 : ℚ := { num := 512, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1053 : ℚ := { num := -29696, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1054 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1055 : ℚ := { num := 14848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1056 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1057 : ℚ := { num := 11264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1058 : ℚ := { num := -56320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1059 : ℚ := { num := 195584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1060 : ℚ := { num := -686592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1061 : ℚ := { num := 1795072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1062 : ℚ := { num := -3902464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1063 : ℚ := { num := 4584448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1064 : ℚ := { num := -52480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1065 : ℚ := { num := -198144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1066 : ℚ := { num := 377856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1067 : ℚ := { num := -284672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1068 : ℚ := { num := -593408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1069 : ℚ := { num := 206336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1070 : ℚ := { num := -44032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1071 : ℚ := { num := 433152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1072 : ℚ := { num := -947712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1073 : ℚ := { num := 80384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1074 : ℚ := { num := 147456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1075 : ℚ := { num := -851968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1076 : ℚ := { num := 1687552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1077 : ℚ := { num := -8192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1078 : ℚ := { num := -45056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1079 : ℚ := { num := 157184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1080 : ℚ := { num := -199168, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1081 : ℚ := { num := -187904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1082 : ℚ := { num := 980992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1083 : ℚ := { num := -193024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1084 : ℚ := { num := 3200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1085 : ℚ := { num := -17216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1086 : ℚ := { num := 1536, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1087 : ℚ := { num := -367872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1088 : ℚ := { num := 627072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1089 : ℚ := { num := -109056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1090 : ℚ := { num := -1627072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1091 : ℚ := { num := 436096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1092 : ℚ := { num := -18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1093 : ℚ := { num := 151040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1094 : ℚ := { num := -5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1095 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1096 : ℚ := { num := -27904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1097 : ℚ := { num := 298496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1098 : ℚ := { num := 65024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1099 : ℚ := { num := -120320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1100 : ℚ := { num := -11264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1101 : ℚ := { num := -314368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1102 : ℚ := { num := 375808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1103 : ℚ := { num := -1961984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1104 : ℚ := { num := 386048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1105 : ℚ := { num := -3200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1106 : ℚ := { num := 17216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1107 : ℚ := { num := -1536, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1108 : ℚ := { num := 367872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1109 : ℚ := { num := -627072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1110 : ℚ := { num := 109056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1111 : ℚ := { num := 1627072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1112 : ℚ := { num := -436096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1113 : ℚ := { num := -45568, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1114 : ℚ := { num := 167424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1115 : ℚ := { num := -267264, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1116 : ℚ := { num := -40448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1117 : ℚ := { num := 1081856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1118 : ℚ := { num := -281088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1119 : ℚ := { num := 9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1120 : ℚ := { num := -100864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1121 : ℚ := { num := 88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1122 : ℚ := { num := -331776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1123 : ℚ := { num := 788992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1124 : ℚ := { num := -221184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1125 : ℚ := { num := -2092032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1126 : ℚ := { num := 36864, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1127 : ℚ := { num := -384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1128 : ℚ := { num := 18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1129 : ℚ := { num := -151040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1130 : ℚ := { num := 5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1131 : ℚ := { num := 4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1132 : ℚ := { num := 10240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1133 : ℚ := { num := -9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1134 : ℚ := { num := 100864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1135 : ℚ := { num := -88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1136 : ℚ := { num := -11520, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1137 : ℚ := { num := 31232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1138 : ℚ := { num := -41984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1139 : ℚ := { num := 106752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1140 : ℚ := { num := -423424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1141 : ℚ := { num := 4992, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1142 : ℚ := { num := 84480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1143 : ℚ := { num := -55296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1144 : ℚ := { num := -35328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1145 : ℚ := { num := 420864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1146 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1147 : ℚ := { num := 30208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1148 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1149 : ℚ := { num := -20992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1150 : ℚ := { num := 214016, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1151 : ℚ := { num := -2560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1152 : ℚ := { num := 11520, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1153 : ℚ := { num := 41984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1154 : ℚ := { num := -106752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1155 : ℚ := { num := 423424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1156 : ℚ := { num := -4992, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1157 : ℚ := { num := -1280, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1158 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1159 : ℚ := { num := -74496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1160 : ℚ := { num := 95232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1161 : ℚ := { num := 83200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1162 : ℚ := { num := -71168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1163 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1164 : ℚ := { num := 33792, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1165 : ℚ := { num := -143872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1166 : ℚ := { num := 2304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1167 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1168 : ℚ := { num := -168960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1169 : ℚ := { num := 110592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1170 : ℚ := { num := -841728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1171 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1172 : ℚ := { num := 44288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1173 : ℚ := { num := -3072, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1174 : ℚ := { num := -62208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1175 : ℚ := { num := 284160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1176 : ℚ := { num := -2816, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1177 : ℚ := { num := -73728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1178 : ℚ := { num := 2048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1179 : ℚ := { num := -67584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1180 : ℚ := { num := 40448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1181 : ℚ := { num := 287744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1182 : ℚ := { num := -4608, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1183 : ℚ := { num := -24576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1184 : ℚ := { num := 73728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1185 : ℚ := { num := -2048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1186 : ℚ := { num := -9728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1187 : ℚ := { num := -48640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1188 : ℚ := { num := -43776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1189 : ℚ := { num := -31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1190 : ℚ := { num := -15360, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1191 : ℚ := { num := 102656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1192 : ℚ := { num := 9728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1193 : ℚ := { num := -123904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1194 : ℚ := { num := 43776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1195 : ℚ := { num := 31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1196 : ℚ := { num := 30720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1197 : ℚ := { num := -205312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1198 : ℚ := { num := 12032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1199 : ℚ := { num := -102656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1200 : ℚ := { num := 1, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1201 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1202 : ℚ := { num := 1, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11],[0,0,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22],[0,0,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32],[0,0,r33,r34,r35,r36,r37,r38,r39,r40,r41],[0,0,r33,r42,r43,r13,r44,r45,r46,r47],[],[],[],[],[],[],[0,0,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59],[0,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71],[0,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82],[0,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[0,r23,r93,r94,r95,r96,r97,r98,r99,r100],[0,r101,r102,r103,r104,r105,r106,r107,r108],[],[],[],[],[],[0,0,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r58,r59],[r60,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130],[0,r0,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140],[r0,r141,r142,r143,r144,r145,r146,r147,r148,r149,r150],[0,r101,r151,r152,r153,r154,r155,r156,r157,r158],[],[],[],[],[0,r48,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168],[r72,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178],[0,r179,r180,r181,r182,r183,r184,r185,r186,r187],[r48,r188,r152,r189,r190,r191,r192,r193,r194],[],[],[],[0,r195,r196,r197,r198,r199,r200,r201,r202,r203],[r204,r205,r206,r207,r208,r209,r210,r211,r212],[0,r195,r213,r214,r215,r216,r217,r218],[],[],[0,r219,r220,r221,r222,r223,r224,r225],[r195,r217,r24,r226,r227,r217,r218],[],[],[0,r83,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238],[0,r204,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r10,r11],[0,r204,r249,r250,r76,r251,r252,r253,r254,r255,r256,r257,r258],[0,r188,r206,r259,r260,r261,r262,r263,r264,r265,r266,-1024],[r195,r267,r268,r269,r270,r271,r272,r273,r274],[0,r219,r275,r34,r276,r277,r278,r279],[],[],[],[],[r0,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289,r21,r22],[0,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300],[r301,r302,r303,r269,r304,r305,r306,r307,r308,r309,r310],[0,r311,r312,r313,r314,r315,r316,r317,r318,r319],[r0,r141,r320,r321,r322,r323,r324,r325,r326],[],[],[],[r12,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336],[0,r169,r337,r338,r339,r340,r341,r342,r343,r344],[r204,r345,r346,r347,r348,r349,r350,r351,r352],[0,r153,r353,r102,r354,r355,r356,r357],[],[],[0,0,r358,r359,r360,r361,r362,r363,r364],[0,r365,r213,r345,r366,r367,r368,r369],[],[],[r153,r96,r370,r371,r372,r373,r374],[],[0,r365,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384],[r12,r151,r385,r386,r387,r388,r389,r390,r391,r392,r393],[0,r23,r394,r395,r396,r397,r398,r399,r400,r401],[0,r153,r302,r402,r403,r404,r405,r406,r407],[0,r153,r408,r302,r282,r409,r410,r411],[],[],[0,r188,r412,r413,r414,r415,r416,r417,r418,r419],[r83,r420,r421,r422,r423,r424,r425,r426,r427],[0,r428,r429,r430,r431,r432,r433,r434],[r12,r151,r435,r93,r436,r437,r438],[],[0,0,r439,r440,r441,r442,r443,r444],[0,r101,r151,r13,r445,r446,r447],[0,0,r448,r449,r450,r451],[0,r448,r452,r453,r454,r455],[r456,r457,r458,r459,r460,r461,r462,r463,r464],[0,r205,r25,r465,r466,r467,r468,r469],[r101,r205,r470,r471,r472,r473,r474],[],[0,0,r196,r475,r476,r477,r478],[0,r479,r480,r449,r481,r482],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,2⟩,[0,0,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨0,0,3⟩,[0,0,r301,r456,r495,r496,r497,r498,r499,r500,r501,r502,r503]),(⟨0,0,4⟩,[0,0,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513]),(⟨0,0,5⟩,[0,0,r365,r514,r515,r516,r517,r518,r519,r520,r368]),(⟨0,0,6⟩,[0,0,r365,r521,r522,r456,r523,r524,r525,r526]),(⟨0,1,1⟩,[0,0,r301,r527,r528,r529,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨0,1,2⟩,[0,0,r72,r141,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨0,1,3⟩,[0,0,r547,r548,r337,r189,r549,r550,r551,r552,r553,r554]),(⟨0,1,4⟩,[0,r72,r555,r515,r556,r557,r558,r559,r560,r561,r562]),(⟨0,1,5⟩,[0,r204,r530,r563,r564,r565,r566,r567,r568,r569]),(⟨0,1,6⟩,[0,r204,r570,r571,r572,r573,r574,r575,r576]),(⟨0,2,0⟩,[0,0,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨0,2,1⟩,[0,0,r72,r141,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨0,2,2⟩,[0,0,r577,r142,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨0,2,3⟩,[0,r301,r586,r587,r588,r589,r590,r591,r592,r593,r594]),(⟨0,2,4⟩,[0,0,r83,r595,r596,r597,r598,r599,r600,r601]),(⟨0,2,5⟩,[0,r204,r204,r602,r603,r604,r605,r606,r607]),(⟨0,2,6⟩,[0,r23,r608,r180,r609,r610,r611,r612]),(⟨0,3,0⟩,[0,0,r301,r456,r495,r496,r497,r498,r499,r500,r501,r502,r503]),(⟨0,3,1⟩,[0,0,r547,r548,r337,r189,r549,r550,r551,r552,r553,r554]),(⟨0,3,2⟩,[0,r301,r586,r587,r588,r589,r590,r591,r592,r593,r594]),(⟨0,3,3⟩,[0,r365,r613,r614,r615,r616,r617,r618,r202,r619]),(⟨0,3,4⟩,[0,r365,r620,r621,r622,r623,r624,r625,r626]),(⟨0,3,5⟩,[0,0,r620,r627,r628,r629,r630,r631]),(⟨0,3,6⟩,[0,r23,r632,r151,r633,r634,r635]),(⟨0,4,0⟩,[0,0,r504,r505,r506,r507,r508,r509,r510,r511,r512,r513]),(⟨0,4,1⟩,[0,r72,r555,r515,r556,r557,r558,r559,r560,r561,r562]),(⟨0,4,2⟩,[0,0,r83,r595,r596,r597,r598,r599,r600,r601]),(⟨0,4,3⟩,[0,r365,r620,r621,r622,r623,r624,r625,r626]),(⟨0,4,4⟩,[0,r636,r267,r637,r638,r639,r640,r641]),(⟨0,4,5⟩,[0,r365,r642,r267,r643,r644,r645]),(⟨0,4,6⟩,[0,0,r353,r646,r356,r647]),(⟨0,5,0⟩,[0,0,r365,r514,r515,r516,r517,r518,r519,r520,r368]),(⟨0,5,1⟩,[0,r204,r530,r563,r564,r565,r566,r567,r568,r569]),(⟨0,5,2⟩,[0,r204,r204,r602,r603,r604,r605,r606,r607]),(⟨0,5,3⟩,[0,0,r620,r627,r628,r629,r630,r631]),(⟨0,5,4⟩,[0,r365,r642,r267,r643,r644,r645]),(⟨0,5,5⟩,[0,0,r275,r648,r278,r649]),(⟨0,6,0⟩,[0,0,r365,r521,r522,r456,r523,r524,r525,r526]),(⟨0,6,1⟩,[0,r204,r570,r571,r572,r573,r574,r575,r576]),(⟨0,6,2⟩,[0,r23,r608,r180,r609,r610,r611,r612]),(⟨0,6,3⟩,[0,r23,r632,r151,r633,r634,r635]),(⟨0,6,4⟩,[0,0,r353,r646,r356,r647]),(⟨1,0,2⟩,[0,r650,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661]),(⟨1,0,3⟩,[0,r662,r228,r663,r516,r664,r498,r665,r666,r667,r668,r669]),(⟨1,0,4⟩,[0,r83,r353,r670,r671,r394,r672,r673,r674,r675,r676]),(⟨1,0,5⟩,[0,r23,r677,r678,r679,r680,r681,r682,r683,r684]),(⟨1,0,6⟩,[0,r204,r685,r686,r687,r688,r689,r690,r691]),(⟨1,1,1⟩,[0,r72,r487,r692,r693,r694,r695,r696,r697,r698,r699,r700,r701]),(⟨1,1,2⟩,[0,r702,r530,r703,r704,r536,r541,r705,r706,r707,r708,r709]),(⟨1,1,3⟩,[0,r301,r547,r353,r609,r710,r711,r712,r713,r714,r715]),(⟨1,1,4⟩,[0,r547,r716,r717,r718,r719,r720,r721,r722,r723]),(⟨1,1,5⟩,[r72,r724,r725,r726,r727,r728,r729,r730,r731]),(⟨1,1,6⟩,[0,r23,r142,r514,r732,r733,r734,r735]),(⟨1,2,0⟩,[0,r650,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661]),(⟨1,2,1⟩,[0,r702,r530,r703,r704,r536,r541,r705,r706,r707,r708,r709]),(⟨1,2,2⟩,[0,r204,r736,r737,r738,r739,r740,r741,r742,r743,r744]),(⟨1,2,3⟩,[0,r504,r142,r745,r746,r747,r748,r749,r750,r751]),(⟨1,2,4⟩,[0,r365,r521,r752,r753,r754,r755,r756,r757]),(⟨1,2,5⟩,[0,r456,r758,r759,r760,r761,r762,r763]),(⟨1,2,6⟩,[0,r23,r764,r765,r766,r767,r768]),(⟨1,3,0⟩,[0,r662,r228,r663,r516,r664,r498,r665,r666,r667,r668,r669]),(⟨1,3,1⟩,[0,r301,r547,r353,r609,r710,r711,r712,r713,r714,r715]),(⟨1,3,2⟩,[0,r504,r142,r745,r746,r747,r748,r749,r750,r751]),(⟨1,3,3⟩,[r204,r205,r769,r376,r770,r771,r772,r773,r774]),(⟨1,3,4⟩,[0,r577,r775,r776,r777,r778,r779,r780]),(⟨1,3,5⟩,[0,r365,r642,r781,r672,r295,r782]),(⟨1,4,0⟩,[0,r83,r353,r670,r671,r394,r672,r673,r674,r675,r676]),(⟨1,4,1⟩,[0,r547,r716,r717,r718,r719,r720,r721,r722,r723]),(⟨1,4,2⟩,[0,r365,r521,r752,r753,r754,r755,r756,r757]),(⟨1,4,3⟩,[0,r577,r775,r776,r777,r778,r779,r780]),(⟨1,4,4⟩,[0,0,r613,r783,r784,r785,r786]),(⟨1,5,0⟩,[0,r23,r677,r678,r679,r680,r681,r682,r683,r684]),(⟨1,5,1⟩,[r72,r724,r725,r726,r727,r728,r729,r730,r731]),(⟨1,5,2⟩,[0,r456,r758,r759,r760,r761,r762,r763]),(⟨1,5,3⟩,[0,r365,r642,r781,r672,r295,r782]),(⟨1,6,0⟩,[0,r204,r685,r686,r687,r688,r689,r690,r691]),(⟨1,6,1⟩,[0,r23,r142,r514,r732,r733,r734,r735]),(⟨1,6,2⟩,[0,r23,r764,r765,r766,r767,r768]),(⟨2,0,2⟩,[0,0,r650,r787,r788,r789,r790,r791,r792,r793,r794,r795,r796,r797]),(⟨2,0,3⟩,[r650,r798,r799,r725,r800,r801,r802,r803,r804,r805,r806,r545,r546]),(⟨2,0,4⟩,[0,r72,r487,r807,r578,r808,r809,r810,r811,r812,r813,r814]),(⟨2,0,5⟩,[r72,r408,r815,0,r816,r817,r818,r819,r820,r821,r822]),(⟨2,0,6⟩,[0,0,r23,r823,r824,r141,r825,r826,r827,r828]),(⟨2,1,1⟩,[0,0,r72,r829,r555,r830,r831,r832,r833,r834,r835,r836,r664,r837]),(⟨2,1,2⟩,[r483,r829,r838,r839,r840,r841,r842,r843,r844,r845,r846,r502,r503]),(⟨2,1,3⟩,[0,r204,r847,r848,r849,r182,r850,r851,r852,r853,r854,r855]),(⟨2,1,4⟩,[0,r301,r856,r857,r858,r859,r860,r861,r862,r863,r864]),(⟨2,1,5⟩,[0,r179,r865,r866,r867,r868,r869,r870,r871,r872]),(⟨2,1,6⟩,[0,r83,r873,r874,r875,r876,r877,r878,r879]),(⟨2,2,0⟩,[0,0,r650,r787,r788,r789,r790,r791,r792,r793,r794,r795,r796,r797]),(⟨2,2,1⟩,[r483,r829,r838,r839,r840,r841,r842,r843,r844,r845,r846,r502,r503]),(⟨2,2,2⟩,[0,r83,r358,r880,r881,r882,r883,r884,r885,r886,r887,r888]),(⟨2,2,3⟩,[r301,r889,r303,r890,r891,r892,r739,r893,r894,r895,r896]),(⟨2,2,4⟩,[0,r23,r897,r898,r899,r900,r901,r902,r903,r904]),(⟨2,2,5⟩,[0,r83,r83,r905,r906,r590,r907,r908,r909]),(⟨2,2,6⟩,[0,r365,r213,r189,r457,r910,r911,r912]),(⟨2,3,0⟩,[r650,r798,r799,r725,r800,r801,r802,r803,r804,r805,r806,r545,r546]),(⟨2,3,1⟩,[0,r204,r847,r848,r849,r182,r850,r851,r852,r853,r854,r855]),(⟨2,3,2⟩,[r301,r889,r303,r890,r891,r892,r739,r893,r894,r895,r896]),(⟨2,3,3⟩,[0,r23,r275,r75,r913,r914,r915,r916,r917,r918]),(⟨2,3,4⟩,[0,r23,r919,r775,r920,r921,r922,r923,r924]),(⟨2,3,5⟩,[0,0,r919,r925,r926,r927,r928,r929]),(⟨2,3,6⟩,[0,r365,r642,r267,r643,r644,r645]),(⟨2,4,0⟩,[0,r72,r487,r807,r578,r808,r809,r810,r811,r812,r813,r814]),(⟨2,4,1⟩,[0,r301,r856,r857,r858,r859,r860,r861,r862,r863,r864]),(⟨2,4,2⟩,[0,r23,r897,r898,r899,r900,r901,r902,r903,r904]),(⟨2,4,3⟩,[0,r23,r919,r775,r920,r921,r922,r923,r924]),(⟨2,4,4⟩,[0,r577,r151,r930,r931,r932,r933,r934]),(⟨2,4,5⟩,[0,r23,r632,r151,r633,r634,r635]),(⟨2,4,6⟩,[0,0,r205,r935,r759,r936]),(⟨2,5,0⟩,[r72,r408,r815,0,r816,r817,r818,r819,r820,r821,r822]),(⟨2,5,1⟩,[0,r179,r865,r866,r867,r868,r869,r870,r871,r872]),(⟨2,5,2⟩,[0,r83,r83,r905,r906,r590,r907,r908,r909]),(⟨2,5,3⟩,[0,0,r919,r925,r926,r927,r928,r929]),(⟨2,5,4⟩,[0,r23,r632,r151,r633,r634,r635]),(⟨2,5,5⟩,[0,0,r613,r937,r938,r939]),(⟨2,6,0⟩,[0,0,r23,r823,r824,r141,r825,r826,r827,r828]),(⟨2,6,1⟩,[0,r83,r873,r874,r875,r876,r877,r878,r879]),(⟨2,6,2⟩,[0,r365,r213,r189,r457,r910,r911,r912]),(⟨2,6,3⟩,[0,r365,r642,r267,r643,r644,r645]),(⟨2,6,4⟩,[0,0,r205,r935,r759,r936]),(⟨3,0,2⟩,[0,r483,r484,r940,r941,r942,r943,r944,r945,r946,r947,r948,r949]),(⟨3,0,3⟩,[0,r941,r950,r951,r952,r953,r954,r955,r956,r957,r708,r709]),(⟨3,0,4⟩,[0,r204,r823,r958,r910,r959,r960,r961,r962,r963,r964]),(⟨3,0,5⟩,[0,r636,r965,r966,r967,r968,r969,r970,r971,r972]),(⟨3,0,6⟩,[0,r83,r973,r677,r974,r975,r976,r977,r978]),(⟨3,1,1⟩,[0,r301,r527,r979,r61,r980,r981,r982,r983,r984,r985,r986,r987]),(⟨3,1,2⟩,[0,r653,r988,r989,r990,r991,r992,r993,r994,r995,r668,r669]),(⟨3,1,3⟩,[0,r72,r996,r205,r457,r997,r998,r999,r1000,r1001,r1002]),(⟨3,1,4⟩,[0,r1003,r1004,r1005,r1006,r1007,r1008,r1009,r1010,r1011]),(⟨3,1,5⟩,[r504,r1012,r1013,r1014,r1015,r1016,r1017,r1018,r1019]),(⟨3,1,6⟩,[0,r365,r358,r1020,r163,r1021,r1022,r1023]),(⟨3,2,0⟩,[0,r483,r484,r940,r941,r942,r943,r944,r945,r946,r947,r948,r949]),(⟨3,2,1⟩,[0,r653,r988,r989,r990,r991,r992,r993,r994,r995,r668,r669]),(⟨3,2,2⟩,[0,r83,r1024,r1025,r1026,r1027,r1028,r1029,r1030,r1031,r1032]),(⟨3,2,3⟩,[0,r798,r435,r1033,r1034,r1035,r1036,r1037,r1038,r1039]),(⟨3,2,4⟩,[0,r23,r823,r1040,r1041,r1042,r1043,r1044,r1045]),(⟨3,2,5⟩,[0,r620,r1046,r1047,r1048,r1049,r1050,r1051]),(⟨3,2,6⟩,[0,r365,r1052,r1053,r1054,r1055,r1056]),(⟨3,3,0⟩,[0,r941,r950,r951,r952,r953,r954,r955,r956,r957,r708,r709]),(⟨3,3,1⟩,[0,r72,r996,r205,r457,r997,r998,r999,r1000,r1001,r1002]),(⟨3,3,2⟩,[0,r798,r435,r1033,r1034,r1035,r1036,r1037,r1038,r1039]),(⟨3,3,3⟩,[r179,r1057,r1058,r1059,r1060,r1061,r1062,r1063,r1064]),(⟨3,3,4⟩,[0,r151,r506,r1065,r1066,r1067,r1068,r1069]),(⟨3,3,5⟩,[0,r23,r632,r1070,r1071,r1072,r1073]),(⟨3,4,0⟩,[0,r204,r823,r958,r910,r959,r960,r961,r962,r963,r964]),(⟨3,4,1⟩,[0,r1003,r1004,r1005,r1006,r1007,r1008,r1009,r1010,r1011]),(⟨3,4,2⟩,[0,r23,r823,r1040,r1041,r1042,r1043,r1044,r1045]),(⟨3,4,3⟩,[0,r151,r506,r1065,r1066,r1067,r1068,r1069]),(⟨3,4,4⟩,[0,0,r275,r1074,r1075,r1076,r1077]),(⟨3,5,0⟩,[0,r636,r965,r966,r967,r968,r969,r970,r971,r972]),(⟨3,5,1⟩,[r504,r1012,r1013,r1014,r1015,r1016,r1017,r1018,r1019]),(⟨3,5,2⟩,[0,r620,r1046,r1047,r1048,r1049,r1050,r1051]),(⟨3,5,3⟩,[0,r23,r632,r1070,r1071,r1072,r1073]),(⟨3,6,0⟩,[0,r83,r973,r677,r974,r975,r976,r977,r978]),(⟨3,6,1⟩,[0,r365,r358,r1020,r163,r1021,r1022,r1023]),(⟨3,6,2⟩,[0,r365,r1052,r1053,r1054,r1055,r1056]),(⟨4,0,2⟩,[0,0,0,r83,r521,r1078,r1079,r1080,r1081,r1082,r1083,768]),(⟨4,0,3⟩,[r662,r1084,r1085,r1086,r953,r1087,r1088,r1089,r1090,r1091,-2624]),(⟨4,0,4⟩,[0,r504,r823,r457,r456,r1092,r1093,r1094,r1095,896]),(⟨4,0,5⟩,[r504,r823,r824,r1052,r1096,r1097,r1098,r1099,1408]),(⟨4,1,1⟩,[0,0,0,r23,r1100,r732,r1101,r819,r1102,r1103,r1104,-1536]),(⟨4,1,2⟩,[r702,r1105,r1106,r1107,r991,r1108,r1109,r1110,r1111,r1112,2624]),(⟨4,1,3⟩,[0,r83,r521,r1113,r1114,r1115,r1116,r1117,r1118,1280]),(⟨4,1,4⟩,[0,0,r23,r226,r1119,r783,r1120,r1121,-512]),(⟨4,1,5⟩,[0,r23,r226,r1119,r783,r1120,r1121,-512]),(⟨4,2,0⟩,[0,0,0,r83,r521,r1078,r1079,r1080,r1081,r1082,r1083,768]),(⟨4,2,1⟩,[r702,r1105,r1106,r1107,r991,r1108,r1109,r1110,r1111,r1112,2624]),(⟨4,2,2⟩,[0,r83,0,r737,r1122,r1123,r1124,r1125,r1126,-4352]),(⟨4,2,3⟩,[r1127,r521,r609,r141,r1128,r1129,r1130,r1131,-896]),(⟨4,2,4⟩,[0,r365,r1132,r1133,r1074,r1134,r1135,512]),(⟨4,3,0⟩,[r662,r1084,r1085,r1086,r953,r1087,r1088,r1089,r1090,r1091,-2624]),(⟨4,3,1⟩,[0,r83,r521,r1113,r1114,r1115,r1116,r1117,r1118,1280]),(⟨4,3,2⟩,[r1127,r521,r609,r141,r1128,r1129,r1130,r1131,-896]),(⟨4,4,0⟩,[0,r504,r823,r457,r456,r1092,r1093,r1094,r1095,896]),(⟨4,4,1⟩,[0,0,r23,r226,r1119,r783,r1120,r1121,-512]),(⟨4,4,2⟩,[0,r365,r1132,r1133,r1074,r1134,r1135,512]),(⟨4,5,0⟩,[r504,r823,r824,r1052,r1096,r1097,r1098,r1099,1408]),(⟨4,5,1⟩,[0,r23,r226,r1119,r783,r1120,r1121,-512]),(⟨5,0,3⟩,[0,r72,r408,r1136,r1137,r1138,r213,r1139,r1140,r1141]),(⟨5,0,4⟩,[0,0,r141,r370,r1142,r1143,r1144,r1145,r1146]),(⟨5,0,5⟩,[0,r23,r1054,r1147,r1148,r1149,r1150,r1151]),(⟨5,1,2⟩,[0,r301,r13,r1152,r515,r1153,r608,r1154,r1155,r1156]),(⟨5,1,4⟩,[0,r1157,r1158,r1159,r1160,r1161,r1162,768]),(⟨5,1,5⟩,[r83,r620,r1163,r1164,r564,r1165,r1166]),(⟨5,2,1⟩,[0,r301,r13,r1152,r515,r1153,r608,r1154,r1155,r1156]),(⟨5,2,2⟩,[0,0,r151,r1167,r1168,r1169,r676,r1170,r374]),(⟨5,2,3⟩,[0,r109,r1171,r1172,r1173,r1174,r1175,r1176]),(⟨5,2,5⟩,[0,r13,r587,r646,r1177,r1178]),(⟨5,3,0⟩,[0,r72,r408,r1136,r1137,r1138,r213,r1139,r1140,r1141]),(⟨5,3,2⟩,[0,r109,r1171,r1172,r1173,r1174,r1175,r1176]),(⟨5,3,3⟩,[r23,r1054,r752,r1179,r1180,r1181,r1182]),(⟨5,3,4⟩,[0,r408,r1183,r935,r1184,r1185]),(⟨5,4,0⟩,[0,0,r141,r370,r1142,r1143,r1144,r1145,r1146]),(⟨5,4,1⟩,[0,r1157,r1158,r1159,r1160,r1161,r1162,768]),(⟨5,4,3⟩,[0,r408,r1183,r935,r1184,r1185]),(⟨5,5,0⟩,[0,r23,r1054,r1147,r1148,r1149,r1150,r1151]),(⟨5,5,1⟩,[r83,r620,r1163,r1164,r564,r1165,r1166]),(⟨5,5,2⟩,[0,r13,r587,r646,r1177,r1178]),(⟨6,0,3⟩,[r301,r13,r250,r1186,r1187,r816,r1188,r1189,384]),(⟨6,0,4⟩,[0,r83,r620,r595,r1190,r1191,r620,-256]),(⟨6,0,5⟩,[r83,r620,r595,r1190,r1191,r620,-256]),(⟨6,1,2⟩,[r72,r408,r897,r1192,r958,r1193,r1194,r1195,-384]),(⟨6,2,1⟩,[r72,r408,r897,r1192,r958,r1193,r1194,r1195,-384]),(⟨6,2,2⟩,[0,r23,r1054,r769,r1196,r1197,r1054,512]),(⟨6,2,3⟩,[r204,r919,r1198,r470,r1199,r919,256]),(⟨6,3,0⟩,[r301,r13,r250,r1186,r1187,r816,r1188,r1189,384]),(⟨6,3,2⟩,[r204,r919,r1198,r470,r1199,r919,256]),(⟨6,4,0⟩,[0,r83,r620,r595,r1190,r1191,r620,-256]),(⟨6,5,0⟩,[r83,r620,r595,r1190,r1191,r620,-256])]


noncomputable def sourceLeft : Poly := [(⟨0,0,1⟩,[0,-1,4,-12,16,-39]),(⟨0,0,2⟩,[0,0,12,-24,12]),(⟨0,0,3⟩,[0,4,-8,20]),(⟨0,1,0⟩,[0,1,-4,12,-16,39]),(⟨0,1,2⟩,[0,-10,20,-42]),(⟨0,1,3⟩,[-2,4,-18]),(⟨0,2,0⟩,[0,0,-12,24,-12]),(⟨0,2,1⟩,[0,10,-20,42]),(⟨0,2,3⟩,[0,-16]),(⟨0,3,0⟩,[0,-4,8,-20]),(⟨0,3,1⟩,[2,-4,18]),(⟨0,3,2⟩,[0,16]),(⟨1,0,1⟩,[1,-4,0,8,-21]),(⟨1,0,2⟩,[0,-2,4,14]),(⟨1,0,3⟩,[-2,4,14]),(⟨1,1,0⟩,[-1,4,0,-8,21]),(⟨1,2,0⟩,[0,2,-4,-14]),(⟨1,3,0⟩,[2,-4,-14])]
noncomputable def sourceRight : Poly := [(⟨0,0,1⟩,[0,64,-576,1088,3776,-11328,4672,960,1344]),(⟨0,0,2⟩,[0,-128,1792,-7808,5632,26240,-46336,20608]),(⟨0,0,3⟩,[0,-128,1152,-2560,-11264,40576,-27776]),(⟨0,1,0⟩,[0,-64,576,-1088,-3776,11328,-4672,-960,-1344]),(⟨0,1,2⟩,[0,-128,1920,-4608,-1536,16000,-11648]),(⟨0,1,3⟩,[0,-256,2560,0,-27136,41216]),(⟨0,2,0⟩,[0,128,-1792,7808,-5632,-26240,46336,-20608]),(⟨0,2,1⟩,[0,128,-1920,4608,1536,-16000,11648]),(⟨0,2,3⟩,[0,-256,3840,-8960,5376]),(⟨0,3,0⟩,[0,128,-1152,2560,11264,-40576,27776]),(⟨0,3,1⟩,[0,256,-2560,0,27136,-41216]),(⟨0,3,2⟩,[0,256,-3840,8960,-5376]),(⟨1,0,1⟩,[0,0,0,256,-4608,26624,-52736,30464]),(⟨1,0,2⟩,[64,-896,3648,-2304,-25408,84096,-83776]),(⟨1,1,0⟩,[0,0,0,-256,4608,-26624,52736,-30464]),(⟨1,1,2⟩,[0,256,-4608,26624,-52736,30464]),(⟨1,2,0⟩,[-64,896,-3648,2304,25408,-84096,83776]),(⟨1,2,1⟩,[0,-256,4608,-26624,52736,-30464]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[128,-1536,3840,4608,-15232])]

theorem left_checked :
    (Poly.add (Data.S7_odd.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r1200) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S7_odd.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r1201) sourceRight))).isZero := by decide +kernel

noncomputable def partial18 : Poly := []

theorem partial_sound18 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 18)
      sourceRight).eval u v t=partial18.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨1,2,0⟩,[0,2,-4,-14]),(⟨1,3,0⟩,[2,-4,-14])]

noncomputable def partial16 : Poly := [(⟨1,2,1⟩,[0,0,128,-1408,3584,11264,-52992,1792,141824,-66560,-18816,-18816]),(⟨1,2,2⟩,[0,0,-256,4096,-20992,17408,139264,-276480,-140800,566272,-288512]),(⟨1,2,3⟩,[0,0,-256,2816,-7936,-28416,162048,-60160,-456960,388864]),(⟨1,3,0⟩,[0,0,-128,1408,-3584,-11264,52992,-1792,-141824,66560,18816,18816]),(⟨1,3,1⟩,[0,128,-1408,3584,11264,-52992,1792,141824,-66560,-18816,-18816]),(⟨1,3,2⟩,[0,-256,3840,-16640,2304,127744,-173824,-206592,388864,-125440]),(⟨1,3,3⟩,[0,-256,2304,-1792,-35072,71936,130816,-241920,-188160]),(⟨1,4,0⟩,[0,-128,1664,-7680,9728,35584,-141056,134656,207360,-547456,307328]),(⟨1,4,1⟩,[0,0,256,-4352,15104,11520,-102656,65792,177408,-163072]),(⟨1,4,2⟩,[0,-256,4352,-15104,-11520,102656,-65792,-177408,163072]),(⟨1,4,3⟩,[0,-512,5632,2048,-119808,183808,318976,-652288]),(⟨1,5,0⟩,[0,256,-3840,18176,-9472,-110848,114432,200960,-109312,-100352]),(⟨1,5,1⟩,[0,256,-3840,8960,18176,-12544,-125184,-37632,413952]),(⟨1,5,2⟩,[0,0,512,-8704,29696,7168,-103936,75264]),(⟨1,5,3⟩,[0,-512,8704,-29696,-7168,103936,-75264]),(⟨1,6,0⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,6,1⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,6,2⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨2,2,1⟩,[0,0,0,0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,2,2⟩,[0,128,-2048,9984,-6656,-92672,302080,-148224,-842240,1172864]),(⟨2,3,0⟩,[0,0,0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,3,1⟩,[0,0,0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,3,2⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,4,0⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,4,1⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,4,2⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,5,0⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,5,1⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨4,2,2⟩,[0,-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,3,2⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,4,0⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,5,0⟩,[256,-3584,12032,15360,-102656,-3584,213248])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial18)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 18))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound18 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,1⟩,[1,-4,0,8,-21]),(⟨1,0,2⟩,[0,-2,4,14]),(⟨1,0,3⟩,[-2,4,14]),(⟨1,1,0⟩,[-1,4,0,-8,21])]

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[0,64,-832,3392,-64,-32384,70784,-10368,-172416,269888,-90432,-9408,-28224]),(⟨1,0,3⟩,[0,-128,2176,-13568,32256,9472,-198400,413184,-132608,-855168,1156736,-413952]),(⟨1,0,4⟩,[0,-256,3328,-14848,7680,133120,-375808,209408,768512,-1621760,890624]),(⟨1,0,5⟩,[0,256,-3840,18176,-9472,-110848,114432,200960,-109312,-100352]),(⟨1,0,6⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,1,1⟩,[0,-128,1664,-6784,128,64768,-141568,20736,344832,-539776,180864,18816,56448]),(⟨1,1,2⟩,[0,128,-2176,13568,-32256,-9472,198400,-413184,132608,855168,-1156736,413952]),(⟨1,1,3⟩,[0,128,-640,-1536,29184,-110336,83712,198144,-467456,626304,-357504]),(⟨1,1,4⟩,[0,-256,3840,-14592,-14080,187136,-321280,-151296,1076992,-1028608]),(⟨1,1,5⟩,[0,256,-3840,8960,18176,-12544,-125184,-37632,413952]),(⟨1,1,6⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,2,0⟩,[0,64,-832,3392,-64,-32384,70784,-10368,-172416,269888,-90432,-9408,-28224]),(⟨1,2,1⟩,[0,128,-2176,13568,-32256,-9472,198400,-413184,132608,855168,-1156736,413952]),(⟨1,2,2⟩,[0,256,-5376,32768,-73728,-45568,584192,-815104,-602112,1990912,-1066240]),(⟨1,2,3⟩,[0,0,0,-3584,23552,-76288,206848,-49664,-967680,1128960]),(⟨1,2,4⟩,[0,-512,9216,-39424,27648,117248,-218112,53760,50176]),(⟨1,2,5⟩,[0,0,512,-8704,29696,7168,-103936,75264]),(⟨1,2,6⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨1,3,0⟩,[0,-128,2176,-13568,32256,9472,-198400,413184,-132608,-855168,1156736,-413952]),(⟨1,3,1⟩,[0,128,-640,-1536,29184,-110336,83712,198144,-467456,626304,-357504]),(⟨1,3,2⟩,[0,0,0,-3584,23552,-76288,206848,-49664,-967680,1128960]),(⟨1,3,3⟩,[0,0,-5120,45056,-148480,114688,566272,-946176,-150528]),(⟨1,3,4⟩,[0,-512,5632,2048,-119808,183808,318976,-652288]),(⟨1,3,5⟩,[0,-512,8704,-29696,-7168,103936,-75264]),(⟨1,4,0⟩,[0,-256,3328,-14848,7680,133120,-375808,209408,768512,-1621760,890624]),(⟨1,4,1⟩,[0,-256,3840,-14592,-14080,187136,-321280,-151296,1076992,-1028608]),(⟨1,4,2⟩,[0,-512,9216,-39424,27648,117248,-218112,53760,50176]),(⟨1,4,3⟩,[0,-512,5632,2048,-119808,183808,318976,-652288]),(⟨1,5,0⟩,[0,256,-3840,18176,-9472,-110848,114432,200960,-109312,-100352]),(⟨1,5,1⟩,[0,256,-3840,8960,18176,-12544,-125184,-37632,413952]),(⟨1,5,2⟩,[0,0,512,-8704,29696,7168,-103936,75264]),(⟨1,5,3⟩,[0,-512,8704,-29696,-7168,103936,-75264]),(⟨1,6,0⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,6,1⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,6,2⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨2,0,2⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,0,3⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,0,4⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,0,5⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,1,1⟩,[0,0,0,-512,11264,-90112,314368,-398336,-375808,1961984,-2702336,1279488]),(⟨2,1,2⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,1,3⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,1,4⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,1,5⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,2,0⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,2,1⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,2,2⟩,[0,-256,7168,-70144,301056,-583680,228352,1665536,-4386816,3625216]),(⟨2,2,3⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,2,4⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,3,0⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,3,1⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,3,2⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,4,0⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,4,1⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,4,2⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,5,0⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,5,1⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨4,0,3⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,0,4⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,0,5⟩,[256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,1,2⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,1⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,2⟩,[0,-512,7168,-24064,-30720,205312,7168,-426496]),(⟨4,2,3⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,3,0⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,3,2⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,4,0⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,5,0⟩,[256,-3584,12032,15360,-102656,-3584,213248])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,2,3⟩,[0,-16]),(⟨0,3,0⟩,[0,-4,8,-20]),(⟨0,3,1⟩,[2,-4,18]),(⟨0,3,2⟩,[0,16])]

noncomputable def partial8 : Poly := [(⟨0,2,4⟩,[0,0,-1024,9216,-17408,-60416,181248,-74752,-15360,-21504]),(⟨0,2,5⟩,[0,0,2048,-28672,124928,-90112,-419840,741376,-329728]),(⟨0,2,6⟩,[0,0,2048,-18432,40960,180224,-649216,444416]),(⟨0,3,1⟩,[0,0,-256,2816,-10240,5120,53760,-184832,260096,-91136,-8448,-26880]),(⟨0,3,2⟩,[0,128,-896,-2560,40960,-139008,218880,61952,-894976,1103488,-387968]),(⟨0,3,3⟩,[0,-256,6656,-49152,131584,11776,-659968,1509376,-1919488,969472]),(⟨0,3,4⟩,[0,-256,768,16640,-116480,170240,-768,100096,-170240]),(⟨0,3,5⟩,[0,0,0,-12288,32768,-155648,393216,-258048]),(⟨0,3,6⟩,[0,0,4096,-40960,0,434176,-659456]),(⟨0,4,0⟩,[0,0,256,-2816,10240,-5120,-53760,184832,-260096,91136,8448,26880]),(⟨0,4,1⟩,[0,-128,1408,-5632,7168,18176,-122624,220672,-82944,-11904,-24192]),(⟨0,4,2⟩,[0,0,-512,512,18944,-129536,197120,130560,-428544,211456]),(⟨0,4,3⟩,[0,-256,3328,-2816,-49408,102656,-77056,465664,-704256]),(⟨0,4,4⟩,[0,-512,2048,46592,-155648,141824,-141312,369152]),(⟨0,4,5⟩,[0,0,-4096,40960,0,-434176,659456]),(⟨0,4,6⟩,[0,0,4096,-61440,143360,-86016]),(⟨0,5,0⟩,[0,0,-512,8192,-48128,120832,-96256,-282624,977920,-1091584,412160]),(⟨0,5,1⟩,[0,256,-4608,33792,-111104,179712,80384,-904192,1329664,-603904]),(⟨0,5,2⟩,[0,256,-2304,-9472,75008,-45312,-304896,406784,-120064]),(⟨0,5,3⟩,[0,0,1024,-29696,104448,-325632,615424,-365568]),(⟨0,5,4⟩,[0,-512,4608,3072,115712,-616960,756224]),(⟨0,5,5⟩,[0,0,-8192,122880,-286720,172032]),(⟨0,6,0⟩,[0,0,-512,5632,-22016,-1536,201216,-660992,1033728,-555520]),(⟨0,6,1⟩,[0,256,-3840,24320,-34048,-137472,802560,-1713920,1324288]),(⟨0,6,2⟩,[0,512,-5120,13824,-22528,159232,-218112,-189952]),(⟨0,6,3⟩,[0,512,-4608,-3072,-115712,616960,-756224]),(⟨0,6,4⟩,[0,0,4096,-61440,143360,-86016]),(⟨1,0,2⟩,[0,64,-832,3392,-64,-32384,70784,-10368,-172416,269888,-90432,-9408,-28224]),(⟨1,0,3⟩,[0,-128,2176,-13568,32256,9472,-198400,413184,-132608,-855168,1156736,-413952]),(⟨1,0,4⟩,[0,-256,3328,-14848,7680,133120,-375808,209408,768512,-1621760,890624]),(⟨1,0,5⟩,[0,256,-3840,18176,-9472,-110848,114432,200960,-109312,-100352]),(⟨1,0,6⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,1,1⟩,[0,-128,1664,-6784,128,64768,-141568,20736,344832,-539776,180864,18816,56448]),(⟨1,1,2⟩,[0,128,-2176,13568,-32256,-9472,198400,-413184,132608,855168,-1156736,413952]),(⟨1,1,3⟩,[0,128,-640,-1536,29184,-110336,83712,198144,-467456,626304,-357504]),(⟨1,1,4⟩,[0,-256,3840,-14592,-14080,187136,-321280,-151296,1076992,-1028608]),(⟨1,1,5⟩,[0,256,-3840,8960,18176,-12544,-125184,-37632,413952]),(⟨1,1,6⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,2,0⟩,[0,64,-832,3392,-64,-32384,70784,-10368,-172416,269888,-90432,-9408,-28224]),(⟨1,2,1⟩,[0,128,-2176,13568,-32256,-9472,198400,-413184,132608,855168,-1156736,413952]),(⟨1,2,2⟩,[0,256,-5376,32768,-73728,-45568,584192,-815104,-602112,1990912,-1066240]),(⟨1,2,3⟩,[0,0,0,-3584,23552,-76288,206848,-49664,-967680,1128960]),(⟨1,2,4⟩,[0,-512,9216,-39424,23552,190976,-644096,897536,-437248]),(⟨1,2,5⟩,[0,-1024,14848,-67072,66560,413696,-1449472,1415680]),(⟨1,2,6⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨1,3,0⟩,[0,-128,2176,-13568,32256,9472,-198400,413184,-132608,-855168,1156736,-413952]),(⟨1,3,1⟩,[0,128,-640,-1536,28160,-89856,-64768,714240,-1543680,1924736,-966784]),(⟨1,3,2⟩,[0,-256,4096,-26112,69632,10240,-581632,2217472,-4390912,3352832]),(⟨1,3,3⟩,[128,-2048,6912,9728,-116224,195584,456960,-784896,-683648]),(⟨1,3,4⟩,[0,512,-8704,60416,-156672,-222720,1664512,-1992704]),(⟨1,3,5⟩,[0,-512,4608,44032,-433152,947712,-562688]),(⟨1,4,0⟩,[0,-256,3328,-14848,8704,112640,-227328,-306688,1844736,-2920192,1499904]),(⟨1,4,1⟩,[0,-256,3840,-15104,-3840,110848,-26368,-902400,2148096,-1576960]),(⟨1,4,2⟩,[0,-512,8192,-18944,-124928,707072,-1720320,2195968,-1046528]),(⟨1,4,3⟩,[0,1024,-18944,136704,-451584,528384,593408,-1444352]),(⟨1,4,4⟩,[0,0,8192,-147456,851968,-1687552,974848]),(⟨1,5,0⟩,[0,512,-7936,41216,-65792,-121088,608000,-1315072,2242816,-1775872]),(⟨1,5,1⟩,[-128,2304,-14848,23808,142592,-756992,1912320,-3184896,2531200]),(⟨1,5,2⟩,[0,-1536,25088,-143360,361472,-337408,-378368,867328]),(⟨1,5,3⟩,[0,-512,4608,44032,-433152,947712,-562688]),(⟨1,6,0⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,6,1⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,6,2⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨2,0,2⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,0,3⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,0,4⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,0,5⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,1,1⟩,[0,0,0,-512,11264,-90112,314368,-398336,-375808,1961984,-2702336,1279488]),(⟨2,1,2⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,1,3⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,1,4⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,1,5⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,2,0⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,2,1⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,2,2⟩,[0,-256,7168,-70144,301056,-583680,228352,1665536,-4386816,3625216]),(⟨2,2,3⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,2,4⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,3,0⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,3,1⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,3,2⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,4,0⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,4,1⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,4,2⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,5,0⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,5,1⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨3,2,5⟩,[0,2048,-24576,61440,73728,-243712]),(⟨3,3,2⟩,[0,512,-7168,30208,-43008,-20992,214016,-304640]),(⟨3,3,3⟩,[-256,3584,-16128,33792,-20224,-143872,274176]),(⟨3,3,4⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨3,4,3⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨3,5,0⟩,[0,-512,7168,-30208,43008,20992,-214016,304640]),(⟨3,5,1⟩,[256,-3584,16128,-33792,20224,143872,-274176]),(⟨3,5,2⟩,[0,2048,-24576,61440,73728,-243712]),(⟨4,0,3⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,0,4⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,0,5⟩,[256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,1,2⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,1⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,2⟩,[0,-512,7168,-24064,-30720,205312,7168,-426496]),(⟨4,2,3⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,3,0⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,3,2⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,4,0⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,5,0⟩,[256,-3584,12032,15360,-102656,-3584,213248])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,2⟩,[0,-10,20,-42]),(⟨0,1,3⟩,[-2,4,-18]),(⟨0,2,0⟩,[0,0,-12,24,-12]),(⟨0,2,1⟩,[0,10,-20,42])]

noncomputable def partial4 : Poly := [(⟨0,1,3⟩,[0,0,-640,7040,-25088,8192,143104,-431872,559616,-190464,-13440,-56448]),(⟨0,1,4⟩,[0,-128,2688,-26112,126464,-269568,55552,972288,-2317824,2346368,-889728]),(⟨0,1,5⟩,[0,256,-2816,11008,-20736,123648,-427264,863488,-1343232,795648]),(⟨0,1,6⟩,[0,256,-2816,12032,-8448,-80128,420608,-841472,499968]),(⟨0,2,1⟩,[0,0,0,-768,8448,-27648,-12288,213504,-373248,236544,-49152,20736,-16128]),(⟨0,2,2⟩,[0,0,1280,-12544,25600,121856,-562688,777728,-1024,-1293312,1077504,-134400]),(⟨0,2,3⟩,[0,128,-2688,27648,-143360,329472,4352,-1698816,3760128,-3499904,1223040]),(⟨0,2,4⟩,[0,0,-1024,1536,18432,-230912,707584,-1136128,1339392,-698880]),(⟨0,2,5⟩,[0,256,256,-40192,136960,118528,-1259776,2370816,-1851136]),(⟨0,2,6⟩,[0,512,-4096,-3584,49152,-10752,4096,-297472]),(⟨0,3,0⟩,[0,0,0,768,-8448,27648,12288,-213504,373248,-236544,49152,-20736,16128]),(⟨0,3,1⟩,[0,0,-896,9856,-35328,13312,196864,-616704,819712,-281600,-21888,-83328]),(⟨0,3,2⟩,[0,128,-2176,19456,-104448,251648,-74496,-863232,1882112,-1726336,617344]),(⟨0,3,3⟩,[0,-512,8192,-27648,-10240,280576,-466944,60416,288768,-132608]),(⟨0,3,4⟩,[0,-512,2560,28160,-128512,-38400,839168,-1529344,1351168]),(⟨0,3,5⟩,[0,0,2560,-55808,209920,-549888,877056,-483840]),(⟨0,3,6⟩,[0,512,-4608,-3072,-115712,616960,-756224]),(⟨0,4,0⟩,[0,0,256,-4352,34816,-143360,222720,270848,-1378304,1765376,-1042176,274176]),(⟨0,4,1⟩,[0,-128,2688,-27648,152576,-372480,170752,1145856,-2860032,2817920,-1029504]),(⟨0,4,2⟩,[0,0,-512,-7168,54784,-300032,723456,-930816,926208,-465920]),(⟨0,4,3⟩,[0,-512,3584,18944,-155136,221696,131584,-420352,462336]),(⟨0,4,4⟩,[0,-1024,3072,118784,-518144,1121280,-1762304,1562624]),(⟨0,4,5⟩,[0,-512,4608,3072,115712,-616960,756224]),(⟨0,4,6⟩,[0,0,4096,-61440,143360,-86016]),(⟨0,5,0⟩,[0,0,-512,6656,-31232,60928,-156160,443904,-464384,61952,78848]),(⟨0,5,1⟩,[0,256,-3328,16640,-20224,128256,-738048,1804032,-2244864,1057280]),(⟨0,5,2⟩,[0,256,256,-43264,189184,-84224,-934144,2134272,-1786624]),(⟨0,5,3⟩,[0,0,3584,-73216,281600,-719872,1099264,-591360]),(⟨0,5,4⟩,[0,-512,4608,3072,115712,-616960,756224]),(⟨0,5,5⟩,[0,0,-8192,122880,-286720,172032]),(⟨0,6,0⟩,[0,0,-512,5632,-22016,-1536,201216,-660992,1033728,-555520]),(⟨0,6,1⟩,[0,256,-3840,24320,-34048,-137472,802560,-1713920,1324288]),(⟨0,6,2⟩,[0,512,-5120,13824,-22528,159232,-218112,-189952]),(⟨0,6,3⟩,[0,512,-4608,-3072,-115712,616960,-756224]),(⟨0,6,4⟩,[0,0,4096,-61440,143360,-86016]),(⟨1,0,2⟩,[0,64,-832,3392,-64,-32384,70784,-10368,-172416,269888,-90432,-9408,-28224]),(⟨1,0,3⟩,[0,-128,2176,-13568,32256,9472,-198400,413184,-132608,-855168,1156736,-413952]),(⟨1,0,4⟩,[0,-256,3328,-14848,7680,133120,-375808,209408,768512,-1621760,890624]),(⟨1,0,5⟩,[0,256,-3840,18176,-9472,-110848,114432,200960,-109312,-100352]),(⟨1,0,6⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,1,1⟩,[0,-128,1664,-6784,128,64768,-141568,20736,344832,-539776,180864,18816,56448]),(⟨1,1,2⟩,[0,128,-2176,13568,-32256,-9472,198400,-413184,132608,855168,-1156736,413952]),(⟨1,1,3⟩,[0,128,-640,-1536,26624,-59136,-285440,1451520,-2945024,3450496,-1636992]),(⟨1,1,4⟩,[0,-896,14080,-72192,129792,165632,-1278720,2684416,-3059456,1941632]),(⟨1,1,5⟩,[-128,2304,-15872,44288,-5888,-240896,836096,-1886464,1921920]),(⟨1,1,6⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,2,0⟩,[0,64,-832,3392,-64,-32384,70784,-10368,-172416,269888,-90432,-9408,-28224]),(⟨1,2,1⟩,[0,128,-2176,13568,-32256,-12544,259840,-846336,1459712,-1095552,207232,48384]),(⟨1,2,2⟩,[0,256,-6144,45056,-134656,-22016,1528320,-4913152,7681536,-6677248,2498048]),(⟨1,2,3⟩,[0,640,-10240,54016,-120320,-54784,1164288,-2885376,3168768,-1841280]),(⟨1,2,4⟩,[0,-512,6656,11776,-345600,1444352,-3121664,3721728,-1716736]),(⟨1,2,5⟩,[0,-1536,25088,-143360,361472,-337408,-378368,867328]),(⟨1,2,6⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨1,3,0⟩,[0,-128,2176,-13568,32256,12544,-259840,846336,-1459712,1095552,-207232,-48384]),(⟨1,3,1⟩,[0,128,-640,-1536,25600,-38656,-433920,1967616,-4021248,4748928,-2246272]),(⟨1,3,2⟩,[0,384,-6144,27904,-2560,-477696,1997824,-3320064,2180608,-531328]),(⟨1,3,3⟩,[256,-4096,24064,-128000,646144,-2082816,4450816,-4584448,367360]),(⟨1,3,4⟩,[0,1024,-18944,136704,-451584,528384,593408,-1444352]),(⟨1,3,5⟩,[0,-512,4608,44032,-433152,947712,-562688]),(⟨1,4,0⟩,[0,-256,4096,-27136,74752,-13312,-433152,1284608,-1483776,99584,494592]),(⟨1,4,1⟩,[0,-896,14080,-69120,68352,598784,-2605824,4635136,-4423424,2307200]),(⟨1,4,2⟩,[0,-512,5632,32256,-494080,1960448,-4197888,5020160,-2326016]),(⟨1,4,3⟩,[0,1024,-18944,136704,-451584,528384,593408,-1444352]),(⟨1,4,4⟩,[0,0,8192,-147456,851968,-1687552,974848]),(⟨1,5,0⟩,[0,512,-7936,41216,-65792,-121088,608000,-1315072,2242816,-1775872]),(⟨1,5,1⟩,[-128,2304,-14848,23808,142592,-756992,1912320,-3184896,2531200]),(⟨1,5,2⟩,[0,-1536,25088,-143360,361472,-337408,-378368,867328]),(⟨1,5,3⟩,[0,-512,4608,44032,-433152,947712,-562688]),(⟨1,6,0⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,6,1⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,6,2⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨2,0,2⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,0,3⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,0,4⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,0,5⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,1,1⟩,[0,0,0,-512,11264,-90112,314368,-398336,-375808,1961984,-2702336,1279488]),(⟨2,1,2⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,1,3⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,1,4⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,1,5⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,2,0⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,2,1⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,2,2⟩,[0,-256,7168,-70144,301056,-583680,228352,1665536,-4386816,3625216]),(⟨2,2,3⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,2,4⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,3,0⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,3,1⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,3,2⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,4,0⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,4,1⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,4,2⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,5,0⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,5,1⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨3,1,4⟩,[0,1280,-17920,74496,-95232,-83200,498176,-639744]),(⟨3,1,5⟩,[256,-3584,16128,-33792,20224,143872,-274176]),(⟨3,2,2⟩,[0,0,1536,-21504,84480,-55296,-247296,420864,-182784]),(⟨3,2,3⟩,[0,-1280,17920,-74496,95232,83200,-498176,639744]),(⟨3,2,5⟩,[0,2048,-24576,61440,73728,-243712]),(⟨3,3,2⟩,[0,-768,10752,-44288,52224,62208,-284160,335104]),(⟨3,3,3⟩,[-512,7168,-32256,67584,-40448,-287744,548352]),(⟨3,3,4⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨3,4,0⟩,[0,0,-1536,21504,-84480,55296,247296,-420864,182784]),(⟨3,4,1⟩,[0,1280,-17920,74496,-95232,-83200,498176,-639744]),(⟨3,4,3⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨3,5,0⟩,[0,-512,7168,-30208,43008,20992,-214016,304640]),(⟨3,5,1⟩,[256,-3584,16128,-33792,20224,143872,-274176]),(⟨3,5,2⟩,[0,2048,-24576,61440,73728,-243712]),(⟨4,0,3⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,0,4⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,0,5⟩,[256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,1,2⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,1⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,2⟩,[0,-512,7168,-24064,-30720,205312,7168,-426496]),(⟨4,2,3⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,3,0⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,3,2⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,4,0⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,5,0⟩,[256,-3584,12032,15360,-102656,-3584,213248])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,1⟩,[0,-1,4,-12,16,-39]),(⟨0,0,2⟩,[0,0,12,-24,12]),(⟨0,0,3⟩,[0,4,-8,20]),(⟨0,1,0⟩,[0,1,-4,12,-16,39])]

noncomputable def partial0 : Poly := [(⟨0,0,2⟩,[0,0,-64,832,-4160,8512,1664,-55424,171648,-382080,510400,-182976,-15936,-52416]),(⟨0,0,3⟩,[0,0,128,-1536,8064,-32768,135936,-324608,247040,602112,-1962880,2116096,-787584]),(⟨0,0,4⟩,[0,0,384,-6016,43520,-158208,191232,510208,-2056704,3187200,-3069056,1357440]),(⟨0,0,5⟩,[0,0,-512,6656,-31232,60928,-156160,443904,-464384,61952,78848]),(⟨0,0,6⟩,[0,0,-512,5632,-22016,-1536,201216,-660992,1033728,-555520]),(⟨0,1,1⟩,[0,0,128,-1664,8320,-17024,-3328,110848,-343296,764160,-1020800,365952,31872,104832]),(⟨0,1,2⟩,[0,0,-128,1536,-8064,32768,-135936,324608,-247040,-602112,1962880,-2116096,787584]),(⟨0,1,3⟩,[0,0,-896,9088,-30208,-13824,297216,-910592,1414656,-1247744,1194624,-712320]),(⟨0,1,4⟩,[0,-128,2944,-31232,165888,-380160,71936,1536512,-3788800,4535680,-2636928]),(⟨0,1,5⟩,[0,256,-3328,16640,-20224,128256,-738048,1804032,-2244864,1057280]),(⟨0,1,6⟩,[0,256,-3840,24320,-34048,-137472,802560,-1713920,1324288]),(⟨0,2,0⟩,[0,0,-64,832,-4160,8512,1664,-55424,171648,-382080,510400,-182976,-15936,-52416]),(⟨0,2,1⟩,[0,0,-128,1536,-8064,32768,-135936,324608,-247040,-602112,1962880,-2116096,787584]),(⟨0,2,2⟩,[0,0,1024,-6144,-26624,344064,-976896,800768,1284096,-3878912,3748864,-1290240]),(⟨0,2,3⟩,[0,128,-2432,24576,-134656,319232,84224,-1980416,4253184,-4597632,2558080]),(⟨0,2,4⟩,[0,0,-256,-12032,82176,-391424,923904,-1288448,1361664,-675584]),(⟨0,2,5⟩,[0,256,256,-43264,189184,-84224,-934144,2134272,-1786624]),(⟨0,2,6⟩,[0,512,-5120,13824,-22528,159232,-218112,-189952]),(⟨0,3,0⟩,[0,0,128,-1536,8064,-32768,135936,-324608,247040,602112,-1962880,2116096,-787584]),(⟨0,3,1⟩,[0,0,-896,9088,-30208,-13824,297216,-910592,1414656,-1247744,1194624,-712320]),(⟨0,3,2⟩,[0,128,-2432,24576,-134656,319232,84224,-1980416,4253184,-4597632,2558080]),(⟨0,3,3⟩,[0,-512,8192,-20480,-79872,529408,-774144,290816,-301056,347648]),(⟨0,3,4⟩,[0,-512,3584,18944,-155136,221696,131584,-420352,462336]),(⟨0,3,5⟩,[0,0,3584,-73216,281600,-719872,1099264,-591360]),(⟨0,3,6⟩,[0,512,-4608,-3072,-115712,616960,-756224]),(⟨0,4,0⟩,[0,0,384,-6016,43520,-158208,191232,510208,-2056704,3187200,-3069056,1357440]),(⟨0,4,1⟩,[0,-128,2944,-31232,165888,-380160,71936,1536512,-3788800,4535680,-2636928]),(⟨0,4,2⟩,[0,0,-256,-12032,82176,-391424,923904,-1288448,1361664,-675584]),(⟨0,4,3⟩,[0,-512,3584,18944,-155136,221696,131584,-420352,462336]),(⟨0,4,4⟩,[0,-1024,3072,118784,-518144,1121280,-1762304,1562624]),(⟨0,4,5⟩,[0,-512,4608,3072,115712,-616960,756224]),(⟨0,4,6⟩,[0,0,4096,-61440,143360,-86016]),(⟨0,5,0⟩,[0,0,-512,6656,-31232,60928,-156160,443904,-464384,61952,78848]),(⟨0,5,1⟩,[0,256,-3328,16640,-20224,128256,-738048,1804032,-2244864,1057280]),(⟨0,5,2⟩,[0,256,256,-43264,189184,-84224,-934144,2134272,-1786624]),(⟨0,5,3⟩,[0,0,3584,-73216,281600,-719872,1099264,-591360]),(⟨0,5,4⟩,[0,-512,4608,3072,115712,-616960,756224]),(⟨0,5,5⟩,[0,0,-8192,122880,-286720,172032]),(⟨0,6,0⟩,[0,0,-512,5632,-22016,-1536,201216,-660992,1033728,-555520]),(⟨0,6,1⟩,[0,256,-3840,24320,-34048,-137472,802560,-1713920,1324288]),(⟨0,6,2⟩,[0,512,-5120,13824,-22528,159232,-218112,-189952]),(⟨0,6,3⟩,[0,512,-4608,-3072,-115712,616960,-756224]),(⟨0,6,4⟩,[0,0,4096,-61440,143360,-86016]),(⟨1,0,2⟩,[0,64,-832,3392,-320,-26752,22656,208256,-817024,1630272,-2338112,2534720,-1216320]),(⟨1,0,3⟩,[0,-192,3328,-21568,60928,-31872,-324608,1392256,-3120640,4437312,-4827392,3218880]),(⟨1,0,4⟩,[0,-256,4096,-27136,74752,-13312,-433152,1284608,-1483776,99584,494592]),(⟨1,0,5⟩,[0,512,-7936,41216,-65792,-121088,608000,-1315072,2242816,-1775872]),(⟨1,0,6⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,1,1⟩,[0,-128,1664,-6784,640,53504,-45312,-416512,1634048,-3260544,4676224,-5069440,2432640]),(⟨1,1,2⟩,[0,192,-3328,21568,-60928,31872,324608,-1392256,3120640,-4437312,4827392,-3218880]),(⟨1,1,3⟩,[0,128,-896,4096,-22528,179968,-1078528,3328000,-6268928,7293056,-3434368]),(⟨1,1,4⟩,[0,-896,14080,-69120,68352,598784,-2605824,4635136,-4423424,2307200]),(⟨1,1,5⟩,[-128,2304,-14848,23808,142592,-756992,1912320,-3184896,2531200]),(⟨1,1,6⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,2,0⟩,[0,64,-832,3392,-320,-26752,22656,208256,-817024,1630272,-2338112,2534720,-1216320]),(⟨1,2,1⟩,[0,192,-3328,21568,-60928,31872,324608,-1392256,3120640,-4437312,4827392,-3218880]),(⟨1,2,2⟩,[0,256,-6400,46080,-104448,-333312,3023360,-9225216,15505408,-14785280,5879552]),(⟨1,2,3⟩,[0,384,-6144,27904,-2560,-477696,1997824,-3320064,2180608,-531328]),(⟨1,2,4⟩,[0,-512,5632,32256,-494080,1960448,-4197888,5020160,-2326016]),(⟨1,2,5⟩,[0,-1536,25088,-143360,361472,-337408,-378368,867328]),(⟨1,2,6⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨1,3,0⟩,[0,-192,3328,-21568,60928,-31872,-324608,1392256,-3120640,4437312,-4827392,3218880]),(⟨1,3,1⟩,[0,128,-896,4096,-22528,179968,-1078528,3328000,-6268928,7293056,-3434368]),(⟨1,3,2⟩,[0,384,-6144,27904,-2560,-477696,1997824,-3320064,2180608,-531328]),(⟨1,3,3⟩,[256,-4096,24064,-128000,646144,-2082816,4450816,-4584448,367360]),(⟨1,3,4⟩,[0,1024,-18944,136704,-451584,528384,593408,-1444352]),(⟨1,3,5⟩,[0,-512,4608,44032,-433152,947712,-562688]),(⟨1,4,0⟩,[0,-256,4096,-27136,74752,-13312,-433152,1284608,-1483776,99584,494592]),(⟨1,4,1⟩,[0,-896,14080,-69120,68352,598784,-2605824,4635136,-4423424,2307200]),(⟨1,4,2⟩,[0,-512,5632,32256,-494080,1960448,-4197888,5020160,-2326016]),(⟨1,4,3⟩,[0,1024,-18944,136704,-451584,528384,593408,-1444352]),(⟨1,4,4⟩,[0,0,8192,-147456,851968,-1687552,974848]),(⟨1,5,0⟩,[0,512,-7936,41216,-65792,-121088,608000,-1315072,2242816,-1775872]),(⟨1,5,1⟩,[-128,2304,-14848,23808,142592,-756992,1912320,-3184896,2531200]),(⟨1,5,2⟩,[0,-1536,25088,-143360,361472,-337408,-378368,867328]),(⟨1,5,3⟩,[0,-512,4608,44032,-433152,947712,-562688]),(⟨1,6,0⟩,[0,256,-2816,7936,28416,-162048,60160,456960,-388864]),(⟨1,6,1⟩,[0,512,-6144,6656,90112,-190976,-215040,577024]),(⟨1,6,2⟩,[0,512,-8704,29696,7168,-103936,75264]),(⟨2,0,2⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,0,3⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,0,4⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,0,5⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,1,1⟩,[0,0,0,-512,11264,-90112,314368,-398336,-375808,1961984,-2702336,1279488]),(⟨2,1,2⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,1,3⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,1,4⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,1,5⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,2,0⟩,[0,0,0,256,-5632,45056,-157184,199168,187904,-980992,1351168,-639744]),(⟨2,2,1⟩,[-64,1152,-7232,16384,25216,-243968,583296,-327680,-1307200,3052672,-2185792]),(⟨2,2,2⟩,[0,-256,7168,-70144,301056,-583680,228352,1665536,-4386816,3625216]),(⟨2,2,3⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,2,4⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,3,0⟩,[64,-1152,7232,-16384,-25216,243968,-583296,327680,1307200,-3052672,2185792]),(⟨2,3,1⟩,[0,256,-5632,45568,-167424,267264,40448,-1081856,1967616,-1066240]),(⟨2,3,2⟩,[128,-2048,10496,-16896,-24576,154624,-249088,-225792,746368]),(⟨2,4,0⟩,[0,-128,2048,-10496,16896,24576,-154624,249088,225792,-746368]),(⟨2,4,1⟩,[0,0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨2,4,2⟩,[0,512,-10240,68096,-147456,-100864,616448,-426496]),(⟨2,5,0⟩,[-128,2048,-9984,6656,92672,-302080,148224,842240,-1172864]),(⟨2,5,1⟩,[0,-512,10240,-68096,147456,100864,-616448,426496]),(⟨3,0,3⟩,[0,128,-2048,11520,-31232,41984,-5120,-106752,423424,-594048]),(⟨3,0,4⟩,[0,0,-1536,21504,-84480,55296,247296,-420864,182784]),(⟨3,0,5⟩,[0,-512,7168,-30208,43008,20992,-214016,304640]),(⟨3,1,2⟩,[0,-128,2048,-11520,31232,-41984,5120,106752,-423424,594048]),(⟨3,1,4⟩,[0,1280,-17920,74496,-95232,-83200,498176,-639744]),(⟨3,1,5⟩,[256,-3584,16128,-33792,20224,143872,-274176]),(⟨3,2,1⟩,[0,-128,2048,-11520,31232,-41984,5120,106752,-423424,594048]),(⟨3,2,2⟩,[0,0,3072,-43008,168960,-110592,-494592,841728,-365568]),(⟨3,2,3⟩,[0,-768,10752,-44288,52224,62208,-284160,335104]),(⟨3,2,5⟩,[0,2048,-24576,61440,73728,-243712]),(⟨3,3,0⟩,[0,128,-2048,11520,-31232,41984,-5120,-106752,423424,-594048]),(⟨3,3,2⟩,[0,-768,10752,-44288,52224,62208,-284160,335104]),(⟨3,3,3⟩,[-512,7168,-32256,67584,-40448,-287744,548352]),(⟨3,3,4⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨3,4,0⟩,[0,0,-1536,21504,-84480,55296,247296,-420864,182784]),(⟨3,4,1⟩,[0,1280,-17920,74496,-95232,-83200,498176,-639744]),(⟨3,4,3⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨3,5,0⟩,[0,-512,7168,-30208,43008,20992,-214016,304640]),(⟨3,5,1⟩,[256,-3584,16128,-33792,20224,143872,-274176]),(⟨3,5,2⟩,[0,2048,-24576,61440,73728,-243712]),(⟨4,0,3⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,0,4⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,0,5⟩,[256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,1,2⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,1⟩,[128,-2048,9984,-9728,-48640,123904,-43776,-218624,319872]),(⟨4,2,2⟩,[0,-512,7168,-24064,-30720,205312,7168,-426496]),(⟨4,2,3⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,3,0⟩,[-128,2048,-9984,9728,48640,-123904,43776,218624,-319872]),(⟨4,3,2⟩,[-256,3584,-12032,-15360,102656,3584,-213248]),(⟨4,4,0⟩,[0,256,-3584,12032,15360,-102656,-3584,213248]),(⟨4,5,0⟩,[256,-3584,12032,15360,-102656,-3584,213248])]


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
    (Poly.add (Poly.scale (K.ofRat r1202) (Poly.mul Data.S7_odd.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S7_odd.weightedProduct 0 1).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r1200*r1201 : ℚ)=r1202 := by decide +kernel
  exact Block.sos_scaled_product Data.S7_odd 0 1 r1200 r1201 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=1 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S7_odd.upperColumn 0 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C187

#print axioms Coulomb8.Columns.C187.sound
