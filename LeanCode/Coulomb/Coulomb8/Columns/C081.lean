import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C081

def r0 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 64032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -374016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1545024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -5119872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 14354880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -32596608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 7792608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -60047616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 35235360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -261504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -8353152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 1990656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 2208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -3360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 157280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -758208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 2884800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -9168704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 24395456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -7386528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 81088032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -85787360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 52053216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -10043520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -540288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -10208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 70880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -379328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 1617984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -5521728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 15151040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -32379168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 50247200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -3037408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 30388576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1008384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -5664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 47456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -237152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 859328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -2558144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 6256704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -11092288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 11567648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -3134240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -6359456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 5294496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -2112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 25952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -158208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 651968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -2135424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 332096, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -11054592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 14423840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -11024960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 504224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 7296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -91520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 101760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 155136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -55168, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 1603648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -144896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 12416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -73728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 200064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -306944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 411008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -341120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 72704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -233472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 477184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -59136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 79616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 14848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 88832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 101568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -72064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 114432, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -6507392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 18422400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 61968384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -62776192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 36701888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -1272576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -1888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 14816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -67232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 30528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -65472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 37440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 314816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -1229280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 2218336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -2110304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 860832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 18560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -120576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 539776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -1894784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 5024896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -9310976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 11228032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -7876416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 320768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -92544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 177024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -638592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 1020288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -23040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -27648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 15168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -83712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 17536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -803072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 1882752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -497408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 581312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -345856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 47040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -23808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 115456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -419584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 1156864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -2093824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 2239744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -977152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -32832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 13824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -824832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 1383552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -81792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -4575744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 1387008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -1310400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 10944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -77184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 256896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -368640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -148992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 1496448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -2574720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 2064960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -73600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 61184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 167936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -488832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 440192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 106880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -55296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 92288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 59008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -212864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 340096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -183296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 307456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -1016832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 308224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -291200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 32016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -187008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 772512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -2559936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 7177440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -16298304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 3896304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -30023808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 17617680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -130752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -4176576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 995328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 1104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -1680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 78640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -379104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 1442400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -4584352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 12197728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -3693264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 40544016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -42893680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 26026608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -5021760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -270144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -5104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 35440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -189664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 808992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -2760864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 7575520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -16189584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 25123600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -1518704, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 15194288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -504192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 23728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -118576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 429664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -1279072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 3128352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -5546144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 5783824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1567120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -3179728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 2647248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -1056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 12976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -79104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 325984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -1067712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 166048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -5527296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 7211920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -5512480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 252112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 3648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -45760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 50880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 77568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -27584, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 801824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -72448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 6208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 100032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -153472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 205504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -170560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 36352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -116736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 238592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -29568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -20416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 39808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 7424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 44416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 50784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -36032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 57216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -3253696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 9211200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 30984192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -31388096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 18350944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -636288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 7408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -33616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 15264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -32736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 18720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 157408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -614640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 1109168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -1055152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 430416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 9280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -60288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 269888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -947392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 2512448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -4655488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 5614016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -3938208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 160384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -46272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 88512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -319296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 510144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -11520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 7584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -41856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 8768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -401536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 941376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -248704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 290656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -172928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 23520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -11904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 57728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -209792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 578432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -1046912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 1119872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -488576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -16416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 6912, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -412416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 691776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -40896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -2287872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 693504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -655200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 5472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -38592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 128448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -184320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -74496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 748224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -1287360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 1032480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -36800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 30592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 83968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -244416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 220096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -26816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 53440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -27648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 46144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -15424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 29504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -106432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 170048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -91648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 153728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -508416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 154112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -145600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[r0,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51],[r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62],[r63,r64,r65,r66,r67,r68,r69,r70,r71,r72],[r73,r74,r75,r76,r77,r78,r79,r80,r81],[0,r82,r83,r84,r85,r86,r87,r88],[r89,r90,r91,r92,r93,r94,r95],[0,r75,r96,r97,r98,r99],[],[],[],[0,r75,r100,r101,r102,r103,r104,r105,-337280,r106,r107,r108,r109],[r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121],[0,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131],[0,0,r132,r133,r134,r135,r136,r137,r138,-4224],[],[0,r82,r83,r84,r85,r86,r87,r88],[0,0,r139,r140,r141,r142,768],[],[],[],[],[r143,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153],[r63,r64,r65,r66,r67,r68,r69,r70,r71,r72],[],[],[r89,r90,r91,r92,r93,r94,r95],[],[],[],[],[0,r154,r155,r156,r157,r158,r159,r160,r161],[],[],[0,r75,r96,r97,r98,r99],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r162,r163,r164,r165,r166,r167,r168,r169,r170,28224],[0,r171,r172,r173,r174,r175,r176,r177,r178,r179,-5952],[r180,r181,r182,r183,r184,r185,r186,r187,r188,-1088],[r143,r189,r190,r191,r192,r193,r194,r195,-3136],[r196,r197,r198,r199,r200,r201,r202,-1408],[0,0,r139,r140,r141,r142,768],[],[r203,r204,r205,r206,256],[],[],[r207,r208,r209,r210,r211,r212,r213,r214,r215,6272],[r143,r189,r190,r191,r192,r193,r194,r195,-3136],[r196,r197,r198,r199,r200,r201,r202,-1408],[],[],[r203,r204,r205,r206,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨0,0,1⟩,[r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243]),(⟨0,0,2⟩,[r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256]),(⟨0,0,3⟩,[r216,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,0,4⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278]),(⟨0,0,5⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨0,0,6⟩,[r143,r287,r207,r288,r289,r290,r291,r292,r293]),(⟨0,0,7⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨0,0,8⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨0,0,9⟩,[0,r207,r306,r307,r308,r309]),(⟨0,1,0⟩,[r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243]),(⟨0,1,1⟩,[0,r207,r1,r310,r311,r312,r313,r314,-168640,r315,r316,r317,r318]),(⟨0,1,2⟩,[r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,1,3⟩,[0,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨0,1,4⟩,[0,0,r171,r341,r342,r343,r344,r345,r346,-2112]),(⟨0,1,6⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨0,1,7⟩,[0,0,r196,r347,r348,r349,384]),(⟨0,2,0⟩,[r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256]),(⟨0,2,1⟩,[r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,2,2⟩,[r52,r139,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,2,3⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨0,2,6⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨0,3,0⟩,[r216,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,3,1⟩,[0,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨0,3,2⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨0,3,3⟩,[0,r359,r360,r361,r362,r363,r364,r365,r366]),(⟨0,3,6⟩,[0,r207,r306,r307,r308,r309]),(⟨0,4,0⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278]),(⟨0,4,1⟩,[0,0,r171,r341,r342,r343,r344,r345,r346,-2112]),(⟨0,5,0⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨0,6,0⟩,[r143,r287,r207,r288,r289,r290,r291,r292,r293]),(⟨0,6,1⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨0,6,2⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨0,6,3⟩,[0,r207,r306,r307,r308,r309]),(⟨0,7,0⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨0,7,1⟩,[0,0,r196,r347,r348,r349,384]),(⟨0,8,0⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨0,9,0⟩,[0,r207,r306,r307,r308,r309]),(⟨1,0,0⟩,[r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243]),(⟨1,0,1⟩,[0,r207,r1,r310,r311,r312,r313,r314,-168640,r315,r316,r317,r318]),(⟨1,0,2⟩,[r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨1,0,3⟩,[0,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨1,0,4⟩,[0,0,r171,r341,r342,r343,r344,r345,r346,-2112]),(⟨1,0,6⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨1,0,7⟩,[0,0,r196,r347,r348,r349,384]),(⟨1,1,0⟩,[0,r207,r1,r310,r311,r312,r313,r314,-168640,r315,r316,r317,r318]),(⟨1,1,1⟩,[0,0,r367,r368,r369,r370,r371,r372,r373,r374,r375,14112]),(⟨1,1,2⟩,[0,r376,r377,r378,r379,r380,r381,r382,r383,r384,-2976]),(⟨1,1,3⟩,[r110,r385,r386,r387,r388,r389,r390,r391,r392,-544]),(⟨1,1,4⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨1,1,5⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨1,1,6⟩,[0,0,r196,r347,r348,r349,384]),(⟨1,1,8⟩,[r89,r406,r407,r408,128]),(⟨1,2,0⟩,[r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨1,2,1⟩,[0,r376,r377,r378,r379,r380,r381,r382,r383,r384,-2976]),(⟨1,2,2⟩,[r180,r181,r409,r410,r411,r412,r413,r414,r415,3136]),(⟨1,2,3⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨1,2,4⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨1,2,7⟩,[r89,r406,r407,r408,128]),(⟨1,3,0⟩,[0,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨1,3,1⟩,[r110,r385,r386,r387,r388,r389,r390,r391,r392,-544]),(⟨1,3,2⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨1,4,0⟩,[0,0,r171,r341,r342,r343,r344,r345,r346,-2112]),(⟨1,4,1⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨1,4,2⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨1,5,1⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨1,6,0⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨1,6,1⟩,[0,0,r196,r347,r348,r349,384]),(⟨1,7,0⟩,[0,0,r196,r347,r348,r349,384]),(⟨1,7,2⟩,[r89,r406,r407,r408,128]),(⟨1,8,1⟩,[r89,r406,r407,r408,128]),(⟨2,0,0⟩,[r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256]),(⟨2,0,1⟩,[r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨2,0,2⟩,[r52,r139,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,0,3⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨2,0,6⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨2,1,0⟩,[r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨2,1,1⟩,[0,r376,r377,r378,r379,r380,r381,r382,r383,r384,-2976]),(⟨2,1,2⟩,[r180,r181,r409,r410,r411,r412,r413,r414,r415,3136]),(⟨2,1,3⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨2,1,4⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨2,1,7⟩,[r89,r406,r407,r408,128]),(⟨2,2,0⟩,[r52,r139,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,2,1⟩,[r180,r181,r409,r410,r411,r412,r413,r414,r415,3136]),(⟨2,3,0⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨2,3,1⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨2,4,1⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨2,6,0⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨2,7,1⟩,[r89,r406,r407,r408,128]),(⟨3,0,0⟩,[r216,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨3,0,1⟩,[0,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨3,0,2⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨3,0,3⟩,[0,r359,r360,r361,r362,r363,r364,r365,r366]),(⟨3,0,6⟩,[0,r207,r306,r307,r308,r309]),(⟨3,1,0⟩,[0,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨3,1,1⟩,[r110,r385,r386,r387,r388,r389,r390,r391,r392,-544]),(⟨3,1,2⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨3,2,0⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨3,2,1⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨3,3,0⟩,[0,r359,r360,r361,r362,r363,r364,r365,r366]),(⟨3,6,0⟩,[0,r207,r306,r307,r308,r309]),(⟨4,0,0⟩,[r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278]),(⟨4,0,1⟩,[0,0,r171,r341,r342,r343,r344,r345,r346,-2112]),(⟨4,1,0⟩,[0,0,r171,r341,r342,r343,r344,r345,r346,-2112]),(⟨4,1,1⟩,[r52,r393,r394,r395,r396,r397,r398,r399,-1568]),(⟨4,1,2⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨4,2,1⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨5,0,0⟩,[r14,r279,r206,r280,r281,r282,r283,r284,r285,r286]),(⟨5,1,1⟩,[r63,r400,r401,r402,r403,r404,r405,-704]),(⟨6,0,0⟩,[r143,r287,r207,r288,r289,r290,r291,r292,r293]),(⟨6,0,1⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨6,0,2⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨6,0,3⟩,[0,r207,r306,r307,r308,r309]),(⟨6,1,0⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨6,1,1⟩,[0,0,r196,r347,r348,r349,384]),(⟨6,2,0⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨6,3,0⟩,[0,r207,r306,r307,r308,r309]),(⟨7,0,0⟩,[0,r203,r294,r295,r296,r297,r298,r299]),(⟨7,0,1⟩,[0,0,r196,r347,r348,r349,384]),(⟨7,1,0⟩,[0,0,r196,r347,r348,r349,384]),(⟨7,1,2⟩,[r89,r406,r407,r408,128]),(⟨7,2,1⟩,[r89,r406,r407,r408,128]),(⟨8,0,0⟩,[r300,r193,r301,r302,r303,r304,r305]),(⟨8,1,1⟩,[r89,r406,r407,r408,128]),(⟨9,0,0⟩,[0,r207,r306,r307,r308,r309])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r416) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r417) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[512,-8192,50688,-181248,544256,-1513472,2959872,-2835456,589824]),(⟨6,0,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,0,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,0,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨6,1,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,1,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨6,2,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,3,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨7,0,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨7,0,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨8,1,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[0,3072,-20480,59392,-200704,355328])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[512,-8192,50688,-181248,544256,-1513472,2959872,-2835456,589824]),(⟨0,6,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,6,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,6,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,7,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,7,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨0,8,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,9,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨1,0,0⟩,[-384,8832,-89472,552320,-2452992,8728320,-26100992,64706816,-127225728,188890752,-199974272,138013056,-52281600,7225344]),(⟨1,0,1⟩,[0,1536,-26112,206592,-1073408,4328448,-14334976,38091264,-77454848,114974208,-117071360,72642304,-20283648]),(⟨1,0,2⟩,[384,-8064,67200,-319616,1082624,-2991360,6843136,-12223232,15767936,-13060992,5500544,-658560]),(⟨1,0,3⟩,[0,-2304,31488,-202752,890880,-2995712,7576064,-13801472,17180672,-13029632,4352768]),(⟨1,1,0⟩,[0,1536,-26112,206592,-1073408,4328448,-14334976,38091264,-77454848,114974208,-117071360,72642304,-20283648]),(⟨1,1,1⟩,[0,0,2304,-43776,313344,-1099776,1844736,-109056,-6100992,12945408,-12230400,4478208]),(⟨1,2,0⟩,[384,-8064,67200,-319616,1082624,-2991360,6843136,-12223232,15767936,-13060992,5500544,-658560]),(⟨1,3,0⟩,[0,-2304,31488,-202752,890880,-2995712,7576064,-13801472,17180672,-13029632,4352768]),(⟨1,6,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨1,6,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,7,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,7,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,8,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[-128,4864,-64640,473600,-2344448,8957952,-28366080,73836032,-148922496,216558848,-209143424,117698560,-27508992]),(⟨2,0,1⟩,[0,512,-7936,50688,-227840,1158144,-5794816,21038080,-50187776,75174400,-64589056,24761856]),(⟨2,0,2⟩,[128,-3072,30336,-167424,596224,-1606144,3765504,-6963712,8138368,-4841984,658560]),(⟨2,0,3⟩,[0,-768,12800,-98304,467456,-1610240,4285952,-7970816,8676864,-4352768]),(⟨2,1,0⟩,[0,512,-7936,50688,-227840,1158144,-5794816,21038080,-50187776,75174400,-64589056,24761856]),(⟨2,1,1⟩,[0,0,768,-16896,147456,-643584,1282560,10752,-4644864,7752192,-4478208]),(⟨2,1,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨2,2,0⟩,[128,-3072,30336,-167424,596224,-1606144,3765504,-6963712,8138368,-4841984,658560]),(⟨2,2,1⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨2,3,0⟩,[0,-768,12800,-98304,467456,-1610240,4285952,-7970816,8676864,-4352768]),(⟨2,6,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨2,7,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[1152,-22656,182912,-856448,2881280,-7997696,18134784,-28979968,24603776,2707840,-25659776,16381056]),(⟨3,0,1⟩,[0,-3072,42752,-279552,1268224,-4583424,12523520,-23442432,27731456,-18476032,4628736]),(⟨3,0,2⟩,[-768,13568,-86528,302592,-833536,2017280,-3665408,4219392,-2262272,295680]),(⟨3,0,3⟩,[0,4608,-47616,230912,-839168,2313728,-4187648,4479488,-1954304]),(⟨3,1,0⟩,[0,-3072,42752,-279552,1268224,-4583424,12523520,-23442432,27731456,-18476032,4628736]),(⟨3,1,1⟩,[768,-14592,99840,-294400,244736,671744,-1955328,1760768,4352,-517888]),(⟨3,1,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨3,2,0⟩,[-768,13568,-86528,302592,-833536,2017280,-3665408,4219392,-2262272,295680]),(⟨3,2,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨3,3,0⟩,[0,4608,-47616,230912,-839168,2313728,-4187648,4479488,-1954304]),(⟨3,6,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨4,0,0⟩,[128,-8448,103808,-632832,2607872,-8541696,22582528,-44218368,57695360,-44099840,14118272]),(⟨4,0,1⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨4,1,0⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨4,1,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨4,1,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨4,2,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨5,0,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨5,1,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨6,0,0⟩,[512,-3584,3072,49664,-294912,800256,-1227776,1644032,-1364480]),(⟨6,0,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,0,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,0,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨6,1,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,1,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨6,2,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,3,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨7,0,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨7,0,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨8,1,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[0,3072,-20480,59392,-200704,355328])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[512,-8192,50688,-181248,544256,-1513472,2959872,-2835456,589824]),(⟨0,0,7⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,0,8⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,0,9⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,1,0⟩,[-384,8832,-89472,552320,-2452992,8728320,-26100992,64706816,-127225728,188890752,-199974272,138013056,-52281600,7225344]),(⟨0,1,1⟩,[0,1536,-26112,206592,-1073408,4328448,-14334976,38091264,-77454848,114974208,-117071360,72642304,-20283648]),(⟨0,1,2⟩,[384,-8064,67200,-319616,1082624,-2991360,6843136,-12223232,15767936,-13060992,5500544,-658560]),(⟨0,1,3⟩,[0,-2304,31488,-202752,890880,-2995712,7576064,-13801472,17180672,-13029632,4352768]),(⟨0,1,6⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,1,7⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨0,2,0⟩,[-128,4864,-64640,473600,-2344448,8957952,-28366080,73836032,-148922496,216558848,-209143424,117698560,-27508992]),(⟨0,2,1⟩,[0,512,-7936,50688,-227840,1158144,-5794816,21038080,-50187776,75174400,-64589056,24761856]),(⟨0,2,2⟩,[128,-3072,30336,-167424,596224,-1606144,3765504,-6963712,8138368,-4841984,658560]),(⟨0,2,3⟩,[0,-768,12800,-98304,467456,-1610240,4285952,-7970816,8676864,-4352768]),(⟨0,2,6⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,3,0⟩,[1152,-22656,182912,-856448,2881280,-7997696,18134784,-28979968,24603776,2707840,-25659776,16381056]),(⟨0,3,1⟩,[0,-3072,42752,-279552,1268224,-4583424,12523520,-23442432,27731456,-18476032,4628736]),(⟨0,3,2⟩,[-768,13568,-86528,302592,-833536,2017280,-3665408,4219392,-2262272,295680]),(⟨0,3,3⟩,[0,4608,-47616,230912,-839168,2313728,-4187648,4479488,-1954304]),(⟨0,3,6⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,4,0⟩,[128,-8448,103808,-632832,2607872,-8541696,22582528,-44218368,57695360,-44099840,14118272]),(⟨0,4,1⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨0,5,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨0,6,0⟩,[512,-3584,3072,49664,-294912,800256,-1227776,1644032,-1364480]),(⟨0,6,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,6,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,6,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,7,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,7,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨0,8,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,9,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨1,0,0⟩,[-384,8832,-89472,552320,-2452992,8728320,-26100992,64706816,-127225728,188890752,-199974272,138013056,-52281600,7225344]),(⟨1,0,1⟩,[0,1536,-26112,206592,-1073408,4328448,-14334976,38091264,-77454848,114974208,-117071360,72642304,-20283648]),(⟨1,0,2⟩,[384,-8064,67200,-319616,1082624,-2991360,6843136,-12223232,15767936,-13060992,5500544,-658560]),(⟨1,0,3⟩,[0,-2304,31488,-202752,890880,-2995712,7576064,-13801472,17180672,-13029632,4352768]),(⟨1,0,6⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨1,0,7⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,1,0⟩,[0,3072,-52224,413184,-2146816,8656896,-28669952,76182528,-154909696,229948416,-234142720,145284608,-40567296]),(⟨1,1,1⟩,[0,0,4608,-87552,626688,-2199552,3689472,-218112,-12201984,25890816,-24460800,8956416]),(⟨1,1,6⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,1,8⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,2,0⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨1,2,1⟩,[0,0,768,-16896,147456,-643584,1282560,10752,-4644864,7752192,-4478208]),(⟨1,2,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,2,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,3,0⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨1,3,1⟩,[768,-14592,99840,-294400,244736,671744,-1955328,1760768,4352,-517888]),(⟨1,3,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,4,0⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨1,4,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,4,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,5,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,6,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨1,6,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,7,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,7,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,8,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[-128,4864,-64640,473600,-2344448,8957952,-28366080,73836032,-148922496,216558848,-209143424,117698560,-27508992]),(⟨2,0,1⟩,[0,512,-7936,50688,-227840,1158144,-5794816,21038080,-50187776,75174400,-64589056,24761856]),(⟨2,0,2⟩,[128,-3072,30336,-167424,596224,-1606144,3765504,-6963712,8138368,-4841984,658560]),(⟨2,0,3⟩,[0,-768,12800,-98304,467456,-1610240,4285952,-7970816,8676864,-4352768]),(⟨2,0,6⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨2,1,0⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨2,1,1⟩,[0,0,768,-16896,147456,-643584,1282560,10752,-4644864,7752192,-4478208]),(⟨2,1,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨2,1,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,2,0⟩,[256,-6144,60672,-334848,1192448,-3212288,7531008,-13927424,16276736,-9683968,1317120]),(⟨2,2,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,3,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨2,3,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,4,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,6,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨2,7,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[1152,-22656,182912,-856448,2881280,-7997696,18134784,-28979968,24603776,2707840,-25659776,16381056]),(⟨3,0,1⟩,[0,-3072,42752,-279552,1268224,-4583424,12523520,-23442432,27731456,-18476032,4628736]),(⟨3,0,2⟩,[-768,13568,-86528,302592,-833536,2017280,-3665408,4219392,-2262272,295680]),(⟨3,0,3⟩,[0,4608,-47616,230912,-839168,2313728,-4187648,4479488,-1954304]),(⟨3,0,6⟩,[0,3072,-20480,59392,-200704,355328]),(⟨3,1,0⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨3,1,1⟩,[768,-14592,99840,-294400,244736,671744,-1955328,1760768,4352,-517888]),(⟨3,1,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨3,2,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨3,2,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨3,3,0⟩,[0,9216,-95232,461824,-1678336,4627456,-8375296,8958976,-3908608]),(⟨3,6,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨4,0,0⟩,[128,-8448,103808,-632832,2607872,-8541696,22582528,-44218368,57695360,-44099840,14118272]),(⟨4,0,1⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨4,1,0⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨4,1,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨4,1,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨4,2,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨5,0,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨5,1,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨6,0,0⟩,[512,-3584,3072,49664,-294912,800256,-1227776,1644032,-1364480]),(⟨6,0,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,0,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,0,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨6,1,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,1,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨6,2,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,3,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨7,0,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨7,0,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨8,1,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[0,3072,-20480,59392,-200704,355328])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,1152,-26112,256128,-1496064,6180096,-20479488,57419520,-130386432,218193024,-240190464,140941440,-7322112,-33412608,7962624]),(⟨0,0,1⟩,[-384,8832,-94080,629120,-3032832,11539200,-36674816,97581824,-206822784,324352128,-343149440,208212864,-40174080,-15128064]),(⟨0,0,2⟩,[-128,3712,-40832,283520,-1517312,6471936,-22086912,60604160,-129516672,200988800,-206543744,121554304,-28234752]),(⟨0,0,3⟩,[1152,-22656,189824,-948608,3437312,-10232576,25026816,-44369152,46270592,-12536960,-25437824,21177984]),(⟨0,0,4⟩,[128,-8448,103808,-632832,2607872,-8541696,22582528,-44218368,57695360,-44099840,14118272]),(⟨0,0,5⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨0,0,6⟩,[512,-3584,3072,49664,-294912,800256,-1227776,1644032,-1364480]),(⟨0,0,7⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,0,8⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,0,9⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,1,0⟩,[-384,8832,-94080,629120,-3032832,11539200,-36674816,97581824,-206822784,324352128,-343149440,208212864,-40174080,-15128064]),(⟨0,1,1⟩,[0,3072,-52224,406272,-2017792,7781376,-26029568,73689600,-160545280,247873536,-251104768,146807552,-35632128]),(⟨0,1,2⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨0,1,3⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨0,1,4⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨0,1,6⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,1,7⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨0,2,0⟩,[-128,3712,-40832,283520,-1517312,6471936,-22086912,60604160,-129516672,200988800,-206543744,121554304,-28234752]),(⟨0,2,1⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨0,2,2⟩,[256,-6144,60672,-334848,1192448,-3212288,7531008,-13927424,16276736,-9683968,1317120]),(⟨0,2,3⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨0,2,6⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,3,0⟩,[1152,-22656,189824,-948608,3437312,-10232576,25026816,-44369152,46270592,-12536960,-25437824,21177984]),(⟨0,3,1⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨0,3,2⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨0,3,3⟩,[0,9216,-95232,461824,-1678336,4627456,-8375296,8958976,-3908608]),(⟨0,3,6⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,4,0⟩,[128,-8448,103808,-632832,2607872,-8541696,22582528,-44218368,57695360,-44099840,14118272]),(⟨0,4,1⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨0,5,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨0,6,0⟩,[512,-3584,3072,49664,-294912,800256,-1227776,1644032,-1364480]),(⟨0,6,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,6,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,6,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨0,7,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨0,7,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨0,8,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨0,9,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨1,0,0⟩,[-384,8832,-94080,629120,-3032832,11539200,-36674816,97581824,-206822784,324352128,-343149440,208212864,-40174080,-15128064]),(⟨1,0,1⟩,[0,3072,-52224,406272,-2017792,7781376,-26029568,73689600,-160545280,247873536,-251104768,146807552,-35632128]),(⟨1,0,2⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨1,0,3⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨1,0,4⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨1,0,6⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨1,0,7⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,1,0⟩,[0,3072,-52224,406272,-2017792,7781376,-26029568,73689600,-160545280,247873536,-251104768,146807552,-35632128]),(⟨1,1,1⟩,[0,0,6912,-131328,940032,-3299328,5534208,-327168,-18302976,38836224,-36691200,13434624]),(⟨1,1,2⟩,[0,-2304,43776,-308736,1027584,-1474560,-595968,5985792,-10298880,8259840,-2833152]),(⟨1,1,3⟩,[768,-14592,99840,-294400,244736,671744,-1955328,1760768,4352,-517888]),(⟨1,1,4⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,1,5⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,1,6⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,1,8⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,2,0⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨1,2,1⟩,[0,-2304,43776,-308736,1027584,-1474560,-595968,5985792,-10298880,8259840,-2833152]),(⟨1,2,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨1,2,3⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,2,4⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,2,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,3,0⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨1,3,1⟩,[768,-14592,99840,-294400,244736,671744,-1955328,1760768,4352,-517888]),(⟨1,3,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,4,0⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨1,4,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,4,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,5,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,6,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨1,6,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,7,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨1,7,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,8,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[-128,3712,-40832,283520,-1517312,6471936,-22086912,60604160,-129516672,200988800,-206543744,121554304,-28234752]),(⟨2,0,1⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨2,0,2⟩,[256,-6144,60672,-334848,1192448,-3212288,7531008,-13927424,16276736,-9683968,1317120]),(⟨2,0,3⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨2,0,6⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨2,1,0⟩,[384,-7552,59264,-268928,854784,-1833216,1048320,8814848,-34419840,62113408,-59088512,24103296]),(⟨2,1,1⟩,[0,-2304,43776,-308736,1027584,-1474560,-595968,5985792,-10298880,8259840,-2833152]),(⟨2,1,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,1,3⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,1,4⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,1,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,2,0⟩,[256,-6144,60672,-334848,1192448,-3212288,7531008,-13927424,16276736,-9683968,1317120]),(⟨2,2,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,3,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨2,3,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,4,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨2,6,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨2,7,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[1152,-22656,189824,-948608,3437312,-10232576,25026816,-44369152,46270592,-12536960,-25437824,21177984]),(⟨3,0,1⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨3,0,2⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨3,0,3⟩,[0,9216,-95232,461824,-1678336,4627456,-8375296,8958976,-3908608]),(⟨3,0,6⟩,[0,3072,-20480,59392,-200704,355328]),(⟨3,1,0⟩,[0,-5376,74240,-482304,2159104,-7579136,20099584,-37243904,44912128,-31505664,8981504]),(⟨3,1,1⟩,[768,-14592,99840,-294400,244736,671744,-1955328,1760768,4352,-517888]),(⟨3,1,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨3,2,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨3,2,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨3,3,0⟩,[0,9216,-95232,461824,-1678336,4627456,-8375296,8958976,-3908608]),(⟨3,6,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨4,0,0⟩,[128,-8448,103808,-632832,2607872,-8541696,22582528,-44218368,57695360,-44099840,14118272]),(⟨4,0,1⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨4,1,0⟩,[0,0,-4608,72192,-370176,708096,78336,-2554368,4081152,-2010624]),(⟨4,1,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨4,1,2⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨4,2,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨5,0,0⟩,[-768,12800,-73728,204288,-366080,407040,620544,-3751424,6414592,-4057088]),(⟨5,1,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨6,0,0⟩,[512,-3584,3072,49664,-294912,800256,-1227776,1644032,-1364480]),(⟨6,0,1⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,0,2⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,0,3⟩,[0,3072,-20480,59392,-200704,355328]),(⟨6,1,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨6,1,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨6,2,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨6,3,0⟩,[0,3072,-20480,59392,-200704,355328]),(⟨7,0,0⟩,[0,-2048,20480,-87040,290816,-933888,1908736,-1655808]),(⟨7,0,1⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,0⟩,[0,0,-3072,36864,-92160,-110592,365568]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[-512,7168,-28160,51200,-163328,318464,-53760]),(⟨8,1,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨9,0,0⟩,[0,3072,-20480,59392,-200704,355328])]


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
    (Poly.add (Poly.scale (K.ofRat r418) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r416*r417 : ℚ)=r418 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 11 r416 r417 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C081

#print axioms Coulomb8.Columns.C081.sound
