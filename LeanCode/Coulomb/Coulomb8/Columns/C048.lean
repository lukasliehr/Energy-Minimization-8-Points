import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C048

def r0 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -3456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 19008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -514368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 343680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -5246784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 5465856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -218496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -1175808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 350208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -11456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 30976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 123328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -1249152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 4364992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -1144832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 7501184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -2315008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -702720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -13696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 164224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -1122176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 3450240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -5799168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 4795136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -182144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 48896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -370688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 968960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -766592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 1242240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -5952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 22016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 60864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -629376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 1723968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -1978624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 683840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 11584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -11520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -158528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 575360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -83904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 2944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -72448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 183552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -5248, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -37376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 76672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -20352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 61568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 8064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1082752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 534656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -6255744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 5068800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -210688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 42496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -92544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -136320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 1075328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -2004736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 189568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 16768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 21888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -47104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 54016, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -1036928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 348032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 20288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -155328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 499200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -63680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1024, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -213760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 632704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -696832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 23424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 8832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -33024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 248704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -44160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -35584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 89344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -3968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 228096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -153344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 76032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -174336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 23808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 590592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -960768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 8576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -39040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 4992, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 26240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 9504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -257184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 171840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -2623392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 2732928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -109248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -587904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 175104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -5728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 15488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 61664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -624576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 2182496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -572416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 3750592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1157504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -351360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -6848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 82112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -561088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 1725120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -2899584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 2397568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -91072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 24448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -185344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 484480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -383296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 621120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -2976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 11008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 30432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -314688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 861984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -989312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 341920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 5792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -5760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -79264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 287680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -41952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 1472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -36224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 91776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -2624, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -18688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 38336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -10176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 30784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 4032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -541376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 267328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -3127872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 2534400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -105344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 21248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -46272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -68160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 537664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1002368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 94784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 8384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 10944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -23552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 27008, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -518464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 174016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 10144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -77664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 249600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -31840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -106880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 316352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -348416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 11712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -16512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 124352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -22080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -17792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 44672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -1984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -5376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 114048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -76672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 38016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -87168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 11904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 295296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -480384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 4288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -19520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 2496, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 13120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10],[r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21],[r22,r23,r24,r25,r26,r27,r28,r29,r30,r31],[r32,r33,r34,r35,r36,r37,r38,-6912,r39],[r40,r41,r42,r43,r44,r45,r46,r47],[r48,r49,r50,r51,r52,r53,r54],[r55,r56,0,r57,r58,r59],[r22,r60,r61,r62,r63],[],[],[],[],[],[r22,r64,r65,r66,r67,r68,r69,r70,r71,r72],[0,r40,r73,r74,r75,r76,r77,r78,r79],[r61,r80,r81,r82,r83,r84,r85,r86],[r0,r87,r88,r89,r90,r91,r92],[r22,r93,r94,r95,r12,384],[r22,r60,r96,r97,128],[],[],[],[],[],[r61,r98,r99,r100,r101,r102,r103,r104],[0,r105,r106,r107,r108,r109,r110],[r55,r56,r80,r111,r112,r113],[r22,r60,r96,r97,128],[],[],[],[],[],[r55,r114,r115,r116,r117,r118],[r22,r60,r61,r62,r63],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r94,r108,r119,r120,r121,r122,r123,3840],[r32,r124,r125,r126,r127,r128,r129,-1152],[0,r130,r131,r89,r132,r133,-512],[0,r130,r134,r135,r136,512],[],[],[],[],[],[],[r32,r137,r138,r89,r73,r139,-896],[r22,r140,r141,r142,r143,-128],[r22,r60,r96,r97,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154]),(⟨0,0,1⟩,[r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165]),(⟨0,0,2⟩,[r11,r93,r166,r167,r168,r169,r170,r171,r172,r173]),(⟨0,0,3⟩,[r48,r174,r175,r176,r177,r178,r179,-3456,r180]),(⟨0,0,4⟩,[r0,r181,r182,r183,r184,r185,r186,r187]),(⟨0,0,5⟩,[r188,r189,r190,r191,r192,r193,r194]),(⟨0,0,6⟩,[r22,r195,0,r196,r197,r198]),(⟨0,0,7⟩,[r11,r94,r32,r199,r200]),(⟨0,1,0⟩,[r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165]),(⟨0,1,1⟩,[r11,r201,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨0,1,2⟩,[0,r0,r210,r211,r212,r213,r214,r215,r216]),(⟨0,1,3⟩,[r32,r137,r217,r218,r219,r220,r221,r222]),(⟨0,1,4⟩,[r144,r33,r223,r224,r225,r226,r227]),(⟨0,1,5⟩,[r11,r228,r40,r229,r156,192]),(⟨0,1,6⟩,[r11,r94,r124,r230,64]),(⟨0,2,0⟩,[r11,r93,r166,r167,r168,r169,r170,r171,r172,r173]),(⟨0,2,1⟩,[0,r0,r210,r211,r212,r213,r214,r215,r216]),(⟨0,2,2⟩,[r32,r231,r232,r233,r234,r235,r236,r237]),(⟨0,2,3⟩,[0,r238,r239,r240,r241,r242,r243]),(⟨0,2,4⟩,[r22,r195,r137,r244,r245,r246]),(⟨0,2,5⟩,[r11,r94,r124,r230,64]),(⟨0,3,0⟩,[r48,r174,r175,r176,r177,r178,r179,-3456,r180]),(⟨0,3,1⟩,[r32,r137,r217,r218,r219,r220,r221,r222]),(⟨0,3,2⟩,[0,r238,r239,r240,r241,r242,r243]),(⟨0,3,3⟩,[r22,r140,r247,r248,r249,r250]),(⟨0,3,4⟩,[r11,r94,r32,r199,r200]),(⟨0,4,0⟩,[r0,r181,r182,r183,r184,r185,r186,r187]),(⟨0,4,1⟩,[r144,r33,r223,r224,r225,r226,r227]),(⟨0,4,2⟩,[r22,r195,r137,r244,r245,r246]),(⟨0,4,3⟩,[r11,r94,r32,r199,r200]),(⟨0,5,0⟩,[r188,r189,r190,r191,r192,r193,r194]),(⟨0,5,1⟩,[r11,r228,r40,r229,r156,192]),(⟨0,5,2⟩,[r11,r94,r124,r230,64]),(⟨0,6,0⟩,[r22,r195,0,r196,r197,r198]),(⟨0,6,1⟩,[r11,r94,r124,r230,64]),(⟨0,7,0⟩,[r11,r94,r32,r199,r200]),(⟨1,0,0⟩,[r155,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165]),(⟨1,0,1⟩,[r11,r201,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨1,0,2⟩,[0,r0,r210,r211,r212,r213,r214,r215,r216]),(⟨1,0,3⟩,[r32,r137,r217,r218,r219,r220,r221,r222]),(⟨1,0,4⟩,[r144,r33,r223,r224,r225,r226,r227]),(⟨1,0,5⟩,[r11,r228,r40,r229,r156,192]),(⟨1,0,6⟩,[r11,r94,r124,r230,64]),(⟨1,1,0⟩,[r11,r201,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨1,1,1⟩,[0,r40,r241,r251,r252,r253,r254,r255,1920]),(⟨1,1,2⟩,[r48,r256,r257,r258,r259,r260,r261,-576]),(⟨1,1,3⟩,[0,r55,r114,r224,r262,r263,-256]),(⟨1,1,4⟩,[0,r55,r264,r265,r266,256]),(⟨1,2,0⟩,[0,r0,r210,r211,r212,r213,r214,r215,r216]),(⟨1,2,1⟩,[r48,r256,r257,r258,r259,r260,r261,-576]),(⟨1,2,2⟩,[r48,r267,r268,r224,r210,r269,-448]),(⟨1,2,3⟩,[r11,r270,r271,r272,r273,-64]),(⟨1,2,4⟩,[r11,r94,r124,r230,64]),(⟨1,3,0⟩,[r32,r137,r217,r218,r219,r220,r221,r222]),(⟨1,3,1⟩,[0,r55,r114,r224,r262,r263,-256]),(⟨1,3,2⟩,[r11,r270,r271,r272,r273,-64]),(⟨1,4,0⟩,[r144,r33,r223,r224,r225,r226,r227]),(⟨1,4,1⟩,[0,r55,r264,r265,r266,256]),(⟨1,4,2⟩,[r11,r94,r124,r230,64]),(⟨1,5,0⟩,[r11,r228,r40,r229,r156,192]),(⟨1,6,0⟩,[r11,r94,r124,r230,64]),(⟨2,0,0⟩,[r11,r93,r166,r167,r168,r169,r170,r171,r172,r173]),(⟨2,0,1⟩,[0,r0,r210,r211,r212,r213,r214,r215,r216]),(⟨2,0,2⟩,[r32,r231,r232,r233,r234,r235,r236,r237]),(⟨2,0,3⟩,[0,r238,r239,r240,r241,r242,r243]),(⟨2,0,4⟩,[r22,r195,r137,r244,r245,r246]),(⟨2,0,5⟩,[r11,r94,r124,r230,64]),(⟨2,1,0⟩,[0,r0,r210,r211,r212,r213,r214,r215,r216]),(⟨2,1,1⟩,[r48,r256,r257,r258,r259,r260,r261,-576]),(⟨2,1,2⟩,[r48,r267,r268,r224,r210,r269,-448]),(⟨2,1,3⟩,[r11,r270,r271,r272,r273,-64]),(⟨2,1,4⟩,[r11,r94,r124,r230,64]),(⟨2,2,0⟩,[r32,r231,r232,r233,r234,r235,r236,r237]),(⟨2,2,1⟩,[r48,r267,r268,r224,r210,r269,-448]),(⟨2,3,0⟩,[0,r238,r239,r240,r241,r242,r243]),(⟨2,3,1⟩,[r11,r270,r271,r272,r273,-64]),(⟨2,4,0⟩,[r22,r195,r137,r244,r245,r246]),(⟨2,4,1⟩,[r11,r94,r124,r230,64]),(⟨2,5,0⟩,[r11,r94,r124,r230,64]),(⟨3,0,0⟩,[r48,r174,r175,r176,r177,r178,r179,-3456,r180]),(⟨3,0,1⟩,[r32,r137,r217,r218,r219,r220,r221,r222]),(⟨3,0,2⟩,[0,r238,r239,r240,r241,r242,r243]),(⟨3,0,3⟩,[r22,r140,r247,r248,r249,r250]),(⟨3,0,4⟩,[r11,r94,r32,r199,r200]),(⟨3,1,0⟩,[r32,r137,r217,r218,r219,r220,r221,r222]),(⟨3,1,1⟩,[0,r55,r114,r224,r262,r263,-256]),(⟨3,1,2⟩,[r11,r270,r271,r272,r273,-64]),(⟨3,2,0⟩,[0,r238,r239,r240,r241,r242,r243]),(⟨3,2,1⟩,[r11,r270,r271,r272,r273,-64]),(⟨3,3,0⟩,[r22,r140,r247,r248,r249,r250]),(⟨3,4,0⟩,[r11,r94,r32,r199,r200]),(⟨4,0,0⟩,[r0,r181,r182,r183,r184,r185,r186,r187]),(⟨4,0,1⟩,[r144,r33,r223,r224,r225,r226,r227]),(⟨4,0,2⟩,[r22,r195,r137,r244,r245,r246]),(⟨4,0,3⟩,[r11,r94,r32,r199,r200]),(⟨4,1,0⟩,[r144,r33,r223,r224,r225,r226,r227]),(⟨4,1,1⟩,[0,r55,r264,r265,r266,256]),(⟨4,1,2⟩,[r11,r94,r124,r230,64]),(⟨4,2,0⟩,[r22,r195,r137,r244,r245,r246]),(⟨4,2,1⟩,[r11,r94,r124,r230,64]),(⟨4,3,0⟩,[r11,r94,r32,r199,r200]),(⟨5,0,0⟩,[r188,r189,r190,r191,r192,r193,r194]),(⟨5,0,1⟩,[r11,r228,r40,r229,r156,192]),(⟨5,0,2⟩,[r11,r94,r124,r230,64]),(⟨5,1,0⟩,[r11,r228,r40,r229,r156,192]),(⟨5,2,0⟩,[r11,r94,r124,r230,64]),(⟨6,0,0⟩,[r22,r195,0,r196,r197,r198]),(⟨6,0,1⟩,[r11,r94,r124,r230,64]),(⟨6,1,0⟩,[r11,r94,r124,r230,64]),(⟨7,0,0⟩,[r11,r94,r32,r199,r200])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r274) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r275) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[256,-3584,10240,61440,-463616,1148416,-1134080,233472]),(⟨4,0,1⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨4,0,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨4,0,3⟩,[-256,3072,512,-74752,153344]),(⟨4,1,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨4,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨4,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨4,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[-256,3072,512,-74752,153344]),(⟨5,0,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨5,0,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨5,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨5,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨6,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,3072,512,-74752,153344])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[256,-3584,10240,61440,-463616,1148416,-1134080,233472]),(⟨0,4,1⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,4,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,4,3⟩,[-256,3072,512,-74752,153344]),(⟨0,5,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,5,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,6,1⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-256,3072,512,-74752,153344]),(⟨1,0,0⟩,[-128,2432,-15232,11648,330368,-1984128,5677952,-9278848,8558080,-3885824,583680]),(⟨1,0,1⟩,[-128,2688,-19584,49280,118656,-1173376,3591296,-5761152,4849920,-1657600]),(⟨1,0,2⟩,[128,-1920,6272,29056,-248704,679808,-862336,460416,-62720]),(⟨1,0,3⟩,[128,-2176,8576,24192,-258176,721024,-876928,383360]),(⟨1,1,0⟩,[-128,2688,-19584,49280,118656,-1173376,3591296,-5761152,4849920,-1657600]),(⟨1,1,1⟩,[0,512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨1,1,2⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,2,0⟩,[128,-1920,6272,29056,-248704,679808,-862336,460416,-62720]),(⟨1,2,1⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,3,0⟩,[128,-2176,8576,24192,-258176,721024,-876928,383360]),(⟨1,4,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨1,4,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-256,4992,-32768,51584,437504,-2889856,8077824,-12165504,9286144,-2474752]),(⟨2,0,1⟩,[-128,3072,-25984,87040,18304,-1028096,3260288,-4579328,2625280]),(⟨2,0,2⟩,[256,-3968,17408,1920,-213760,632704,-696832,163968]),(⟨2,0,3⟩,[128,-2048,6784,27648,-227968,568320,-536704]),(⟨2,1,0⟩,[-128,3072,-25984,87040,18304,-1028096,3260288,-4579328,2625280]),(⟨2,1,1⟩,[0,512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,1,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[256,-3968,17408,1920,-213760,632704,-696832,163968]),(⟨2,2,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,3,0⟩,[128,-2048,6784,27648,-227968,568320,-536704]),(⟨2,4,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[256,-3200,2816,116608,-639232,1247872,-278272,-2110848,2024448]),(⟨3,0,1⟩,[384,-6016,24960,19584,-401280,1115520,-1196928,312704]),(⟨3,0,2⟩,[-128,768,10880,-93696,201856,-70912,-81536]),(⟨3,0,3⟩,[-256,3328,-2560,-75264,228096,-153344]),(⟨3,1,0⟩,[384,-6016,24960,19584,-401280,1115520,-1196928,312704]),(⟨3,1,1⟩,[0,-1024,13312,-43008,-6144,158720,-121856]),(⟨3,1,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[-128,768,10880,-93696,201856,-70912,-81536]),(⟨3,2,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,3,0⟩,[-256,3328,-2560,-75264,228096,-153344]),(⟨3,4,0⟩,[-256,3072,512,-74752,153344]),(⟨4,0,0⟩,[768,-11904,44032,121728,-1258752,3447936,-3957248,1367680]),(⟨4,0,1⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨4,0,2⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨4,0,3⟩,[-256,3072,512,-74752,153344]),(⟨4,1,0⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨4,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨4,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨4,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[-256,3072,512,-74752,153344]),(⟨5,0,0⟩,[128,-3328,23168,-23040,-317056,1150720,-1174656]),(⟨5,0,1⟩,[-256,2304,1536,-32256,2816,91392]),(⟨5,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[-256,2304,1536,-32256,2816,91392]),(⟨5,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-512,5888,0,-144896,367104,-178432]),(⟨6,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,3072,512,-74752,153344])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[256,-3584,10240,61440,-463616,1148416,-1134080,233472]),(⟨0,0,5⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,0,6⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,0,7⟩,[-256,3072,512,-74752,153344]),(⟨0,1,0⟩,[-128,2432,-15232,11648,330368,-1984128,5677952,-9278848,8558080,-3885824,583680]),(⟨0,1,1⟩,[-128,2688,-19584,49280,118656,-1173376,3591296,-5761152,4849920,-1657600]),(⟨0,1,2⟩,[128,-1920,6272,29056,-248704,679808,-862336,460416,-62720]),(⟨0,1,3⟩,[128,-2176,8576,24192,-258176,721024,-876928,383360]),(⟨0,1,4⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,1,5⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,1,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[-256,4992,-32768,51584,437504,-2889856,8077824,-12165504,9286144,-2474752]),(⟨0,2,1⟩,[-128,3072,-25984,87040,18304,-1028096,3260288,-4579328,2625280]),(⟨0,2,2⟩,[256,-3968,17408,1920,-213760,632704,-696832,163968]),(⟨0,2,3⟩,[128,-2048,6784,27648,-227968,568320,-536704]),(⟨0,2,4⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,2,5⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[256,-3200,2816,116608,-639232,1247872,-278272,-2110848,2024448]),(⟨0,3,1⟩,[384,-6016,24960,19584,-401280,1115520,-1196928,312704]),(⟨0,3,2⟩,[-128,768,10880,-93696,201856,-70912,-81536]),(⟨0,3,3⟩,[-256,3328,-2560,-75264,228096,-153344]),(⟨0,3,4⟩,[-256,3072,512,-74752,153344]),(⟨0,4,0⟩,[768,-11904,44032,121728,-1258752,3447936,-3957248,1367680]),(⟨0,4,1⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨0,4,2⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨0,4,3⟩,[-256,3072,512,-74752,153344]),(⟨0,5,0⟩,[128,-3328,23168,-23040,-317056,1150720,-1174656]),(⟨0,5,1⟩,[-256,2304,1536,-32256,2816,91392]),(⟨0,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[-512,5888,0,-144896,367104,-178432]),(⟨0,6,1⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-256,3072,512,-74752,153344]),(⟨1,0,0⟩,[-128,2432,-15232,11648,330368,-1984128,5677952,-9278848,8558080,-3885824,583680]),(⟨1,0,1⟩,[-128,2688,-19584,49280,118656,-1173376,3591296,-5761152,4849920,-1657600]),(⟨1,0,2⟩,[128,-1920,6272,29056,-248704,679808,-862336,460416,-62720]),(⟨1,0,3⟩,[128,-2176,8576,24192,-258176,721024,-876928,383360]),(⟨1,0,4⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨1,0,5⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[-256,5376,-39168,98560,237312,-2346752,7182592,-11522304,9699840,-3315200]),(⟨1,1,1⟩,[0,1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨1,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,1,4⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,2,0⟩,[0,1152,-19712,116096,-230400,-348288,2397952,-4118912,2562560]),(⟨1,2,1⟩,[128,-1664,4480,14464,-82048,71296,212608,-350336]),(⟨1,2,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,3,0⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨1,3,1⟩,[0,-1024,13312,-43008,-6144,158720,-121856]),(⟨1,3,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,4,0⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨1,4,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[-256,2304,1536,-32256,2816,91392]),(⟨1,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-256,4992,-32768,51584,437504,-2889856,8077824,-12165504,9286144,-2474752]),(⟨2,0,1⟩,[-128,3072,-25984,87040,18304,-1028096,3260288,-4579328,2625280]),(⟨2,0,2⟩,[256,-3968,17408,1920,-213760,632704,-696832,163968]),(⟨2,0,3⟩,[128,-2048,6784,27648,-227968,568320,-536704]),(⟨2,0,4⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,0,5⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[0,1152,-19712,116096,-230400,-348288,2397952,-4118912,2562560]),(⟨2,1,1⟩,[128,-1664,4480,14464,-82048,71296,212608,-350336]),(⟨2,1,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[512,-7936,34816,3840,-427520,1265408,-1393664,327936]),(⟨2,2,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,0⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨2,3,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,4,0⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨2,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[256,-3200,2816,116608,-639232,1247872,-278272,-2110848,2024448]),(⟨3,0,1⟩,[384,-6016,24960,19584,-401280,1115520,-1196928,312704]),(⟨3,0,2⟩,[-128,768,10880,-93696,201856,-70912,-81536]),(⟨3,0,3⟩,[-256,3328,-2560,-75264,228096,-153344]),(⟨3,0,4⟩,[-256,3072,512,-74752,153344]),(⟨3,1,0⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨3,1,1⟩,[0,-1024,13312,-43008,-6144,158720,-121856]),(⟨3,1,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨3,2,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,3,0⟩,[-512,6656,-5120,-150528,456192,-306688]),(⟨3,4,0⟩,[-256,3072,512,-74752,153344]),(⟨4,0,0⟩,[768,-11904,44032,121728,-1258752,3447936,-3957248,1367680]),(⟨4,0,1⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨4,0,2⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨4,0,3⟩,[-256,3072,512,-74752,153344]),(⟨4,1,0⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨4,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨4,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨4,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[-256,3072,512,-74752,153344]),(⟨5,0,0⟩,[128,-3328,23168,-23040,-317056,1150720,-1174656]),(⟨5,0,1⟩,[-256,2304,1536,-32256,2816,91392]),(⟨5,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[-256,2304,1536,-32256,2816,91392]),(⟨5,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-512,5888,0,-144896,367104,-178432]),(⟨6,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,3072,512,-74752,153344])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,384,-6912,38016,15360,-1028736,4811520,-10493568,10931712,-3058944,-2351616,700416]),(⟨0,0,1⟩,[-128,2816,-22912,61952,246656,-2498304,8729984,-16027648,15002368,-4630016,-1405440]),(⟨0,0,2⟩,[-256,4608,-27392,38912,328448,-2244352,6900480,-11598336,9590272,-2550016]),(⟨0,0,3⟩,[256,-3584,8960,97792,-741376,1937920,-1533184,-1645056,2484480]),(⟨0,0,4⟩,[768,-11904,44032,121728,-1258752,3447936,-3957248,1367680]),(⟨0,0,5⟩,[128,-3328,23168,-23040,-317056,1150720,-1174656]),(⟨0,0,6⟩,[-512,5888,0,-144896,367104,-178432]),(⟨0,0,7⟩,[-256,3072,512,-74752,153344]),(⟨0,1,0⟩,[-128,2816,-22912,61952,246656,-2498304,8729984,-16027648,15002368,-4630016,-1405440]),(⟨0,1,1⟩,[-256,5376,-40704,123136,112896,-2165504,7485184,-12511488,10137600,-2949632]),(⟨0,1,2⟩,[0,768,-13568,84992,-185088,-272640,2150656,-4009472,2653952]),(⟨0,1,3⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨0,1,4⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨0,1,5⟩,[-256,2304,1536,-32256,2816,91392]),(⟨0,1,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[-256,4608,-27392,38912,328448,-2244352,6900480,-11598336,9590272,-2550016]),(⟨0,2,1⟩,[0,768,-13568,84992,-185088,-272640,2150656,-4009472,2653952]),(⟨0,2,2⟩,[512,-7936,34816,3840,-427520,1265408,-1393664,327936]),(⟨0,2,3⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨0,2,4⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨0,2,5⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[256,-3584,8960,97792,-741376,1937920,-1533184,-1645056,2484480]),(⟨0,3,1⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨0,3,2⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨0,3,3⟩,[-512,6656,-5120,-150528,456192,-306688]),(⟨0,3,4⟩,[-256,3072,512,-74752,153344]),(⟨0,4,0⟩,[768,-11904,44032,121728,-1258752,3447936,-3957248,1367680]),(⟨0,4,1⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨0,4,2⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨0,4,3⟩,[-256,3072,512,-74752,153344]),(⟨0,5,0⟩,[128,-3328,23168,-23040,-317056,1150720,-1174656]),(⟨0,5,1⟩,[-256,2304,1536,-32256,2816,91392]),(⟨0,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[-512,5888,0,-144896,367104,-178432]),(⟨0,6,1⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-256,3072,512,-74752,153344]),(⟨1,0,0⟩,[-128,2816,-22912,61952,246656,-2498304,8729984,-16027648,15002368,-4630016,-1405440]),(⟨1,0,1⟩,[-256,5376,-40704,123136,112896,-2165504,7485184,-12511488,10137600,-2949632]),(⟨1,0,2⟩,[0,768,-13568,84992,-185088,-272640,2150656,-4009472,2653952]),(⟨1,0,3⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨1,0,4⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨1,0,5⟩,[-256,2304,1536,-32256,2816,91392]),(⟨1,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[-256,5376,-40704,123136,112896,-2165504,7485184,-12511488,10137600,-2949632]),(⟨1,1,1⟩,[0,1536,-26112,152064,-348672,47616,1181184,-1921536,913920]),(⟨1,1,2⟩,[256,-3840,17152,-14592,-78080,169728,52480,-274176]),(⟨1,1,3⟩,[0,-1024,13312,-43008,-6144,158720,-121856]),(⟨1,1,4⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,2,0⟩,[0,768,-13568,84992,-185088,-272640,2150656,-4009472,2653952]),(⟨1,2,1⟩,[256,-3840,17152,-14592,-78080,169728,52480,-274176]),(⟨1,2,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨1,2,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,3,0⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨1,3,1⟩,[0,-1024,13312,-43008,-6144,158720,-121856]),(⟨1,3,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,4,0⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨1,4,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[-256,2304,1536,-32256,2816,91392]),(⟨1,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-256,4608,-27392,38912,328448,-2244352,6900480,-11598336,9590272,-2550016]),(⟨2,0,1⟩,[0,768,-13568,84992,-185088,-272640,2150656,-4009472,2653952]),(⟨2,0,2⟩,[512,-7936,34816,3840,-427520,1265408,-1393664,327936]),(⟨2,0,3⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨2,0,4⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨2,0,5⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[0,768,-13568,84992,-185088,-272640,2150656,-4009472,2653952]),(⟨2,1,1⟩,[256,-3840,17152,-14592,-78080,169728,52480,-274176]),(⟨2,1,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,1,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[512,-7936,34816,3840,-427520,1265408,-1393664,327936]),(⟨2,2,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,0⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨2,3,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,4,0⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨2,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[256,-3584,8960,97792,-741376,1937920,-1533184,-1645056,2484480]),(⟨3,0,1⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨3,0,2⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨3,0,3⟩,[-512,6656,-5120,-150528,456192,-306688]),(⟨3,0,4⟩,[-256,3072,512,-74752,153344]),(⟨3,1,0⟩,[512,-8192,33536,43776,-659456,1836544,-2073856,696064]),(⟨3,1,1⟩,[0,-1024,13312,-43008,-6144,158720,-121856]),(⟨3,1,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[0,-1280,17664,-66048,-26112,497408,-618240]),(⟨3,2,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,3,0⟩,[-512,6656,-5120,-150528,456192,-306688]),(⟨3,4,0⟩,[-256,3072,512,-74752,153344]),(⟨4,0,0⟩,[768,-11904,44032,121728,-1258752,3447936,-3957248,1367680]),(⟨4,0,1⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨4,0,2⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨4,0,3⟩,[-256,3072,512,-74752,153344]),(⟨4,1,0⟩,[384,-7168,40576,-43008,-310656,998400,-891520]),(⟨4,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨4,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-512,5888,-8192,-71168,178688,-55552]),(⟨4,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[-256,3072,512,-74752,153344]),(⟨5,0,0⟩,[128,-3328,23168,-23040,-317056,1150720,-1174656]),(⟨5,0,1⟩,[-256,2304,1536,-32256,2816,91392]),(⟨5,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[-256,2304,1536,-32256,2816,91392]),(⟨5,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-512,5888,0,-144896,367104,-178432]),(⟨6,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,3072,512,-74752,153344])]


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
    (Poly.add (Poly.scale (K.ofRat r276) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 3).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r274*r275 : ℚ)=r276 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 3 r274 r275 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=3 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C048

#print axioms Coulomb8.Columns.C048.sound
