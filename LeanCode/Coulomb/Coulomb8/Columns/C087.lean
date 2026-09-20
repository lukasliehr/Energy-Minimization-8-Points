import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C087

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 2146304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -1703936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 28393472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -574160896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -1638989824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 24415371264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -18060247040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 421127323648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -145635196928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 1859258941440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -2510087667712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 2328399511552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1272021155840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 297277915136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -22204121088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 425984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -44679168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 352845824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -1465843712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 1476001792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 18757419008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -128802750464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 471254351872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -24417959936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 319939461120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -3033368756224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 2717986422784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -1311899582464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 25250430976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -3538944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 34504704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -107479040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -588054528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 6928433152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -30437605376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 75657248768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -103292993536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 8075280384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 316135604224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -745762586624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 798340481024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -47384330240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -6356992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 78872576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -448069632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 714637312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 5742919680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -6176571392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 3144548352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -364620283904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 5153030144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -680213512192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 378427342848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -23736320000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 180224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 32768, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -143507456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 777977856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -72646656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -5746917376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 38384992256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -117849882624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 236160663552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -288467288064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 22490955776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 3244032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -31375360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 93454336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 53182464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -3615948800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 12177145856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -25525354496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 36986503168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -1457946624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -609239040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -12189696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 47316992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 83427328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -1308688384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 5064491008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -12550799360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 22169223168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -18862538752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 1736704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -33849344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 47742976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -264175616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 5507121152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -3875864576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -41217753088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 227665346560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -708686479360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1517985300480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -310009757696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1832128610304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -97972584448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -5144576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 63602688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -383320064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 140476416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1334902784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -19349962752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 75058905088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -173277609984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 244219740160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -145613488128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -98765832192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 22400761856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 46366720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -356024320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 1328807936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -1369047040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -8497856512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 47857074176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -143391260672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 284095545344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -19459768320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 24040734720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -2768896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 73138176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -683933696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 3181936640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -7154171904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 801226752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 28231073792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -295256064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 77725696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -236388352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 374276096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -181534720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -1059454976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 3711139840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -31490048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 4489216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -4259840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -54886400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 1697251328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -9429254144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 25603735552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -34220736512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1945698304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 67637510144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -5079498752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 3477045248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 7307264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -73826304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 293470208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 81133568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -4733206528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 17729650688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -33103151104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 30807293952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 4937449472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -4233723904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -4063232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 86114304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -536936448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 28508160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -86638592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -609878016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 8177090560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -37912576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 11272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -308936704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 162004992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -473169920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -3690463232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 39256064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 2424832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -30670848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 148111360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -3014656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -2670329856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 11443896320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -26633568256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 42092396544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -34012856320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -7274496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 104792064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -806289408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 3970301952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -14620164096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 6001655808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -74648518656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 1867972608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 45564493824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -5344788480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -98304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 29786112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -261980160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 10944512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -3972726784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 7507869696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -4211015680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -3545399296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 69123473408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -7671152640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -3375104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 3538944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -34078720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 158859264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -12320768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 3407872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -7892107264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 718798848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 2005794816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -20316160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -66158592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 326107136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -644284416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -687865856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 6054543360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -634388480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -1500872704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 4370464768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -36667392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -19529728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 18743296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -406257664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 321323008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 1133379584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -152436736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 1465090048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -294912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -4325376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 3932160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -901644288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 3067871232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -1274806272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -9629073408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 1913978880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -2752512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 38010880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -85458944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -335413248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 105381888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1239154688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -4813488128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 54853632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 1073152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -851968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 14196736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -287080448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -819494912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 12207685632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -9030123520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 210563661824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -72817598464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 929629470720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -1255043833856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 1164199755776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -636010577920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 148638957568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -11102060544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 212992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -22339584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 176422912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -732921856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 738000896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 9378709504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -64401375232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 235627175936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -12208979968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 159969730560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -1516684378112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 1358993211392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -655949791232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 12625215488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -1769472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 17252352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -53739520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -294027264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 3464216576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -15218802688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 37828624384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -51646496768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 4037640192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 158067802112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -372881293312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 399170240512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -23692165120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -3178496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 39436288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -224034816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 357318656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 2871459840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -3088285696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 1572274176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -182310141952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 2576515072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -340106756096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 189213671424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -11868160000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 90112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 16384, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -71753728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 388988928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -36323328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -2873458688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 19192496128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -58924941312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 118080331776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -144233644032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 11245477888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 1622016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -15687680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 46727168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 26591232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -1807974400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 6088572928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -12762677248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 18493251584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -728973312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -304619520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 540672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -6094848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 23658496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 41713664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -654344192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 2532245504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -6275399680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 11084611584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -9431269376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 868352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -16924672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 23871488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -132087808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 2753560576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -1937932288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -20608876544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 113832673280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -354343239680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 758992650240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -155004878848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 916064305152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -48986292224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -2572288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 31801344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -191660032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 70238208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 667451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -9674981376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 37529452544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -86638804992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 122109870080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -72806744064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -49382916096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 11200380928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 23183360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -178012160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 664403968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -684523520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -4248928256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 23928537088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -71695630336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 142047772672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -9729884160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 12020367360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -1384448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 36569088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -341966848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 1590968320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -3577085952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 400613376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 14115536896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -147628032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 38862848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -118194176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 187138048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -90767360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -529727488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 1855569920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -15745024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 2244608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -2129920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -27443200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 848625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -4714627072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 12801867776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -17110368256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 972849152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 33818755072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -2539749376, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 1738522624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 3653632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -36913152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 146735104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 40566784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -2366603264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 8864825344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -16551575552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 15403646976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 2468724736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -2116861952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -180224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -2031616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 43057152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -268468224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 14254080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -43319296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -304939008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 4088545280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -18956288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -154468352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 81002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -1845231616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 19628032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 1212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -15335424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 74055680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -1507328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -1335164928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 5721948160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -13316784128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 21046198272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -17006428160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -3637248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 52396032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -403144704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 1985150976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -7310082048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 3000827904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -37324259328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 933986304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 22782246912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -2672394240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -49152, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 14893056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -130990080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 5472256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -1986363392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 3753934848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -2105507840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -1772699648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 34561736704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -3835576320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -1687552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 1769472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -17039360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 79429632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -6160384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 1703936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -3946053632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 359399424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 1002897408, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -10158080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -33079296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 163053568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -322142208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -343932928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 3027271680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -317194240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -750436352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 2185232384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -18333696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -9764864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 9371648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -203128832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 160661504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 566689792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -76218368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 732545024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 1966080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -450822144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 1533935616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -637403136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -4814536704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 956989440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -1376256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 19005440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -42729472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -167706624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 52690944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -619577344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -2406744064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 27426816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15],[r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30],[r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44],[r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57],[r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69],[r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80],[r58,r81,r82,r83,r84,r85,r86,r87,r88,r89],[],[],[],[],[],[],[r58,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115],[r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127],[r16,r128,r129,r130,r91,r131,r132,r133,r134,r135,r136],[r58,r81,r137,r138,r139,r140,r141,r142,r143,r144],[],[],[],[],[],[],[r145,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156],[r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167],[r168,r169,r170,r171,r172,r173,r174,r175,r176,r177],[r116,r178,r179,r180,r181,r182,r183,r184,r185],[],[],[],[],[],[r0,r186,r187,r188,r189,r190,r191,r192,r193,r194],[r116,r178,r195,r196,r137,r197,r198,r199,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r45,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,29687808],[r168,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220],[0,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230],[],[],[],[],[],[],[],[r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241],[r58,r242,r243,r244,r245,r246,r247,r248,r249,r250],[r116,r178,r195,r196,r137,r197,r198,r199,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r45,r251,r252,r253,r254,r255,r256,r257,r258,r259],[r45,r260,r261,r262,r263,r264,r265,r266,r267],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r58,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,0,1⟩,[r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨0,0,2⟩,[r116,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,0,3⟩,[r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,0,4⟩,[r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,0,5⟩,[r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨0,0,6⟩,[r324,r347,r348,r349,r350,r351,r352,r353,r354,r355]),(⟨0,1,0⟩,[r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨0,1,1⟩,[r324,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,1,2⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨0,1,3⟩,[r168,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,1,4⟩,[r283,r393,r394,r395,r357,r396,r397,r398,r399,r400,r401]),(⟨0,1,5⟩,[r324,r347,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨0,2,0⟩,[r116,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,2,1⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨0,2,2⟩,[r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨0,2,3⟩,[r221,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨0,2,4⟩,[r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨0,2,5⟩,[r168,r442,r443,r157,r444,r445,r446,r447,r448]),(⟨0,3,0⟩,[r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,3,1⟩,[r168,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,3,2⟩,[r221,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨0,3,3⟩,[r58,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨0,3,4⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨0,4,0⟩,[r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,4,1⟩,[r283,r393,r394,r395,r357,r396,r397,r398,r399,r400,r401]),(⟨0,4,2⟩,[r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨0,4,3⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨0,5,0⟩,[r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨0,5,1⟩,[r324,r347,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨0,5,2⟩,[r168,r442,r443,r157,r444,r445,r446,r447,r448]),(⟨0,6,0⟩,[r324,r347,r348,r349,r350,r351,r352,r353,r354,r355]),(⟨1,0,0⟩,[r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨1,0,1⟩,[r324,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨1,0,2⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨1,0,3⟩,[r168,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨1,0,4⟩,[r283,r393,r394,r395,r357,r396,r397,r398,r399,r400,r401]),(⟨1,0,5⟩,[r324,r347,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨1,1,0⟩,[r324,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨1,1,1⟩,[0,r311,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472,14843904]),(⟨1,1,2⟩,[r432,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,1,3⟩,[0,r0,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨1,2,0⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨1,2,1⟩,[r432,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,2,2⟩,[r70,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502]),(⟨1,2,3⟩,[r324,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨1,2,4⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨1,3,0⟩,[r168,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨1,3,1⟩,[0,r0,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨1,3,2⟩,[r324,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨1,4,0⟩,[r283,r393,r394,r395,r357,r396,r397,r398,r399,r400,r401]),(⟨1,4,2⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨1,5,0⟩,[r324,r347,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨2,0,0⟩,[r116,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨2,0,1⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨2,0,2⟩,[r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨2,0,3⟩,[r221,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨2,0,4⟩,[r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨2,0,5⟩,[r168,r442,r443,r157,r444,r445,r446,r447,r448]),(⟨2,1,0⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381]),(⟨2,1,1⟩,[r432,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨2,1,2⟩,[r70,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502]),(⟨2,1,3⟩,[r324,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨2,1,4⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨2,2,0⟩,[r410,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨2,2,1⟩,[r70,r493,r494,r495,r496,r497,r498,r499,r500,r501,r502]),(⟨2,2,2⟩,[r311,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨2,2,3⟩,[r311,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨2,3,0⟩,[r221,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨2,3,1⟩,[r324,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨2,3,2⟩,[r311,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨2,4,0⟩,[r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨2,4,1⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨2,5,0⟩,[r168,r442,r443,r157,r444,r445,r446,r447,r448]),(⟨3,0,0⟩,[r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨3,0,1⟩,[r168,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨3,0,2⟩,[r221,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨3,0,3⟩,[r58,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨3,0,4⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨3,1,0⟩,[r168,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨3,1,1⟩,[0,r0,r484,r485,r486,r487,r488,r489,r490,r491,r492]),(⟨3,1,2⟩,[r324,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨3,2,0⟩,[r221,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨3,2,1⟩,[r324,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨3,2,2⟩,[r311,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨3,3,0⟩,[r58,r449,r450,r451,r452,r453,r454,r455,r456,r457]),(⟨3,4,0⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨4,0,0⟩,[r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨4,0,1⟩,[r283,r393,r394,r395,r357,r396,r397,r398,r399,r400,r401]),(⟨4,0,2⟩,[r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨4,0,3⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨4,1,0⟩,[r283,r393,r394,r395,r357,r396,r397,r398,r399,r400,r401]),(⟨4,1,2⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨4,2,0⟩,[r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨4,2,1⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨4,3,0⟩,[r168,r442,r458,r459,r402,r460,r461,r462,32768]),(⟨5,0,0⟩,[r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨5,0,1⟩,[r324,r347,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨5,0,2⟩,[r168,r442,r443,r157,r444,r445,r446,r447,r448]),(⟨5,1,0⟩,[r324,r347,r402,r403,r404,r405,r406,r407,r408,r409]),(⟨5,2,0⟩,[r168,r442,r443,r157,r444,r445,r446,r447,r448]),(⟨6,0,0⟩,[r324,r347,r348,r349,r350,r351,r352,r353,r354,r355])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r529) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r529) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[32768,-1007616,12926976,-90775552,384811008,-1013563392,1549565952,-548028416,-4087873536,12860989440,-19206881280,12796387328,-1448624128]),(⟨2,0,2⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨2,0,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,1,0⟩,[32768,-1007616,12926976,-90775552,384811008,-1013563392,1549565952,-548028416,-4087873536,12860989440,-19206881280,12796387328,-1448624128]),(⟨2,1,1⟩,[16384,-671744,10567680,-85934080,404783104,-1156349952,1954316288,-1170243584,-4215324672,15721742336,-24150654976,14835236864]),(⟨2,1,2⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,2,0⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨2,2,1⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨2,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,0,0⟩,[32768,-1007616,11878400,-62726144,65519616,1048985600,-7013105664,24173723648,-56561762304,95957491712,-110048165888,65760747520,-7291813888]),(⟨3,0,1⟩,[16384,-671744,10305536,-76234752,270041088,-165969920,-2511568896,12470681600,-34665447424,66119974912,-79763718144,44755042304]),(⟨3,0,2⟩,[-40960,1114112,-10543104,32636928,99205120,-1063518208,3645784064,-7327580160,8591826944,-1658650624,-5531459584]),(⟨3,0,3⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨3,1,0⟩,[16384,-671744,10305536,-76234752,270041088,-165969920,-2511568896,12470681600,-34665447424,66119974912,-79763718144,44755042304]),(⟨3,1,1⟩,[0,0,-393216,9437184,-76021760,170917888,670826496,-3582984192,2478309376,9626976256,-13055164416]),(⟨3,2,0⟩,[-40960,1114112,-10543104,32636928,99205120,-1063518208,3645784064,-7327580160,8591826944,-1658650624,-5531459584]),(⟨3,2,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨3,3,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨4,0,0⟩,[8192,-335872,5021696,-33267712,67649536,412205056,-3488727040,13055803392,-32557785088,58259103744,-67688390656,37337423872]),(⟨4,0,1⟩,[-40960,1114112,-11853824,63045632,-172376064,130809856,842416128,-3214016512,2519523328,6693257216,-10073104384]),(⟨4,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-40960,1114112,-11853824,63045632,-172376064,130809856,842416128,-3214016512,2519523328,6693257216,-10073104384]),(⟨4,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-40960,1114112,-10412032,29491200,125943808,-1148452864,3619307520,-6670123008,7825842176,-2781675520,-3675348992]),(⟨5,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨5,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,2,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[32768,-1007616,12926976,-90775552,384811008,-1013563392,1549565952,-548028416,-4087873536,12860989440,-19206881280,12796387328,-1448624128]),(⟨1,0,3⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,0,4⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨1,0,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[0,131072,-4030464,51707904,-363102208,1539244032,-4054253568,6198263808,-2192113664,-16351494144,51443957760,-76827525120,51185549312,-5794496512]),(⟨1,1,1⟩,[0,32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨1,1,2⟩,[8192,-499712,9740288,-89858048,441991168,-1177501696,1496203264,313049088,-5891448832,14153605120,-14826004480,4496973824]),(⟨1,1,3⟩,[0,-65536,2031616,-23330816,128712704,-387842048,775028736,-1020526592,-1352925184,8545304576,-9350742016]),(⟨1,2,0⟩,[32768,-974848,11583488,-69640192,212942848,-203997184,-763133952,3360604160,-6428360704,4430340096,12236603392,-35504922624,28221849600]),(⟨1,2,1⟩,[8192,-335872,5283840,-43491328,214974464,-685129728,1316896768,-479215616,-4737490944,10924810240,-7583227904,-6823936]),(⟨1,2,2⟩,[-81920,2228224,-23445504,119799808,-299663360,259522560,449085440,-1891893248,3146366976,-1375338496,-1460322304]),(⟨1,2,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[8192,-499712,9740288,-89858048,441991168,-1177501696,1496203264,313049088,-5891448832,14153605120,-14826004480,4496973824]),(⟨1,3,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,3,2⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,4,0⟩,[-40960,1048576,-9560064,33423360,5619712,-343015424,973094912,-1309016064,-545726464,6734610432,-8224792576]),(⟨1,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[32768,-942080,10387456,-49324032,5734400,1175044096,-7031685120,23610966016,-54977921024,93685227520,-109950238720,72741019648,-16787406848,1192984576]),(⟨2,0,1⟩,[40960,-1327104,17408000,-117932032,420397056,-523206656,-1976942592,12234915840,-35716390912,69496324096,-86586417152,54739566592,-7557251072]),(⟨2,0,2⟩,[-24576,360448,1728512,-66650112,553009152,-2283601920,5427085312,-7638482944,3513786368,12327288832,-26734174208,15436546048]),(⟨2,0,3⟩,[-57344,1622016,-17129472,80281600,-116375552,-444825600,2720284672,-7695958016,13006577664,-9175515136,-1043259392]),(⟨2,0,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,1,0⟩,[40960,-1294336,16064512,-96796672,248528896,286359552,-4289642496,16143548416,-38056878080,61065674752,-55142932480,6438256640,22113222656]),(⟨2,1,1⟩,[16384,-671744,10436608,-83574784,399015936,-1280081920,2895151104,-3109584896,-5995282432,25205063680,-28590456832,8939356160]),(⟨2,1,2⟩,[-40960,1114112,-11984896,66191360,-203309056,299630592,277495808,-2260860928,3105153024,1558380544,-4442382336]),(⟨2,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,2,0⟩,[-24576,360448,1728512,-67174400,565592064,-2390556672,5766823936,-7532576768,883957760,15391227904,-22242074624,8012103680]),(⟨2,2,1⟩,[-40960,1114112,-11984896,66191360,-203309056,299630592,277495808,-2260860928,3105153024,1558380544,-4442382336]),(⟨2,2,2⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-57344,1622016,-17129472,80281600,-116375552,-444825600,2720284672,-7695958016,13006577664,-9175515136,-1043259392]),(⟨2,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,0,0⟩,[40960,-1327104,16359424,-89882624,101105664,1539342336,-10539614208,36956667904,-88190279680,152592826368,-177427701760,107703926784,-13400440832]),(⟨3,0,1⟩,[16384,-671744,10174464,-73351168,251691008,-182747136,-1910472704,10425434112,-33815576576,72539357184,-88695619584,46283603968]),(⟨3,0,2⟩,[-81920,2228224,-22265856,92536832,-50626560,-933756928,3870326784,-8273526784,10165010432,-2346319872,-6261620736]),(⟨3,0,3⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨3,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[16384,-835584,14630912,-120242176,491290624,-782073856,-1391427584,11323604992,-37599363072,78832091136,-91446296576,43362959360]),(⟨3,1,1⟩,[0,0,-393216,9437184,-76021760,170917888,670826496,-3582984192,2478309376,9626976256,-13055164416]),(⟨3,1,2⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,2,0⟩,[-81920,2228224,-22265856,92536832,-50626560,-933756928,3870326784,-8273526784,10165010432,-2346319872,-6261620736]),(⟨3,2,2⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨3,3,0⟩,[-16384,671744,-9240576,50397184,-43220992,-680820736,3189702656,-7041384448,9961586688,-7575158784]),(⟨3,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-32768,696320,-3817472,-13983744,215875584,-715046912,-15958016,6587564032,-24828674048,54864650240,-70271909888,37938733056]),(⟨4,0,1⟩,[-40960,1114112,-11853824,63045632,-172376064,130809856,842416128,-3214016512,2519523328,6693257216,-10073104384]),(⟨4,0,2⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨5,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨5,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,2,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928])]

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[32768,-1007616,12926976,-90775552,384811008,-1013563392,1549565952,-548028416,-4087873536,12860989440,-19206881280,12796387328,-1448624128]),(⟨0,2,2⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨0,2,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨0,2,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,3,0⟩,[32768,-1007616,11878400,-62726144,65519616,1048985600,-7013105664,24173723648,-56561762304,95957491712,-110048165888,65760747520,-7291813888]),(⟨0,3,1⟩,[16384,-671744,10305536,-76234752,270041088,-165969920,-2511568896,12470681600,-34665447424,66119974912,-79763718144,44755042304]),(⟨0,3,2⟩,[-40960,1114112,-10543104,32636928,99205120,-1063518208,3645784064,-7327580160,8591826944,-1658650624,-5531459584]),(⟨0,3,3⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨0,4,0⟩,[8192,-335872,5021696,-33267712,67649536,412205056,-3488727040,13055803392,-32557785088,58259103744,-67688390656,37337423872]),(⟨0,4,1⟩,[-40960,1114112,-11853824,63045632,-172376064,130809856,842416128,-3214016512,2519523328,6693257216,-10073104384]),(⟨0,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[-40960,1114112,-10412032,29491200,125943808,-1148452864,3619307520,-6670123008,7825842176,-2781675520,-3675348992]),(⟨0,5,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,5,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨0,6,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨1,0,0⟩,[-32768,1138688,-16498688,128376832,-551206912,890568704,3925934080,-32477298688,121844400128,-308252680192,569002311680,-756437786624,661595176960,-304468836352,31528878080]),(⟨1,0,1⟩,[-8192,499712,-10543104,111108096,-659456000,2187296768,-2726477824,-9598943232,62944829440,-191566471168,389937864704,-537286877184,446924636160,-167236780032]),(⟨1,0,2⟩,[73728,-2252800,27189248,-160833536,418594816,324943872,-6024478720,21653209088,-44909355008,56732557312,-27142299648,-33622433792,44113592320]),(⟨1,0,3⟩,[24576,-1105920,18292736,-147628032,615104512,-1079951360,-1361297408,12917981184,-39987716096,77369286656,-88787738624,45276585984]),(⟨1,0,4⟩,[-40960,1048576,-9560064,33423360,5619712,-343015424,973094912,-1309016064,-545726464,6734610432,-8224792576]),(⟨1,0,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[-8192,499712,-10543104,111108096,-659456000,2187296768,-2726477824,-9598943232,62944829440,-191566471168,389937864704,-537286877184,446924636160,-167236780032]),(⟨1,1,1⟩,[0,65536,-2555904,38600704,-306249728,1471283200,-4749393920,10910564352,-14781906944,-8119320576,84602060800,-154306281472,99738648576]),(⟨1,1,2⟩,[8192,-499712,9740288,-90382336,454574080,-1284456448,1835941888,418955264,-8521277440,17217544192,-10333904896,-2927468544]),(⟨1,1,3⟩,[0,-65536,2031616,-23330816,128712704,-387842048,775028736,-1020526592,-1352925184,8545304576,-9350742016]),(⟨1,2,0⟩,[73728,-2252800,27189248,-160833536,418594816,324943872,-6024478720,21653209088,-44909355008,56732557312,-27142299648,-33622433792,44113592320]),(⟨1,2,1⟩,[16384,-835584,15024128,-133349376,656965632,-1862631424,2813100032,-166166528,-10628939776,25078415360,-22409232384,4490149888]),(⟨1,2,2⟩,[-114688,3145728,-32948224,159907840,-295403520,-428867584,3000795136,-4734844928,-1516421120,14173601792,-13415858176]),(⟨1,2,3⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[32768,-1441792,23314432,-180895744,682754048,-667746304,-4850024448,25973784576,-72545501184,135628390400,-156476129280,82614009856]),(⟨1,3,1⟩,[0,-65536,1769472,-17039360,79429632,-301858816,1419378688,-3946053632,359399424,17049255936,-20549795840]),(⟨1,3,2⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,4,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨1,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[24576,-573440,3874816,10076160,-290619392,1823096832,-5703909376,7813758976,10159022080,-81529749504,228543668224,-387718332416,378951680000,-160249298944]),(⟨2,0,1⟩,[40960,-1294336,16195584,-100466688,286015488,138510336,-4413636608,19236847616,-48157810688,69807652864,-33427841024,-51265404928,62510923776]),(⟨2,0,2⟩,[-24576,360448,1728512,-67174400,565592064,-2390556672,5766823936,-7532576768,883957760,15391227904,-22242074624,8012103680]),(⟨2,0,3⟩,[-57344,1622016,-17129472,80281600,-116375552,-444825600,2720284672,-7695958016,13006577664,-9175515136,-1043259392]),(⟨2,0,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,1,0⟩,[40960,-1294336,16195584,-100466688,286015488,138510336,-4413636608,19236847616,-48157810688,69807652864,-33427841024,-51265404928,62510923776]),(⟨2,1,1⟩,[16384,-671744,10436608,-84099072,411598848,-1387036672,3234889728,-3003678720,-8625111040,28269002752,-24098357248,1514913792]),(⟨2,1,2⟩,[-40960,1114112,-11984896,66191360,-203309056,299630592,277495808,-2260860928,3105153024,1558380544,-4442382336]),(⟨2,1,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,2,0⟩,[-24576,360448,1728512,-67174400,565592064,-2390556672,5766823936,-7532576768,883957760,15391227904,-22242074624,8012103680]),(⟨2,2,1⟩,[-81920,2228224,-23707648,126091264,-353140736,429391872,502038528,-3206807552,4678336512,870711296,-5172543488]),(⟨2,2,2⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[-98304,2736128,-27541504,109772800,9568256,-1593278464,6339592192,-14366081024,20832419840,-11957190656,-4718608384]),(⟨2,3,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,3,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨2,4,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨3,0,0⟩,[81920,-2605056,31965184,-181075968,306757632,2068283392,-15800958976,55249272832,-126671273984,204895043584,-216806604800,109586415616,2491301888]),(⟨3,0,1⟩,[16384,-835584,14630912,-120242176,491290624,-782073856,-1391427584,11323604992,-37599363072,78832091136,-91446296576,43362959360]),(⟨3,0,2⟩,[-114688,3145728,-31637504,129499136,-19628032,-1707081728,6395559936,-10459021312,4736237568,12079595520,-16361046016]),(⟨3,0,3⟩,[-16384,671744,-9240576,50397184,-43220992,-680820736,3189702656,-7041384448,9961586688,-7575158784]),(⟨3,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[16384,-835584,14630912,-120242176,491290624,-782073856,-1391427584,11323604992,-37599363072,78832091136,-91446296576,43362959360]),(⟨3,1,1⟩,[0,0,-393216,9437184,-76021760,170917888,670826496,-3582984192,2478309376,9626976256,-13055164416]),(⟨3,1,2⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,2,0⟩,[-114688,3145728,-31637504,129499136,-19628032,-1707081728,6395559936,-10459021312,4736237568,12079595520,-16361046016]),(⟨3,2,1⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨3,2,2⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨3,3,0⟩,[-32768,1212416,-15335424,74055680,-1507328,-1335164928,5721948160,-13316784128,21046198272,-17006428160]),(⟨3,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-16384,90112,4734976,-71753728,388988928,-617496576,-2873458688,19192496128,-58924941312,118080331776,-144233644032,78718345216]),(⟨4,0,1⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,0,2⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨5,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨5,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,2,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-32768,1138688,-16498688,128376832,-551206912,890568704,3925934080,-32477298688,121844400128,-308252680192,569002311680,-756437786624,661595176960,-304468836352,31528878080]),(⟨0,1,1⟩,[-8192,499712,-10543104,111108096,-659456000,2187296768,-2726477824,-9598943232,62944829440,-191566471168,389937864704,-537286877184,446924636160,-167236780032]),(⟨0,1,2⟩,[73728,-2252800,27189248,-160833536,418594816,324943872,-6024478720,21653209088,-44909355008,56732557312,-27142299648,-33622433792,44113592320]),(⟨0,1,3⟩,[24576,-1105920,18292736,-147628032,615104512,-1079951360,-1361297408,12917981184,-39987716096,77369286656,-88787738624,45276585984]),(⟨0,1,4⟩,[-40960,1048576,-9560064,33423360,5619712,-343015424,973094912,-1309016064,-545726464,6734610432,-8224792576]),(⟨0,1,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,2,0⟩,[24576,-573440,3874816,10076160,-290619392,1823096832,-5703909376,7813758976,10159022080,-81529749504,228543668224,-387718332416,378951680000,-160249298944]),(⟨0,2,1⟩,[40960,-1294336,16195584,-100466688,286015488,138510336,-4413636608,19236847616,-48157810688,69807652864,-33427841024,-51265404928,62510923776]),(⟨0,2,2⟩,[-24576,360448,1728512,-67174400,565592064,-2390556672,5766823936,-7532576768,883957760,15391227904,-22242074624,8012103680]),(⟨0,2,3⟩,[-57344,1622016,-17129472,80281600,-116375552,-444825600,2720284672,-7695958016,13006577664,-9175515136,-1043259392]),(⟨0,2,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,3,0⟩,[81920,-2605056,31965184,-181075968,306757632,2068283392,-15800958976,55249272832,-126671273984,204895043584,-216806604800,109586415616,2491301888]),(⟨0,3,1⟩,[16384,-835584,14630912,-120242176,491290624,-782073856,-1391427584,11323604992,-37599363072,78832091136,-91446296576,43362959360]),(⟨0,3,2⟩,[-114688,3145728,-31637504,129499136,-19628032,-1707081728,6395559936,-10459021312,4736237568,12079595520,-16361046016]),(⟨0,3,3⟩,[-16384,671744,-9240576,50397184,-43220992,-680820736,3189702656,-7041384448,9961586688,-7575158784]),(⟨0,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,4,0⟩,[-16384,90112,4734976,-71753728,388988928,-617496576,-2873458688,19192496128,-58924941312,118080331776,-144233644032,78718345216]),(⟨0,4,1⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨0,4,2⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨0,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨0,5,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,5,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨0,6,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨1,0,0⟩,[-32768,1138688,-16498688,128376832,-551206912,890568704,3925934080,-32477298688,121844400128,-308252680192,569002311680,-756437786624,661595176960,-304468836352,31528878080]),(⟨1,0,1⟩,[-8192,499712,-10543104,111108096,-659456000,2187296768,-2726477824,-9598943232,62944829440,-191566471168,389937864704,-537286877184,446924636160,-167236780032]),(⟨1,0,2⟩,[73728,-2252800,27189248,-160833536,418594816,324943872,-6024478720,21653209088,-44909355008,56732557312,-27142299648,-33622433792,44113592320]),(⟨1,0,3⟩,[24576,-1105920,18292736,-147628032,615104512,-1079951360,-1361297408,12917981184,-39987716096,77369286656,-88787738624,45276585984]),(⟨1,0,4⟩,[-40960,1048576,-9560064,33423360,5619712,-343015424,973094912,-1309016064,-545726464,6734610432,-8224792576]),(⟨1,0,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[-16384,868352,-17055744,170508288,-955809792,2835349504,-1398702080,-25396150272,128081772544,-366781448192,728431771648,-997746229248,842663723008,-328679063552]),(⟨1,1,1⟩,[0,98304,-3768320,56066048,-440631296,2133000192,-7186087936,17912496128,-27223326720,-7807991808,137760636928,-260311252992,169806823424]),(⟨1,1,2⟩,[16384,-835584,15024128,-133873664,669548544,-1969586176,3152838656,-60260352,-13258768384,28142354432,-17917132800,-2934292480]),(⟨1,1,3⟩,[0,-65536,1900544,-20185088,101974016,-302907392,801505280,-1677983744,-586940416,9668329472,-11206852608]),(⟨1,2,0⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨1,2,1⟩,[16384,-835584,14893056,-130990080,651198464,-1986363392,3753934848,-2105507840,-12408897536,34561736704,-26849034240,-1405730816]),(⟨1,2,2⟩,[-114688,3145728,-33079296,163053568,-322142208,-343932928,3027271680,-5392302080,-750436352,15296626688,-15271968768]),(⟨1,2,3⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨1,3,1⟩,[0,-65536,1769472,-17039360,79429632,-301858816,1419378688,-3946053632,359399424,17049255936,-20549795840]),(⟨1,3,2⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,4,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨1,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[24576,-573440,3874816,10076160,-290619392,1823096832,-5703909376,7813758976,10159022080,-81529749504,228543668224,-387718332416,378951680000,-160249298944]),(⟨2,0,1⟩,[40960,-1294336,16195584,-100466688,286015488,138510336,-4413636608,19236847616,-48157810688,69807652864,-33427841024,-51265404928,62510923776]),(⟨2,0,2⟩,[-24576,360448,1728512,-67174400,565592064,-2390556672,5766823936,-7532576768,883957760,15391227904,-22242074624,8012103680]),(⟨2,0,3⟩,[-57344,1622016,-17129472,80281600,-116375552,-444825600,2720284672,-7695958016,13006577664,-9175515136,-1043259392]),(⟨2,0,4⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,1,0⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨2,1,1⟩,[16384,-835584,14893056,-130990080,651198464,-1986363392,3753934848,-2105507840,-12408897536,34561736704,-26849034240,-1405730816]),(⟨2,1,2⟩,[-114688,3145728,-33079296,163053568,-322142208,-343932928,3027271680,-5392302080,-750436352,15296626688,-15271968768]),(⟨2,1,3⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨2,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[-65536,1392640,-7110656,-47890432,713818112,-3517808640,9239592960,-14000816128,8613068800,11996774400,-24825593856,8613412864]),(⟨2,2,1⟩,[-81920,2228224,-23707648,126091264,-353140736,429391872,502038528,-3206807552,4678336512,870711296,-5172543488]),(⟨2,2,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨2,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨2,3,1⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨2,3,2⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨2,4,0⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨2,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨3,0,0⟩,[81920,-2605056,31965184,-181075968,306757632,2068283392,-15800958976,55249272832,-126671273984,204895043584,-216806604800,109586415616,2491301888]),(⟨3,0,1⟩,[16384,-835584,14630912,-120242176,491290624,-782073856,-1391427584,11323604992,-37599363072,78832091136,-91446296576,43362959360]),(⟨3,0,2⟩,[-114688,3145728,-31637504,129499136,-19628032,-1707081728,6395559936,-10459021312,4736237568,12079595520,-16361046016]),(⟨3,0,3⟩,[-16384,671744,-9240576,50397184,-43220992,-680820736,3189702656,-7041384448,9961586688,-7575158784]),(⟨3,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨3,1,1⟩,[0,-65536,1769472,-17039360,79429632,-301858816,1419378688,-3946053632,359399424,17049255936,-20549795840]),(⟨3,1,2⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨3,2,0⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨3,2,1⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨3,2,2⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨3,3,0⟩,[-32768,1212416,-15335424,74055680,-1507328,-1335164928,5721948160,-13316784128,21046198272,-17006428160]),(⟨3,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-16384,90112,4734976,-71753728,388988928,-617496576,-2873458688,19192496128,-58924941312,118080331776,-144233644032,78718345216]),(⟨4,0,1⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,0,2⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨5,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨5,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,2,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1073152,-14483456,99377152,-287080448,-819494912,12207685632,-63210864640,210563661824,-509723189248,929629470720,-1255043833856,1164199755776,-636010577920,148638957568,-11102060544]),(⟨0,0,1⟩,[-40960,1490944,-22339584,176422912,-732921856,738000896,9378709504,-64401375232,235627175936,-598240018432,1119788113920,-1516684378112,1358993211392,-655949791232,88376508416]),(⟨0,0,2⟩,[65536,-1769472,17252352,-53739520,-294027264,3464216576,-15218802688,37828624384,-51646496768,4037640192,158067802112,-372881293312,399170240512,-165845155840]),(⟨0,0,3⟩,[98304,-3178496,39436288,-224034816,357318656,2871459840,-21617999872,77041434624,-182310141952,306605293568,-340106756096,189213671424,-11868160000]),(⟨0,0,4⟩,[-16384,90112,4734976,-71753728,388988928,-617496576,-2873458688,19192496128,-58924941312,118080331776,-144233644032,78718345216]),(⟨0,0,5⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨0,0,6⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨0,1,0⟩,[-40960,1490944,-22339584,176422912,-732921856,738000896,9378709504,-64401375232,235627175936,-598240018432,1119788113920,-1516684378112,1358993211392,-655949791232,88376508416]),(⟨0,1,1⟩,[-16384,868352,-16924672,167100416,-924614656,2753560576,-1937932288,-20608876544,113832673280,-354343239680,758992650240,-1085034151936,916064305152,-342904045568]),(⟨0,1,2⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨0,1,3⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨0,1,4⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨0,1,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,2,0⟩,[65536,-1769472,17252352,-53739520,-294027264,3464216576,-15218802688,37828624384,-51646496768,4037640192,158067802112,-372881293312,399170240512,-165845155840]),(⟨0,2,1⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨0,2,2⟩,[-98304,2244608,-14909440,-27443200,848625664,-4714627072,12801867776,-17110368256,972849152,33818755072,-43175739392,12169658368]),(⟨0,2,3⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨0,2,4⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨0,2,5⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨0,3,0⟩,[98304,-3178496,39436288,-224034816,357318656,2871459840,-21617999872,77041434624,-182310141952,306605293568,-340106756096,189213671424,-11868160000]),(⟨0,3,1⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨0,3,2⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨0,3,3⟩,[-32768,1212416,-15335424,74055680,-1507328,-1335164928,5721948160,-13316784128,21046198272,-17006428160]),(⟨0,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,4,0⟩,[-16384,90112,4734976,-71753728,388988928,-617496576,-2873458688,19192496128,-58924941312,118080331776,-144233644032,78718345216]),(⟨0,4,1⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨0,4,2⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨0,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨0,5,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,5,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨0,6,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376]),(⟨1,0,0⟩,[-40960,1490944,-22339584,176422912,-732921856,738000896,9378709504,-64401375232,235627175936,-598240018432,1119788113920,-1516684378112,1358993211392,-655949791232,88376508416]),(⟨1,0,1⟩,[-16384,868352,-16924672,167100416,-924614656,2753560576,-1937932288,-20608876544,113832673280,-354343239680,758992650240,-1085034151936,916064305152,-342904045568]),(⟨1,0,2⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨1,0,3⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨1,0,4⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨1,0,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,1,0⟩,[-16384,868352,-16924672,167100416,-924614656,2753560576,-1937932288,-20608876544,113832673280,-354343239680,758992650240,-1085034151936,916064305152,-342904045568]),(⟨1,1,1⟩,[0,98304,-3637248,52396032,-403144704,1985150976,-7310082048,21005795328,-37324259328,933986304,159475728384,-318014914560,210204524544]),(⟨1,1,2⟩,[16384,-835584,14893056,-130990080,651198464,-1986363392,3753934848,-2105507840,-12408897536,34561736704,-26849034240,-1405730816]),(⟨1,1,3⟩,[0,-65536,1769472,-17039360,79429632,-301858816,1419378688,-3946053632,359399424,17049255936,-20549795840]),(⟨1,2,0⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨1,2,1⟩,[16384,-835584,14893056,-130990080,651198464,-1986363392,3753934848,-2105507840,-12408897536,34561736704,-26849034240,-1405730816]),(⟨1,2,2⟩,[-114688,3145728,-33079296,163053568,-322142208,-343932928,3027271680,-5392302080,-750436352,15296626688,-15271968768]),(⟨1,2,3⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨1,3,1⟩,[0,-65536,1769472,-17039360,79429632,-301858816,1419378688,-3946053632,359399424,17049255936,-20549795840]),(⟨1,3,2⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨1,4,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨1,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,0,0⟩,[65536,-1769472,17252352,-53739520,-294027264,3464216576,-15218802688,37828624384,-51646496768,4037640192,158067802112,-372881293312,399170240512,-165845155840]),(⟨2,0,1⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨2,0,2⟩,[-98304,2244608,-14909440,-27443200,848625664,-4714627072,12801867776,-17110368256,972849152,33818755072,-43175739392,12169658368]),(⟨2,0,3⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨2,0,4⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨2,0,5⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨2,1,0⟩,[81920,-2572288,31801344,-191660032,491667456,667451392,-9674981376,37529452544,-86638804992,122109870080,-72806744064,-49382916096,78402666496]),(⟨2,1,1⟩,[16384,-835584,14893056,-130990080,651198464,-1986363392,3753934848,-2105507840,-12408897536,34561736704,-26849034240,-1405730816]),(⟨2,1,2⟩,[-114688,3145728,-33079296,163053568,-322142208,-343932928,3027271680,-5392302080,-750436352,15296626688,-15271968768]),(⟨2,1,3⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨2,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[-98304,2244608,-14909440,-27443200,848625664,-4714627072,12801867776,-17110368256,972849152,33818755072,-43175739392,12169658368]),(⟨2,2,1⟩,[-114688,3145728,-33079296,163053568,-322142208,-343932928,3027271680,-5392302080,-750436352,15296626688,-15271968768]),(⟨2,2,2⟩,[98304,-2162688,13762560,12582912,-450822144,1533935616,-637403136,-4814536704,6698926080,-1146421248]),(⟨2,2,3⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨2,3,0⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨2,3,1⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨2,3,2⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨2,4,0⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨2,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨3,0,0⟩,[98304,-3178496,39436288,-224034816,357318656,2871459840,-21617999872,77041434624,-182310141952,306605293568,-340106756096,189213671424,-11868160000]),(⟨3,0,1⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨3,0,2⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨3,0,3⟩,[-32768,1212416,-15335424,74055680,-1507328,-1335164928,5721948160,-13316784128,21046198272,-17006428160]),(⟨3,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,1,0⟩,[32768,-1441792,23183360,-178012160,664403968,-684523520,-4248928256,23928537088,-71695630336,142047772672,-165408030720,84142571520]),(⟨3,1,1⟩,[0,-65536,1769472,-17039360,79429632,-301858816,1419378688,-3946053632,359399424,17049255936,-20549795840]),(⟨3,1,2⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨3,2,0⟩,[-131072,3653632,-36913152,146735104,40566784,-2366603264,8864825344,-16551575552,15403646976,2468724736,-14818033664]),(⟨3,2,1⟩,[-16384,671744,-9764864,65601536,-203128832,160661504,566689792,-1295712256,732545024,-17547264]),(⟨3,2,2⟩,[98304,-2359296,19005440,-42729472,-167706624,895746048,-619577344,-2406744064,3263791104]),(⟨3,3,0⟩,[-32768,1212416,-15335424,74055680,-1507328,-1335164928,5721948160,-13316784128,21046198272,-17006428160]),(⟨3,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[-16384,90112,4734976,-71753728,388988928,-617496576,-2873458688,19192496128,-58924941312,118080331776,-144233644032,78718345216]),(⟨4,0,1⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,0,2⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,0,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-40960,1048576,-9691136,36569088,-16924672,-341966848,1590968320,-3577085952,400613376,14115536896,-17567735808]),(⟨4,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[16384,-180224,-2031616,43057152,-268468224,698449920,-303235072,-2134573056,4088545280,-2255798272]),(⟨4,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-57344,1622016,-15687680,46727168,186138624,-1807974400,6088572928,-12762677248,18493251584,-12392546304,-2132336640]),(⟨5,0,1⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,2⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨5,1,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,2,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,0,0⟩,[-16384,540672,-6094848,23658496,41713664,-654344192,2532245504,-6275399680,11084611584,-9431269376])]


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
    (Poly.add (Poly.scale (K.ofRat r530) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 6).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r529*r529 : ℚ)=r530 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 6 r529 r529 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=6 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 6).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C087

#print axioms Coulomb8.Columns.C087.sound
