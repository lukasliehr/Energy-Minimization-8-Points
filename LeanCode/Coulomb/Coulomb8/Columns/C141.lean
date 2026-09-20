import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C141

def r0 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 1515520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -11485184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 59596800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -234053632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 44138496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -2024751104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 635138048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -7334088704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 8178753536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -757137408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 1518600192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -150994944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 950272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -9625600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 58417152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -251076608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 860839936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -2469830656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 5668020224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -9421242368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 10023051264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -798883840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 914620416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 221184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2334720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 13008896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -44761088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 110411776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -207650816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 25526272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 541138944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -312270848, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 2960531456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -199557120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -1974272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 16105472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -75333632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 254558208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -719470592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 228704256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -2293923840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1568161792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -156213248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -12574720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 63315968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -222199808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 35799040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -961785856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 616558592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -8192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 991232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -5922816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 18456576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -48668672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 110190592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -107356160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -1368064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -1900544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 7733248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -24248320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 3604480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -68222976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 385024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -5054464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 33497088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -149053440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 560390144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -1864065024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 4748959744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -7925596160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 7475609600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -3009282048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 6627328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -29712384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 97705984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -255025152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 404119552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -83369984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -740753408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 114647040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -450560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 4939776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -25092096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 92250112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -318480384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 802955264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -1096720384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 607698944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 622592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -2113536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 5308416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -43335680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 156073984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -9814016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1867776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -7847936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 18300928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -38043648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 77824000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -86458368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 69246976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -13344768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -3801088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 15466496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -48496640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 7208960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -136445952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -212992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 2359296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 58621952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -172736512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 506609664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -1541914624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 3473891328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -637009920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 142589952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -1556480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 376832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -8126464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -39305216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 229883904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -625262592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 989863936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -5767168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 14598144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -5898240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 68894720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -12828672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 113393664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -4710400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 663552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 843776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -155648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 4235264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -127901696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 5283840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -16384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 851968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -49627136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 8552448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 98025472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -364380160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 2539520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -24576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 1122304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1482752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -7905280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 18554880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 13066240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -335872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 8208384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -23003136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 1523712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 5210112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -59392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 757760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -5742592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 29798400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -117026816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 22069248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -1012375552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 317569024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -3667044352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 4089376768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -378568704, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 759300096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -75497472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -20480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -4812800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 29208576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -125538304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 430419968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1234915328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 2834010112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -4710621184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 5011525632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -399441920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 457310208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 110592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1167360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 6504448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -22380544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 55205888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -103825408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 12763136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 270569472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -156135424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 1480265728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -99778560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -987136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 8052736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -37666816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 127279104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -359735296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 114352128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1146961920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 784080896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -78106624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -51200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -6287360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 31657984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -111099904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 17899520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -480892928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 308279296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 495616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -2961408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 9228288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -24334336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 55095296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -53678080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -684032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -950272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 3866624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -12124160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1802240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -34111488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 192512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2527232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 16748544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -74526720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 280195072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -932032512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 2374479872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -3962798080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 3737804800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1504641024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 20480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 3313664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -14856192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 48852992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -127512576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 202059776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -41684992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -370376704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 57323520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -225280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 2469888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -12546048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 46125056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -159240192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 401477632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -548360192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 303849472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 311296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -1056768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 2654208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -21667840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 78036992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -4907008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 933888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -3923968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 9150464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -19021824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 38912000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -43229184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 34623488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -6672384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 1179648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 29310976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -86368256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 253304832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -770957312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 1736945664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -318504960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 71294976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -778240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 188416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -4063232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -19652608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 114941952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -312631296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 494931968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -2883584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 122880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 7299072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -2949120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 34447360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -6414336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 56696832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -2355200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 331776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 421888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -77824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 2117632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -63950848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 2641920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -8192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 425984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -24813568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 4276224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 49012736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -182190080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 1269760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 561152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -3952640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 9277440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 6533120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -167936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -540672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 4104192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -11501568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 761856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 2605056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[0,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37],[0,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[r0,r48,r49,r50,r51,r52,r53,r54,r55,r56],[0,r57,r58,r59,r60,r61,r62,r63,r64],[0,0,r65,r66,r67,r68,r69,r70],[],[],[],[],[],[],[0,r26,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80],[0,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90],[0,r91,r92,r93,r94,r95,r96,r97,r98,r99],[0,0,r100,r101,r102,r103,r104,r105,r106],[],[],[],[],[],[],[],[r91,r107,r108,r109,r110,r111,r112,r113,r114,r115],[0,r57,r58,r59,r60,r61,r62,r63,r64],[],[],[],[],[],[],[],[0,0,r116,r117,r118,r119,r120,r121],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r91,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131],[r26,r132,r133,r134,r135,r136,r137,r138,r139,r140],[r26,r141,r142,r143,r144,r145,r146,r147,r148],[r91,r149,r150,r151,r152,r153,r154,r155],[0,r156,r157,r158,r159,r160,r161],[],[],[],[],[],[0,r38,r162,r163,r164,r165,r166,r167,r168],[r91,r169,r170,r171,r172,r173,r174,r175],[0,r156,r157,r158,r159,r160,r161],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r176,r177,r178,r179,r180,r181,-49152],[r182,r183,r142,r184,r185,r186,16384],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨0,0,1⟩,[0,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨0,0,2⟩,[r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224]),(⟨0,0,3⟩,[0,r176,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨0,0,4⟩,[r187,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨0,0,5⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,0,6⟩,[0,0,r38,r251,r252,r253,r254,r255]),(⟨0,1,0⟩,[0,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨0,1,1⟩,[0,r213,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨0,1,2⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275]),(⟨0,1,3⟩,[0,r0,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,1,4⟩,[0,0,r284,r285,r286,r287,r288,r289,r290]),(⟨0,2,0⟩,[r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224]),(⟨0,2,1⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275]),(⟨0,2,2⟩,[r0,r48,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,2,3⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,3,0⟩,[0,r176,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨0,3,1⟩,[0,r0,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,3,2⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,3,3⟩,[0,0,r65,r66,r67,r68,r69,r70]),(⟨0,4,0⟩,[r187,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨0,4,1⟩,[0,0,r284,r285,r286,r287,r288,r289,r290]),(⟨0,5,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,6,0⟩,[0,0,r38,r251,r252,r253,r254,r255]),(⟨1,0,0⟩,[0,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨1,0,1⟩,[0,r213,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨1,0,2⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275]),(⟨1,0,3⟩,[0,r0,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨1,0,4⟩,[0,0,r284,r285,r286,r287,r288,r289,r290]),(⟨1,1,0⟩,[0,r213,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨1,1,1⟩,[r0,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308]),(⟨1,1,2⟩,[r213,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨1,1,3⟩,[r213,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨1,1,4⟩,[r0,r326,r327,r328,r329,r330,r331,r332]),(⟨1,1,5⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨1,2,0⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275]),(⟨1,2,1⟩,[r213,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨1,2,2⟩,[0,r176,r339,r340,r341,r342,r343,r344,r345]),(⟨1,2,3⟩,[r0,r346,r347,r348,r349,r350,r351,r352]),(⟨1,2,4⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨1,3,0⟩,[0,r0,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨1,3,1⟩,[r213,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨1,3,2⟩,[r0,r346,r347,r348,r349,r350,r351,r352]),(⟨1,4,0⟩,[0,0,r284,r285,r286,r287,r288,r289,r290]),(⟨1,4,1⟩,[r0,r326,r327,r328,r329,r330,r331,r332]),(⟨1,4,2⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨1,5,1⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨2,0,0⟩,[r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224]),(⟨2,0,1⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275]),(⟨2,0,2⟩,[r0,r48,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨2,0,3⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨2,1,0⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275]),(⟨2,1,1⟩,[r213,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨2,1,2⟩,[0,r176,r339,r340,r341,r342,r343,r344,r345]),(⟨2,1,3⟩,[r0,r346,r347,r348,r349,r350,r351,r352]),(⟨2,1,4⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨2,2,0⟩,[r0,r48,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨2,2,1⟩,[0,r176,r339,r340,r341,r342,r343,r344,r345]),(⟨2,2,2⟩,[0,r353,r354,r355,r356,r357,r358,-24576]),(⟨2,2,3⟩,[r26,r132,r319,r359,r360,r124,8192]),(⟨2,3,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨2,3,1⟩,[r0,r346,r347,r348,r349,r350,r351,r352]),(⟨2,3,2⟩,[r26,r132,r319,r359,r360,r124,8192]),(⟨2,4,1⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨3,0,0⟩,[0,r176,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨3,0,1⟩,[0,r0,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨3,0,2⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨3,0,3⟩,[0,0,r65,r66,r67,r68,r69,r70]),(⟨3,1,0⟩,[0,r0,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨3,1,1⟩,[r213,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨3,1,2⟩,[r0,r346,r347,r348,r349,r350,r351,r352]),(⟨3,2,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨3,2,1⟩,[r0,r346,r347,r348,r349,r350,r351,r352]),(⟨3,2,2⟩,[r26,r132,r319,r359,r360,r124,8192]),(⟨3,3,0⟩,[0,0,r65,r66,r67,r68,r69,r70]),(⟨4,0,0⟩,[r187,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨4,0,1⟩,[0,0,r284,r285,r286,r287,r288,r289,r290]),(⟨4,1,0⟩,[0,0,r284,r285,r286,r287,r288,r289,r290]),(⟨4,1,1⟩,[r0,r326,r327,r328,r329,r330,r331,r332]),(⟨4,1,2⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨4,2,1⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨5,0,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨5,1,1⟩,[0,r333,r334,r335,r336,r337,r338]),(⟨6,0,0⟩,[0,0,r38,r251,r252,r253,r254,r255])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r361) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r362) sourceRight))).isZero := by decide +kernel

noncomputable def partial14 : Poly := []

theorem partial_sound14 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 14)
      sourceRight).eval u v t=partial14.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[-2048,55296,-602112,3563520,-13774848,42356736,-114720768,241360896,-309692416,158570496,34566144,-16515072]),(⟨2,0,1⟩,[0,8192,-172032,1404928,-6492160,22573056,-68390912,153440256,-191770624,72396800,46362624]),(⟨2,0,2⟩,[2048,-51200,466944,-1974272,4845568,-11563008,25206784,-21995520,-4831232,1505280]),(⟨2,0,3⟩,[0,-12288,217088,-1372160,4886528,-14192640,29224960,-21385216,-9949184]),(⟨2,1,0⟩,[0,8192,-172032,1404928,-6492160,22573056,-68390912,153440256,-191770624,72396800,46362624]),(⟨2,1,1⟩,[0,0,12288,-282624,2224128,-6328320,-356352,27070464,-24686592,-10235904]),(⟨2,2,0⟩,[2048,-51200,466944,-1974272,4845568,-11563008,25206784,-21995520,-4831232,1505280]),(⟨2,3,0⟩,[0,-12288,217088,-1372160,4886528,-14192640,29224960,-21385216,-9949184]),(⟨3,0,0⟩,[0,24576,-483328,3813376,-17158144,57389056,-169070592,393449472,-566652928,363474944,-10260480]),(⟨3,0,1⟩,[0,0,-53248,569344,-2527232,11333632,-58159104,177803264,-260911104,148721664]),(⟨3,0,2⟩,[0,-16384,278528,-1589248,4341760,-10141696,25870336,-32292864,5160960]),(⟨3,0,3⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨3,1,0⟩,[0,0,-53248,569344,-2527232,11333632,-58159104,177803264,-260911104,148721664]),(⟨3,1,1⟩,[0,0,0,-98304,1474560,-6488064,5308416,22315008,-35094528]),(⟨3,1,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,2,0⟩,[0,-16384,278528,-1589248,4341760,-10141696,25870336,-32292864,5160960]),(⟨3,2,1⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨4,0,0⟩,[2048,-51200,401408,-1122304,94208,6098944,-32595968,128737280,-241055744,160462848]),(⟨4,0,1⟩,[0,0,0,-98304,1474560,-6488064,5308416,22315008,-35094528]),(⟨4,1,0⟩,[0,0,0,-98304,1474560,-6488064,5308416,22315008,-35094528]),(⟨4,1,1⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,1,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,2,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨5,1,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial14)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 14))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound14 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544])]

noncomputable def partial8 : Poly := [(⟨1,0,0⟩,[0,-12288,286720,-2883584,17088512,-70672384,232947712,-652279808,1481326592,-2445144064,2582716416,-1439072256,245366784]),(⟨1,0,1⟩,[0,-4096,155648,-1982464,13213696,-57909248,200712192,-593117184,1372872704,-2153861120,1955397632,-769032192]),(⟨1,0,2⟩,[0,12288,-245760,1835008,-6938624,16228352,-28057600,20971520,75423744,-235917312,202825728]),(⟨1,0,3⟩,[0,4096,-172032,1900544,-10018816,34791424,-101081088,223674368,-287449088,155127808]),(⟨1,0,4⟩,[0,0,-24576,409600,-2531328,9142272,-26976256,55721984,-48324608]),(⟨1,1,0⟩,[0,-4096,155648,-1982464,13213696,-57909248,200712192,-593117184,1372872704,-2153861120,1955397632,-769032192]),(⟨1,1,1⟩,[4096,-106496,1163264,-7200768,29548544,-94396416,272859136,-696721408,1294667776,-1423769600,682672128]),(⟨1,1,2⟩,[0,-12288,229376,-1720320,7897088,-29237248,95453184,-244072448,388726784,-267595776]),(⟨1,1,3⟩,[-4096,98304,-892928,4046848,-11763712,31719424,-75096064,103333888,-55635968]),(⟨1,1,4⟩,[0,24576,-409600,2531328,-9142272,26976256,-55721984,48324608]),(⟨1,2,0⟩,[0,12288,-245760,1835008,-6938624,16228352,-28057600,20971520,75423744,-235917312,202825728]),(⟨1,2,1⟩,[0,-12288,229376,-1720320,7897088,-29237248,95453184,-244072448,388726784,-267595776]),(⟨1,2,2⟩,[0,0,-24576,540672,-4104192,11501568,-761856,-44285952,49717248]),(⟨1,3,0⟩,[0,4096,-172032,1900544,-10018816,34791424,-101081088,223674368,-287449088,155127808]),(⟨1,3,1⟩,[-4096,98304,-892928,4046848,-11763712,31719424,-75096064,103333888,-55635968]),(⟨1,4,0⟩,[0,0,-24576,409600,-2531328,9142272,-26976256,55721984,-48324608]),(⟨1,4,1⟩,[0,24576,-409600,2531328,-9142272,26976256,-55721984,48324608]),(⟨2,0,0⟩,[-2048,55296,-552960,2711552,-7180288,10194944,5693440,-132980736,597874688,-1361192960,1557155840,-705331200]),(⟨2,0,1⟩,[0,8192,-155648,1150976,-5304320,20549632,-56881152,51556352,175845376,-526512128,423628800]),(⟨2,0,2⟩,[2048,-51200,466944,-1949696,4304896,-7458816,13705216,-21233664,39454720,-48211968]),(⟨2,0,3⟩,[0,-12288,217088,-1372160,4886528,-14192640,29224960,-21385216,-9949184]),(⟨2,1,0⟩,[0,8192,-155648,1150976,-5304320,20549632,-56881152,51556352,175845376,-526512128,423628800]),(⟨2,1,1⟩,[0,-16384,339968,-2846720,13217792,-40693760,106172416,-264359936,455938048,-334860288]),(⟨2,1,2⟩,[0,24576,-499712,3891200,-14458880,20717568,24125440,-113238016,100409344]),(⟨2,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[2048,-51200,466944,-1949696,4304896,-7458816,13705216,-21233664,39454720,-48211968]),(⟨2,2,1⟩,[0,24576,-499712,3891200,-14458880,20717568,24125440,-113238016,100409344]),(⟨2,2,2⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨2,2,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,3,0⟩,[0,-12288,217088,-1372160,4886528,-14192640,29224960,-21385216,-9949184]),(⟨2,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,3,2⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,0,0⟩,[0,36864,-745472,5976064,-26710016,85692416,-239702016,543952896,-784183296,519610368,-32624640]),(⟨3,0,1⟩,[0,4096,-151552,1437696,-6164480,20566016,-80736256,225923072,-308523008,156033024]),(⟨3,0,2⟩,[0,-16384,278528,-1589248,4341760,-10141696,25870336,-32292864,5160960]),(⟨3,0,3⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨3,1,0⟩,[0,4096,-151552,1437696,-6164480,20566016,-80736256,225923072,-308523008,156033024]),(⟨3,1,1⟩,[-4096,122880,-1343488,6889472,-18112512,25305088,-17924096,974848,8286208]),(⟨3,1,2⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨3,2,0⟩,[0,-16384,278528,-1589248,4341760,-10141696,25870336,-32292864,5160960]),(⟨3,2,1⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨3,2,2⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,3,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨4,0,0⟩,[2048,-51200,327680,-90112,-6287360,31657984,-111099904,304291840,-480892928,308279296]),(⟨4,0,1⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨4,1,0⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨4,1,1⟩,[4096,-69632,331776,421888,-9261056,35999744,-63950848,44912640]),(⟨4,1,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,2,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨5,1,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-12288,286720,-2883584,17088512,-70672384,232947712,-652279808,1481326592,-2445144064,2582716416,-1439072256,245366784]),(⟨0,1,1⟩,[0,-4096,155648,-1982464,13213696,-57909248,200712192,-593117184,1372872704,-2153861120,1955397632,-769032192]),(⟨0,1,2⟩,[0,12288,-245760,1835008,-6938624,16228352,-28057600,20971520,75423744,-235917312,202825728]),(⟨0,1,3⟩,[0,4096,-172032,1900544,-10018816,34791424,-101081088,223674368,-287449088,155127808]),(⟨0,1,4⟩,[0,0,-24576,409600,-2531328,9142272,-26976256,55721984,-48324608]),(⟨0,2,0⟩,[-2048,55296,-552960,2711552,-7180288,10194944,5693440,-132980736,597874688,-1361192960,1557155840,-705331200]),(⟨0,2,1⟩,[0,8192,-155648,1150976,-5304320,20549632,-56881152,51556352,175845376,-526512128,423628800]),(⟨0,2,2⟩,[2048,-51200,466944,-1949696,4304896,-7458816,13705216,-21233664,39454720,-48211968]),(⟨0,2,3⟩,[0,-12288,217088,-1372160,4886528,-14192640,29224960,-21385216,-9949184]),(⟨0,3,0⟩,[0,36864,-745472,5976064,-26710016,85692416,-239702016,543952896,-784183296,519610368,-32624640]),(⟨0,3,1⟩,[0,4096,-151552,1437696,-6164480,20566016,-80736256,225923072,-308523008,156033024]),(⟨0,3,2⟩,[0,-16384,278528,-1589248,4341760,-10141696,25870336,-32292864,5160960]),(⟨0,3,3⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨0,4,0⟩,[2048,-51200,327680,-90112,-6287360,31657984,-111099904,304291840,-480892928,308279296]),(⟨0,4,1⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨0,5,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨0,6,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨1,0,0⟩,[0,-12288,286720,-2883584,17088512,-70672384,232947712,-652279808,1481326592,-2445144064,2582716416,-1439072256,245366784]),(⟨1,0,1⟩,[0,-4096,155648,-1982464,13213696,-57909248,200712192,-593117184,1372872704,-2153861120,1955397632,-769032192]),(⟨1,0,2⟩,[0,12288,-245760,1835008,-6938624,16228352,-28057600,20971520,75423744,-235917312,202825728]),(⟨1,0,3⟩,[0,4096,-172032,1900544,-10018816,34791424,-101081088,223674368,-287449088,155127808]),(⟨1,0,4⟩,[0,0,-24576,409600,-2531328,9142272,-26976256,55721984,-48324608]),(⟨1,1,0⟩,[0,-4096,204800,-2834432,19808256,-90071040,321126400,-967458816,2280439808,-3673624576,3477987328,-1457848320]),(⟨1,1,1⟩,[4096,-106496,1179648,-7454720,30736384,-96419840,284368896,-798605312,1662283776,-2022678528,1059938304]),(⟨1,1,2⟩,[0,-12288,229376,-1695744,7356416,-25133056,83951616,-243310592,433012736,-317313024]),(⟨1,1,3⟩,[-4096,98304,-892928,4046848,-11763712,31719424,-75096064,103333888,-55635968]),(⟨1,1,4⟩,[0,24576,-409600,2531328,-9142272,26976256,-55721984,48324608]),(⟨1,2,0⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨1,2,1⟩,[0,-12288,241664,-1978368,9580544,-31461376,83595264,-216240128,408326144,-327548928]),(⟨1,2,2⟩,[0,24576,-499712,3891200,-14458880,20717568,24125440,-113238016,100409344]),(⟨1,2,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,0⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨1,3,1⟩,[-4096,122880,-1368064,7299072,-20643840,34447360,-44900352,56696832,-40038400]),(⟨1,3,2⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨1,4,0⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨1,4,1⟩,[4096,-69632,331776,421888,-9261056,35999744,-63950848,44912640]),(⟨1,4,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,5,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,0,0⟩,[-2048,55296,-552960,2711552,-7180288,10194944,5693440,-132980736,597874688,-1361192960,1557155840,-705331200]),(⟨2,0,1⟩,[0,8192,-155648,1150976,-5304320,20549632,-56881152,51556352,175845376,-526512128,423628800]),(⟨2,0,2⟩,[2048,-51200,466944,-1949696,4304896,-7458816,13705216,-21233664,39454720,-48211968]),(⟨2,0,3⟩,[0,-12288,217088,-1372160,4886528,-14192640,29224960,-21385216,-9949184]),(⟨2,1,0⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨2,1,1⟩,[0,-12288,241664,-1978368,9580544,-31461376,83595264,-216240128,408326144,-327548928]),(⟨2,1,2⟩,[0,24576,-499712,3891200,-14458880,20717568,24125440,-113238016,100409344]),(⟨2,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[4096,-102400,933888,-3923968,9150464,-19021824,38912000,-43229184,34623488,-46706688]),(⟨2,2,1⟩,[0,49152,-974848,7241728,-24813568,29933568,49012736,-182190080,151101440]),(⟨2,2,2⟩,[0,24576,-540672,4104192,-11501568,761856,44285952,-49717248]),(⟨2,2,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,3,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨2,3,1⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨2,3,2⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,4,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[0,36864,-745472,5976064,-26710016,85692416,-239702016,543952896,-784183296,519610368,-32624640]),(⟨3,0,1⟩,[0,4096,-151552,1437696,-6164480,20566016,-80736256,225923072,-308523008,156033024]),(⟨3,0,2⟩,[0,-16384,278528,-1589248,4341760,-10141696,25870336,-32292864,5160960]),(⟨3,0,3⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨3,1,0⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨3,1,1⟩,[-4096,122880,-1368064,7299072,-20643840,34447360,-44900352,56696832,-40038400]),(⟨3,1,2⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨3,2,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨3,2,1⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨3,2,2⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,3,0⟩,[0,0,196608,-1900544,7733248,-24248320,61276160,-68222976]),(⟨4,0,0⟩,[2048,-51200,327680,-90112,-6287360,31657984,-111099904,304291840,-480892928,308279296]),(⟨4,0,1⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨4,1,0⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨4,1,1⟩,[4096,-69632,331776,421888,-9261056,35999744,-63950848,44912640]),(⟨4,1,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,2,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨5,1,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[2048,-59392,757760,-5742592,29798400,-117026816,375177216,-1012375552,2222983168,-3667044352,4089376768,-2649980928,759300096,-75497472]),(⟨0,0,1⟩,[0,-20480,475136,-4812800,29208576,-125538304,430419968,-1234915328,2834010112,-4710621184,5011525632,-2796093440,457310208]),(⟨0,0,2⟩,[-4096,110592,-1167360,6504448,-22380544,55205888,-103825408,89341952,270569472,-1092947968,1480265728,-698449920]),(⟨0,0,3⟩,[0,49152,-987136,8052736,-37666816,127279104,-359735296,800464896,-1146961920,784080896,-78106624]),(⟨0,0,4⟩,[2048,-51200,327680,-90112,-6287360,31657984,-111099904,304291840,-480892928,308279296]),(⟨0,0,5⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨0,0,6⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨0,1,0⟩,[0,-20480,475136,-4812800,29208576,-125538304,430419968,-1234915328,2834010112,-4710621184,5011525632,-2796093440,457310208]),(⟨0,1,1⟩,[0,-4096,192512,-2527232,16748544,-74526720,280195072,-932032512,2374479872,-3962798080,3737804800,-1504641024]),(⟨0,1,2⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨0,1,3⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨0,1,4⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨0,2,0⟩,[-4096,110592,-1167360,6504448,-22380544,55205888,-103825408,89341952,270569472,-1092947968,1480265728,-698449920]),(⟨0,2,1⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨0,2,2⟩,[4096,-102400,933888,-3923968,9150464,-19021824,38912000,-43229184,34623488,-46706688]),(⟨0,2,3⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨0,3,0⟩,[0,49152,-987136,8052736,-37666816,127279104,-359735296,800464896,-1146961920,784080896,-78106624]),(⟨0,3,1⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨0,3,2⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨0,3,3⟩,[0,0,196608,-1900544,7733248,-24248320,61276160,-68222976]),(⟨0,4,0⟩,[2048,-51200,327680,-90112,-6287360,31657984,-111099904,304291840,-480892928,308279296]),(⟨0,4,1⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨0,5,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨0,6,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488]),(⟨1,0,0⟩,[0,-20480,475136,-4812800,29208576,-125538304,430419968,-1234915328,2834010112,-4710621184,5011525632,-2796093440,457310208]),(⟨1,0,1⟩,[0,-4096,192512,-2527232,16748544,-74526720,280195072,-932032512,2374479872,-3962798080,3737804800,-1504641024]),(⟨1,0,2⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨1,0,3⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨1,0,4⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨1,1,0⟩,[0,-4096,192512,-2527232,16748544,-74526720,280195072,-932032512,2374479872,-3962798080,3737804800,-1504641024]),(⟨1,1,1⟩,[4096,-106496,1179648,-7380992,29310976,-86368256,253304832,-770957312,1736945664,-2229534720,1212014592]),(⟨1,1,2⟩,[-4096,90112,-778240,3203072,-4063232,-19652608,114941952,-312631296,494931968,-343146496]),(⟨1,1,3⟩,[-4096,122880,-1368064,7299072,-20643840,34447360,-44900352,56696832,-40038400]),(⟨1,1,4⟩,[4096,-69632,331776,421888,-9261056,35999744,-63950848,44912640]),(⟨1,1,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,2,0⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨1,2,1⟩,[-4096,90112,-778240,3203072,-4063232,-19652608,114941952,-312631296,494931968,-343146496]),(⟨1,2,2⟩,[0,49152,-974848,7241728,-24813568,29933568,49012736,-182190080,151101440]),(⟨1,2,3⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨1,2,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,3,0⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨1,3,1⟩,[-4096,122880,-1368064,7299072,-20643840,34447360,-44900352,56696832,-40038400]),(⟨1,3,2⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨1,4,0⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨1,4,1⟩,[4096,-69632,331776,421888,-9261056,35999744,-63950848,44912640]),(⟨1,4,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,5,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,0,0⟩,[-4096,110592,-1167360,6504448,-22380544,55205888,-103825408,89341952,270569472,-1092947968,1480265728,-698449920]),(⟨2,0,1⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨2,0,2⟩,[4096,-102400,933888,-3923968,9150464,-19021824,38912000,-43229184,34623488,-46706688]),(⟨2,0,3⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨2,1,0⟩,[0,20480,-417792,3313664,-14856192,48852992,-127512576,202059776,-41684992,-370376704,401264640]),(⟨2,1,1⟩,[-4096,90112,-778240,3203072,-4063232,-19652608,114941952,-312631296,494931968,-343146496]),(⟨2,1,2⟩,[0,49152,-974848,7241728,-24813568,29933568,49012736,-182190080,151101440]),(⟨2,1,3⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨2,1,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,2,0⟩,[4096,-102400,933888,-3923968,9150464,-19021824,38912000,-43229184,34623488,-46706688]),(⟨2,2,1⟩,[0,49152,-974848,7241728,-24813568,29933568,49012736,-182190080,151101440]),(⟨2,2,2⟩,[0,24576,-540672,4104192,-11501568,761856,44285952,-49717248]),(⟨2,2,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,3,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨2,3,1⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨2,3,2⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,4,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[0,49152,-987136,8052736,-37666816,127279104,-359735296,800464896,-1146961920,784080896,-78106624]),(⟨3,0,1⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨3,0,2⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨3,0,3⟩,[0,0,196608,-1900544,7733248,-24248320,61276160,-68222976]),(⟨3,1,0⟩,[0,4096,-225280,2469888,-12546048,46125056,-159240192,401477632,-548360192,303849472]),(⟨3,1,1⟩,[-4096,122880,-1368064,7299072,-20643840,34447360,-44900352,56696832,-40038400]),(⟨3,1,2⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨3,2,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨3,2,1⟩,[4096,-86016,561152,-741376,-3952640,9277440,6533120,-19984384]),(⟨3,2,2⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,3,0⟩,[0,0,196608,-1900544,7733248,-24248320,61276160,-68222976]),(⟨4,0,0⟩,[2048,-51200,327680,-90112,-6287360,31657984,-111099904,304291840,-480892928,308279296]),(⟨4,0,1⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨4,1,0⟩,[0,0,-24576,311296,-1056768,2654208,-21667840,78036992,-83419136]),(⟨4,1,1⟩,[4096,-69632,331776,421888,-9261056,35999744,-63950848,44912640]),(⟨4,1,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,2,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[0,-28672,495616,-2961408,9228288,-24334336,55095296,-53678080,-4788224]),(⟨5,1,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,0,98304,-950272,3866624,-12124160,30638080,-34111488])]


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
    (Poly.add (Poly.scale (K.ofRat r363) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 10 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r361*r362 : ℚ)=r363 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 10 11 r361 r362 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 10=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 10 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C141

#print axioms Coulomb8.Columns.C141.sound
