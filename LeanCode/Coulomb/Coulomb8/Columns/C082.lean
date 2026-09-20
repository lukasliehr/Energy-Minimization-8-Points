import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C082

def r0 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -7968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 100416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -757152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 536160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -12615552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 28388736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -39286080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 21757536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 26210784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -59874240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 40646880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -1194528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -8956224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1244160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -36672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 313280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -1817056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 7386944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -21165888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 41702016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -51414816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 24595968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 4813248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -70882880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 50338144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -1351232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -521280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 1376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -20736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 176192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -59168, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -12353536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 25640960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -33171808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 17070624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 19411200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -5826496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 3870816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -815200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -7104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 4672, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -521408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 2172384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -825344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 1291520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -5073664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -8694432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 2705984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -11023680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -3462208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 4718496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 52704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -23680, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 1802688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -5050240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 8662592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -205600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 10603072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -1433312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 453248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 4224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -2112, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 150016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -283776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -40448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 1233280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -2187264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 158400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 123008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -129728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 29824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -111872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 243328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -371712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 279936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 194688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -359808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -73856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 221824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -325760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 82560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 53120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -50560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 55808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -56704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 18304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 47616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -24320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 82176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -28416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 273408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -1579264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 6056000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -941056, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 28851712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -32517120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 13701568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 2960640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -5854720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 4309760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -1238720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 23680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -123072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 323808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -138752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -1877632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 6457856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -1414560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 834240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 589312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -1235136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 588000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 40448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -314368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 1413120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -3990528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 7053824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -964608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 46080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 7426304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -1164288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 421888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 24512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -176384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 779136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -124672, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 459648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -203264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -503360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 907648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -538048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 62720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -53248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 310784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -968704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 1645568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -1167360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -695808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 1828864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -903936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -145920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 440064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -415488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -939264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 2987520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -2827008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 253824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -183296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 307456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -1016832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 308224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -291200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -107264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 213760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -110592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 184576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -61696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 118016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -425728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 680192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -21888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 9216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -549888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 922368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -3050496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 924672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -873600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -3984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 50208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -378576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 268080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -6307776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 14194368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -19643040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 10878768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 13105392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -29937120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 20323440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -597264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -4478112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 622080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -18336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 156640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -908528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 3693472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -10582944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 20851008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -25707408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 12297984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 2406624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -35441440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 25169072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -675616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -260640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -10368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 88096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -29584, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -6176768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 12820480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -16585904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 8535312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 9705600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -2913248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 1935408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -407600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -3552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 2336, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -260704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1086192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -412672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 645760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2536832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -4347216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 1352992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -5511840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -1731104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 2359248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 26352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -11840, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 901344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -2525120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 4331296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -102800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 5301536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -716656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 226624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 2112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -1056, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 75008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -141888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -20224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 616640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -1093632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 79200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 61504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -64864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 14912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -55936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 121664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -185856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 139968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 97344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -179904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -36928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 110912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -162880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 41280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 26560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -25280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 27904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 9152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 23808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -12160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 41088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 136704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -789632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 3028000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -470528, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 14425856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -16258560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 6850784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 1480320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -2927360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 2154880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -619360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -1184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 11840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -61536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 161904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -69376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -938816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 3228928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -707280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 417120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 294656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -617568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 294000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 20224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -157184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 706560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -1995264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 3526912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -482304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 23040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 3713152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -582144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 210944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 12256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -88192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 389568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -62336, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 229824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -101632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -251680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 453824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -269024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 31360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -26624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 155392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -484352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 822784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -583680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -347904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 914432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -451968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -72960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 220032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -207744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -469632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 1493760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -1413504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 126912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -91648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 153728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -508416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 154112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -145600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 106880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -55296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 92288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 59008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -212864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 340096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -10944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 4608, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -274944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 461184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -27264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -1525248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 462336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -436800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29],[r30,r31,r32,r33,r34,34784,r35,r36,r37,r38,r39,r40,r41,r42],[r0,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54],[r55,r56,r57,r58,r59,r60,r61,-62720,r62,r63,r64,r65],[r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[r77,r78,r79,r80,r81,r82,r83,r84,r85,r86],[0,r87,r88,r89,r90,r91,r92,r93,r94],[r95,r96,r97,r98,r99,-512,r100,r101],[0,r102,r103,r104,-512,r105,r106],[],[],[],[0,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119],[r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132],[0,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143],[],[],[0,r87,r88,r89,r90,r91,r92,r93,r94],[],[],[],[],[],[r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155],[r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[],[],[r95,r96,r97,r98,r99,-512,r100,r101],[],[],[],[],[0,r156,r157,r158,r159,r160,r161,r162,r163,r164],[],[],[0,r102,r103,r104,-512,r105,r106],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r165,r166,r167,r168,r169,r170,r171,r172,r173,6912],[r174,r175,r176,r177,r178,r179,r180,r181,r182,6272],[r77,r183,r184,r185,r186,r187,r188,r189,-6272],[r78,r190,r191,r192,r193,r194,r195,-2816],[],[],[r196,r197,r198,r199,512],[],[],[],[],[],[],[],[],[],[],[],[],[],[r200,r201,r202,r203,r204,r205,r206,r207,r208,18816],[r77,r183,r184,r185,r186,r187,r188,r189,-6272],[r78,r190,r191,r192,r193,r194,r195,-2816],[],[],[r196,r197,r198,r199,512],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223]),(⟨0,0,1⟩,[r224,r107,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237]),(⟨0,0,2⟩,[r238,r239,r240,r241,r242,17392,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,0,3⟩,[r209,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨0,0,4⟩,[r263,r264,r265,r266,r267,r268,r269,-31360,r270,r271,r272,r273]),(⟨0,0,5⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,0,6⟩,[r144,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,0,7⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,0,8⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨0,0,9⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨0,1,0⟩,[r224,r107,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237]),(⟨0,1,1⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨0,1,2⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨0,1,3⟩,[0,r165,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347]),(⟨0,1,6⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,2,0⟩,[r238,r239,r240,r241,r242,17392,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,2,1⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨0,2,2⟩,[r55,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,2,3⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,2,6⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨0,3,0⟩,[r209,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨0,3,1⟩,[0,r165,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347]),(⟨0,3,2⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,3,3⟩,[0,r359,r360,r361,r362,r363,r364,r365,r366,r367]),(⟨0,3,6⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨0,4,0⟩,[r263,r264,r265,r266,r267,r268,r269,-31360,r270,r271,r272,r273]),(⟨0,5,0⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,6,0⟩,[r144,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨0,6,1⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,6,2⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨0,6,3⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨0,7,0⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,8,0⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨0,9,0⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨1,0,0⟩,[r224,r107,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237]),(⟨1,0,1⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨1,0,2⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨1,0,3⟩,[0,r165,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347]),(⟨1,0,6⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨1,1,0⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨1,2,0⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨1,2,2⟩,[0,r368,r369,r370,r371,r372,r373,r374,r375,r376,3456]),(⟨1,2,3⟩,[r377,r378,r379,r380,r381,r382,r383,r384,r385,3136]),(⟨1,2,4⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨1,2,5⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨1,2,8⟩,[r399,r400,r401,r402,256]),(⟨1,3,0⟩,[0,r165,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347]),(⟨1,3,2⟩,[r377,r378,r379,r380,r381,r382,r383,r384,r385,3136]),(⟨1,4,2⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨1,5,2⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨1,6,0⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨1,8,2⟩,[r399,r400,r401,r402,256]),(⟨2,0,0⟩,[r238,r239,r240,r241,r242,17392,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨2,0,1⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨2,0,2⟩,[r55,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,0,3⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨2,0,6⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨2,1,0⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨2,1,2⟩,[0,r368,r369,r370,r371,r372,r373,r374,r375,r376,3456]),(⟨2,1,3⟩,[r377,r378,r379,r380,r381,r382,r383,r384,r385,3136]),(⟨2,1,4⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨2,1,5⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨2,1,8⟩,[r399,r400,r401,r402,256]),(⟨2,2,0⟩,[r55,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,2,1⟩,[0,r368,r369,r370,r371,r372,r373,r374,r375,r376,3456]),(⟨2,2,2⟩,[r403,r404,r405,r406,r407,r408,r409,r410,r411,9408]),(⟨2,2,3⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨2,2,4⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨2,2,7⟩,[r399,r400,r401,r402,256]),(⟨2,3,0⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨2,3,1⟩,[r377,r378,r379,r380,r381,r382,r383,r384,r385,3136]),(⟨2,3,2⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨2,4,1⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨2,4,2⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨2,5,1⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨2,6,0⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨2,7,2⟩,[r399,r400,r401,r402,256]),(⟨2,8,1⟩,[r399,r400,r401,r402,256]),(⟨3,0,0⟩,[r209,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨3,0,1⟩,[0,r165,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347]),(⟨3,0,2⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨3,0,3⟩,[0,r359,r360,r361,r362,r363,r364,r365,r366,r367]),(⟨3,0,6⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨3,1,0⟩,[0,r165,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347]),(⟨3,1,2⟩,[r377,r378,r379,r380,r381,r382,r383,r384,r385,3136]),(⟨3,2,0⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨3,2,1⟩,[r377,r378,r379,r380,r381,r382,r383,r384,r385,3136]),(⟨3,2,2⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨3,3,0⟩,[0,r359,r360,r361,r362,r363,r364,r365,r366,r367]),(⟨3,6,0⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨4,0,0⟩,[r263,r264,r265,r266,r267,r268,r269,-31360,r270,r271,r272,r273]),(⟨4,1,2⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨4,2,1⟩,[r144,r386,r387,r388,r389,r390,r391,r392,-3136]),(⟨4,2,2⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨5,0,0⟩,[r15,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨5,1,2⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨5,2,1⟩,[r284,r393,r394,r395,r396,r397,r398,-1408]),(⟨6,0,0⟩,[r144,r284,r285,r286,r287,r288,r289,r290,r291,r292]),(⟨6,0,1⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨6,0,2⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨6,0,3⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨6,1,0⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨6,2,0⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨6,3,0⟩,[0,r307,r308,r309,-256,r310,r311]),(⟨7,0,0⟩,[0,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨7,2,2⟩,[r399,r400,r401,r402,256]),(⟨8,0,0⟩,[r301,r102,r302,r303,r304,-256,r305,r306]),(⟨8,1,2⟩,[r399,r400,r401,r402,256]),(⟨8,2,1⟩,[r399,r400,r401,r402,256]),(⟨9,0,0⟩,[0,r307,r308,r309,-256,r310,r311])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r412) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r413) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[512,-10752,98304,-502272,1489920,-2317824,847872,2511360,-2878976,368640]),(⟨6,0,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,0,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,0,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨6,1,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,2,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,3,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨7,0,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨8,1,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,2,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨9,0,0⟩,[0,5120,-52224,190464,-243712,-97280,328704])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[512,-10752,98304,-502272,1489920,-2317824,847872,2511360,-2878976,368640]),(⟨0,6,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,6,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,6,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,7,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,8,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,9,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨1,0,0⟩,[-384,10752,-138624,1085312,-5708800,21074048,-55261440,100911360,-117499776,55390464,69906048,-155338880,127288576,-46234496,4515840]),(⟨1,0,1⟩,[0,2688,-56832,546816,-3158528,12112000,-31995904,57703424,-65034240,27403136,41448960,-81966080,60336640,-17342080]),(⟨1,0,2⟩,[384,-10368,116352,-730496,2850560,-7131904,10937088,-7450880,-6539904,20773760,-20347264,8410752,-878080]),(⟨1,0,3⟩,[0,-3840,66048,-501504,2195456,-6042112,10499072,-10164736,1290240,9605376,-10970624,4026624]),(⟨1,1,0⟩,[0,2688,-56832,546816,-3158528,12112000,-31995904,57703424,-65034240,27403136,41448960,-81966080,60336640,-17342080]),(⟨1,2,0⟩,[384,-10368,116352,-730496,2850560,-7131904,10937088,-7450880,-6539904,20773760,-20347264,8410752,-878080]),(⟨1,3,0⟩,[0,-3840,66048,-501504,2195456,-6042112,10499072,-10164736,1290240,9605376,-10970624,4026624]),(⟨1,6,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨1,8,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,0,0⟩,[-128,6656,-113664,1040000,-6013312,23542144,-63640576,115758848,-125752192,36975360,106162176,-166983040,102055296,-21857920]),(⟨2,0,1⟩,[0,896,-21632,238208,-1555328,6576896,-18447616,33282304,-33067776,2584960,36848000,-42994560,17342080]),(⟨2,0,2⟩,[128,-3840,49024,-352768,1558272,-4238848,6435072,-2845696,-7047040,12707072,-7532672,878080]),(⟨2,0,3⟩,[0,-1280,25856,-231936,1175040,-3561472,6206464,-4754944,-2168320,6944000,-4026624]),(⟨2,1,0⟩,[0,896,-21632,238208,-1555328,6576896,-18447616,33282304,-33067776,2584960,36848000,-42994560,17342080]),(⟨2,2,0⟩,[128,-3840,49024,-352768,1558272,-4238848,6435072,-2845696,-7047040,12707072,-7532672,878080]),(⟨2,2,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,3,0⟩,[0,-1280,25856,-231936,1175040,-3561472,6206464,-4754944,-2168320,6944000,-4026624]),(⟨2,6,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨2,7,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,8,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[1152,-28416,306176,-1891328,7285632,-17538560,23426048,-5278720,-36935808,58940672,-26689536,-15247360,14436480]),(⟨3,0,1⟩,[0,-5376,95744,-755968,3457024,-9920000,17716224,-16844288,0,20099840,-21629440,7786240]),(⟨3,0,2⟩,[-768,18176,-169472,832000,-2310144,3399680,-1273344,-3994112,6603520,-3499776,394240]),(⟨3,0,3⟩,[0,7680,-106496,621568,-1937408,3291136,-2334720,-1391616,3657728,-1807872]),(⟨3,1,0⟩,[0,-5376,95744,-755968,3457024,-9920000,17716224,-16844288,0,20099840,-21629440,7786240]),(⟨3,1,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨3,2,0⟩,[-768,18176,-169472,832000,-2310144,3399680,-1273344,-3994112,6603520,-3499776,394240]),(⟨3,2,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨3,2,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨3,3,0⟩,[0,7680,-106496,621568,-1937408,3291136,-2334720,-1391616,3657728,-1807872]),(⟨3,6,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨4,0,0⟩,[128,-13056,210816,-1610240,7210752,-20200960,34650368,-29854720,-5756800,42412288,-40132736,12690944]),(⟨4,1,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨4,2,1⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨4,2,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨5,0,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨5,1,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨5,2,1⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨6,0,0⟩,[512,-3072,-8192,119296,-447488,973312,-1486848,1119744,778752,-1439232]),(⟨6,0,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,0,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,0,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨6,1,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,2,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,3,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨7,0,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨8,1,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,2,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨9,0,0⟩,[0,5120,-52224,190464,-243712,-97280,328704])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[512,-10752,98304,-502272,1489920,-2317824,847872,2511360,-2878976,368640]),(⟨0,0,7⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,0,8⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,0,9⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,1,0⟩,[-384,10752,-138624,1085312,-5708800,21074048,-55261440,100911360,-117499776,55390464,69906048,-155338880,127288576,-46234496,4515840]),(⟨0,1,1⟩,[0,2688,-56832,546816,-3158528,12112000,-31995904,57703424,-65034240,27403136,41448960,-81966080,60336640,-17342080]),(⟨0,1,2⟩,[384,-10368,116352,-730496,2850560,-7131904,10937088,-7450880,-6539904,20773760,-20347264,8410752,-878080]),(⟨0,1,3⟩,[0,-3840,66048,-501504,2195456,-6042112,10499072,-10164736,1290240,9605376,-10970624,4026624]),(⟨0,1,6⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,2,0⟩,[-128,6656,-113664,1040000,-6013312,23542144,-63640576,115758848,-125752192,36975360,106162176,-166983040,102055296,-21857920]),(⟨0,2,1⟩,[0,896,-21632,238208,-1555328,6576896,-18447616,33282304,-33067776,2584960,36848000,-42994560,17342080]),(⟨0,2,2⟩,[128,-3840,49024,-352768,1558272,-4238848,6435072,-2845696,-7047040,12707072,-7532672,878080]),(⟨0,2,3⟩,[0,-1280,25856,-231936,1175040,-3561472,6206464,-4754944,-2168320,6944000,-4026624]),(⟨0,2,6⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,3,0⟩,[1152,-28416,306176,-1891328,7285632,-17538560,23426048,-5278720,-36935808,58940672,-26689536,-15247360,14436480]),(⟨0,3,1⟩,[0,-5376,95744,-755968,3457024,-9920000,17716224,-16844288,0,20099840,-21629440,7786240]),(⟨0,3,2⟩,[-768,18176,-169472,832000,-2310144,3399680,-1273344,-3994112,6603520,-3499776,394240]),(⟨0,3,3⟩,[0,7680,-106496,621568,-1937408,3291136,-2334720,-1391616,3657728,-1807872]),(⟨0,3,6⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,4,0⟩,[128,-13056,210816,-1610240,7210752,-20200960,34650368,-29854720,-5756800,42412288,-40132736,12690944]),(⟨0,5,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨0,6,0⟩,[512,-3072,-8192,119296,-447488,973312,-1486848,1119744,778752,-1439232]),(⟨0,6,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,6,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,6,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,7,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,8,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,9,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨1,0,0⟩,[-384,10752,-138624,1085312,-5708800,21074048,-55261440,100911360,-117499776,55390464,69906048,-155338880,127288576,-46234496,4515840]),(⟨1,0,1⟩,[0,2688,-56832,546816,-3158528,12112000,-31995904,57703424,-65034240,27403136,41448960,-81966080,60336640,-17342080]),(⟨1,0,2⟩,[384,-10368,116352,-730496,2850560,-7131904,10937088,-7450880,-6539904,20773760,-20347264,8410752,-878080]),(⟨1,0,3⟩,[0,-3840,66048,-501504,2195456,-6042112,10499072,-10164736,1290240,9605376,-10970624,4026624]),(⟨1,0,6⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨1,1,0⟩,[0,5376,-113664,1093632,-6317056,24224000,-63991808,115406848,-130068480,54806272,82897920,-163932160,120673280,-34684160]),(⟨1,2,0⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨1,2,8⟩,[-2048,24576,-61440,-73728,243712]),(⟨1,3,0⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨1,3,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨1,4,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨1,5,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨1,6,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨1,8,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,0,0⟩,[-128,6656,-113664,1040000,-6013312,23542144,-63640576,115758848,-125752192,36975360,106162176,-166983040,102055296,-21857920]),(⟨2,0,1⟩,[0,896,-21632,238208,-1555328,6576896,-18447616,33282304,-33067776,2584960,36848000,-42994560,17342080]),(⟨2,0,2⟩,[128,-3840,49024,-352768,1558272,-4238848,6435072,-2845696,-7047040,12707072,-7532672,878080]),(⟨2,0,3⟩,[0,-1280,25856,-231936,1175040,-3561472,6206464,-4754944,-2168320,6944000,-4026624]),(⟨2,0,6⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨2,1,0⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨2,1,8⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,2,0⟩,[256,-7680,98048,-705536,3116544,-8477696,12870144,-5691392,-14094080,25414144,-15065344,1756160]),(⟨2,2,2⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨2,2,7⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,3,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨2,3,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,3,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,4,1⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,4,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨2,5,1⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨2,6,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨2,7,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,8,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[1152,-28416,306176,-1891328,7285632,-17538560,23426048,-5278720,-36935808,58940672,-26689536,-15247360,14436480]),(⟨3,0,1⟩,[0,-5376,95744,-755968,3457024,-9920000,17716224,-16844288,0,20099840,-21629440,7786240]),(⟨3,0,2⟩,[-768,18176,-169472,832000,-2310144,3399680,-1273344,-3994112,6603520,-3499776,394240]),(⟨3,0,3⟩,[0,7680,-106496,621568,-1937408,3291136,-2334720,-1391616,3657728,-1807872]),(⟨3,0,6⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨3,1,0⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨3,1,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨3,2,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨3,2,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨3,2,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨3,3,0⟩,[0,15360,-212992,1243136,-3874816,6582272,-4669440,-2783232,7315456,-3615744]),(⟨3,6,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨4,0,0⟩,[128,-13056,210816,-1610240,7210752,-20200960,34650368,-29854720,-5756800,42412288,-40132736,12690944]),(⟨4,1,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨4,2,1⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨4,2,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨5,0,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨5,1,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨5,2,1⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨6,0,0⟩,[512,-3072,-8192,119296,-447488,973312,-1486848,1119744,778752,-1439232]),(⟨6,0,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,0,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,0,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨6,1,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,2,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,3,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨7,0,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨8,1,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,2,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨9,0,0⟩,[0,5120,-52224,190464,-243712,-97280,328704])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,1152,-31872,401664,-3028608,15012480,-50462208,113554944,-157144320,87030144,104843136,-239496960,162587520,-4778112,-35824896,4976640]),(⟨0,0,1⟩,[-384,10752,-146688,1253120,-7268224,29547776,-84663552,166808064,-205659264,98383872,134770944,-283531520,201352576,-37834496,-14595840]),(⟨0,0,2⟩,[-128,5504,-82944,704768,-4023424,16557184,-49414144,102563840,-132687232,68282496,77644800,-163141888,108382848,-22825600]),(⟨0,0,3⟩,[1152,-28416,317696,-2085632,8689536,-23109632,36162560,-20294656,-34777728,75767552,-44094720,-13848832,18873984]),(⟨0,0,4⟩,[128,-13056,210816,-1610240,7210752,-20200960,34650368,-29854720,-5756800,42412288,-40132736,12690944]),(⟨0,0,5⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨0,0,6⟩,[512,-3072,-8192,119296,-447488,973312,-1486848,1119744,778752,-1439232]),(⟨0,0,7⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,0,8⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,0,9⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,1,0⟩,[-384,10752,-146688,1253120,-7268224,29547776,-84663552,166808064,-205659264,98383872,134770944,-283531520,201352576,-37834496,-14595840]),(⟨0,1,1⟩,[0,5376,-113664,1093632,-6317056,24224000,-63991808,115406848,-130068480,54806272,82897920,-163932160,120673280,-34684160]),(⟨0,1,2⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨0,1,3⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨0,1,6⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,2,0⟩,[-128,5504,-82944,704768,-4023424,16557184,-49414144,102563840,-132687232,68282496,77644800,-163141888,108382848,-22825600]),(⟨0,2,1⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨0,2,2⟩,[256,-7680,98048,-705536,3116544,-8477696,12870144,-5691392,-14094080,25414144,-15065344,1756160]),(⟨0,2,3⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨0,2,6⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,3,0⟩,[1152,-28416,317696,-2085632,8689536,-23109632,36162560,-20294656,-34777728,75767552,-44094720,-13848832,18873984]),(⟨0,3,1⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨0,3,2⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨0,3,3⟩,[0,15360,-212992,1243136,-3874816,6582272,-4669440,-2783232,7315456,-3615744]),(⟨0,3,6⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,4,0⟩,[128,-13056,210816,-1610240,7210752,-20200960,34650368,-29854720,-5756800,42412288,-40132736,12690944]),(⟨0,5,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨0,6,0⟩,[512,-3072,-8192,119296,-447488,973312,-1486848,1119744,778752,-1439232]),(⟨0,6,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,6,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,6,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨0,7,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨0,8,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨0,9,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨1,0,0⟩,[-384,10752,-146688,1253120,-7268224,29547776,-84663552,166808064,-205659264,98383872,134770944,-283531520,201352576,-37834496,-14595840]),(⟨1,0,1⟩,[0,5376,-113664,1093632,-6317056,24224000,-63991808,115406848,-130068480,54806272,82897920,-163932160,120673280,-34684160]),(⟨1,0,2⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨1,0,3⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨1,0,6⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨1,1,0⟩,[0,5376,-113664,1093632,-6317056,24224000,-63991808,115406848,-130068480,54806272,82897920,-163932160,120673280,-34684160]),(⟨1,2,0⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨1,2,2⟩,[0,-4608,86016,-583680,1760256,-1661952,-3757056,11950080,-11308032,1015296,3290112]),(⟨1,2,3⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨1,2,4⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨1,2,5⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨1,2,8⟩,[-2048,24576,-61440,-73728,243712]),(⟨1,3,0⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨1,3,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨1,4,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨1,5,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨1,6,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨1,8,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,0,0⟩,[-128,5504,-82944,704768,-4023424,16557184,-49414144,102563840,-132687232,68282496,77644800,-163141888,108382848,-22825600]),(⟨2,0,1⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨2,0,2⟩,[256,-7680,98048,-705536,3116544,-8477696,12870144,-5691392,-14094080,25414144,-15065344,1756160]),(⟨2,0,3⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨2,0,6⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨2,1,0⟩,[384,-9472,94720,-492288,1295232,-555008,-7510528,25831424,-39607680,23358720,16500736,-34583808,16464000]),(⟨2,1,2⟩,[0,-4608,86016,-583680,1760256,-1661952,-3757056,11950080,-11308032,1015296,3290112]),(⟨2,1,3⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,1,4⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,1,5⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨2,1,8⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,2,0⟩,[256,-7680,98048,-705536,3116544,-8477696,12870144,-5691392,-14094080,25414144,-15065344,1756160]),(⟨2,2,1⟩,[0,-4608,86016,-583680,1760256,-1661952,-3757056,11950080,-11308032,1015296,3290112]),(⟨2,2,2⟩,[4608,-87552,626688,-2199552,3689472,-218112,-12201984,25890816,-24460800,8956416]),(⟨2,2,3⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,2,4⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨2,2,7⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,3,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨2,3,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨2,3,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,4,1⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,4,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨2,5,1⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨2,6,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨2,7,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,8,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[1152,-28416,317696,-2085632,8689536,-23109632,36162560,-20294656,-34777728,75767552,-44094720,-13848832,18873984]),(⟨3,0,1⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨3,0,2⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨3,0,3⟩,[0,15360,-212992,1243136,-3874816,6582272,-4669440,-2783232,7315456,-3615744]),(⟨3,0,6⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨3,1,0⟩,[0,-9216,161792,-1257472,5652480,-15962112,28215296,-27009024,1290240,29705216,-32600064,11812864]),(⟨3,1,2⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨3,2,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨3,2,1⟩,[1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨3,2,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨3,3,0⟩,[0,15360,-212992,1243136,-3874816,6582272,-4669440,-2783232,7315456,-3615744]),(⟨3,6,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨4,0,0⟩,[128,-13056,210816,-1610240,7210752,-20200960,34650368,-29854720,-5756800,42412288,-40132736,12690944]),(⟨4,1,2⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨4,2,1⟩,[512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨4,2,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨5,0,0⟩,[-768,16896,-143616,600064,-1135104,-161792,4933120,-8749056,4435200,3444224,-3632384]),(⟨5,1,2⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨5,2,1⟩,[-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨6,0,0⟩,[512,-3072,-8192,119296,-447488,973312,-1486848,1119744,778752,-1439232]),(⟨6,0,1⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,0,2⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,0,3⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨6,1,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨6,2,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨6,3,0⟩,[0,5120,-52224,190464,-243712,-97280,328704]),(⟨7,0,0⟩,[0,-3584,50688,-295424,887296,-1303040,330240,1487360,-1415680]),(⟨7,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,0,0⟩,[-512,10240,-72192,223232,-226816,-243712,512512,-71680]),(⟨8,1,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨8,2,1⟩,[-2048,24576,-61440,-73728,243712]),(⟨9,0,0⟩,[0,5120,-52224,190464,-243712,-97280,328704])]


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
    (Poly.add (Poly.scale (K.ofRat r414) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r412*r413 : ℚ)=r414 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 12 r412 r413 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C082

#print axioms Coulomb8.Columns.C082.sound
