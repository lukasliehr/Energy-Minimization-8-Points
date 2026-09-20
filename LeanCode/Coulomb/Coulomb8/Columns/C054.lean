import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C054

def r0 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 20448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -231648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 1489056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -6073920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 16386432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -1702080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 30609408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -1841280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -7959648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 9262752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -13728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -174528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -7456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 95968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -725280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 3579936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -12036608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 27765888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -42782848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 40147328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -6225760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 6466976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 52128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 110912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -722560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 3159040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -9717440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 20957824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 26567808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -9045312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -586816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 396480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 14656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -139072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 727936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -2321408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 4461440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -251392, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -595072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 5365632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -169920, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -169536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 27040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -38464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 1437312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -4620864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 9196480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -10765632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 5789824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 671616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -174240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -22976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 274496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -1206208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 2738752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -3263552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 198720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 80640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -14656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 118144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -437568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 860032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -119360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 145536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 47104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -188672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 361600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -281728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -6912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 116512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -798848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 3519552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -10414720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 20867776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -27409920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 20869728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -751296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -444192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 169344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -3552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 17568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -114880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 37952, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -2322496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 5122368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -926176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 478048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 240352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -340256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 4192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -81792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 552128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -2040576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 4589248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -6368384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 5177184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -2261568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 103456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 13760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -13248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 400832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -1056576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 1628224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -161344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -50176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 119168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 42368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -15360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 46592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 11840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -109056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 535552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -1581056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 2843776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -407040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 132608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 125440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -65856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 42624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -62976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -30208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 1022464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -1700480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 148992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 14784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 9472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -201792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 309760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -27456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -12544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 9408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 10368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -426240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 1176192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -219136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 82304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 26880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -184704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 460032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -441856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 3968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -17760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 91872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -311616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 676416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -714048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -715200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 4311456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 1069152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -5344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 26368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -12096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 167936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -133440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -44288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 173600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -269696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -27136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 63360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -8832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 61952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -99904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -29056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -160128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 119040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 10224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -115824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 744528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -3036960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 8193216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -851040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 15304704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -920640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -3979824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 4631376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -6864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -87264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -3728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 47984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -362640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 1789968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -6018304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 13882944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -21391424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 20073664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -3112880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 3233488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 26064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -4992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 55456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -361280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 1579520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -4858720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 10478912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 13283904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -4522656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -293408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 198240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 7328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -69536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 363968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -1160704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 2230720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -125696, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -297536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 2682816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -84960, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -84768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 13520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -19232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 718656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -2310432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 4598240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -5382816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 2894912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 335808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -87120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -11488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 137248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -603104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 1369376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1631776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 99360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 40320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -7328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 59072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -218784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 430016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -59680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 72768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 23552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -94336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 180800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -140864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -288, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 58256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -399424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 1759776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -5207360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 10433888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -13704960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 10434864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -375648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -222096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 84672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -1776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 8784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -57440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 18976, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -1161248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 2561184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -463088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 239024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 120176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -170128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 2096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -40896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 276064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -1020288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 2294624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -3184192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 2588592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -1130784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 51728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 6880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -6624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 200416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -528288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 814112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -80672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -25088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 59584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 21184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 23296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 5920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 267776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -790528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 1421888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -203520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 66304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 62720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -32928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 21312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -31488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -15104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 511232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -850240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 74496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 7392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 4736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -100896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 154880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -13728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -6272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 4704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 5184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -213120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 588096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -109568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 41152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 13440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -92352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 230016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -220928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 1984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -8880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 45936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -155808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 338208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -357024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -357600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 2155728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 534576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -2672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 13184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -6048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 83968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -66720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -22144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 86800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -134848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 31680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -4416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -44032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 30976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -49952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -14528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 49216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -80064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 4992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 59520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[0,r13,r14,r15,r16,r17,r18,r19,r20,r21,-133664,r22,r23,r24],[0,r25,r26,r27,r28,r29,r30,r31,-255552,r32,r33,r34,r35],[0,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46],[0,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56],[0,r57,r47,r58,r59,r60,r61,r62,r63,r64],[0,r65,r66,r67,r68,r69,r70,r71,960],[0,r72,r73,r74,r75,r76,r77,r78],[],[],[],[],[],[0,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90],[r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[r91,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112],[r113,r114,r115,r116,r117,r118,r119,r120,r121,r122],[r113,r123,r124,r125,r126,r127,r128,r129,-3136],[],[],[],[],[],[],[0,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139],[0,r140,r141,r142,r143,r144,r145,r146,r147,r148],[0,r149,r80,r150,r151,r152,r153,r154,r155],[],[],[],[],[],[],[0,r156,r157,r158,r159,r160,r161,r162,r163],[r72,r164,r165,r166,r167,r168,r169,r170],[r72,r164,r171,r172,r173,r174,-896],[r175,r176,r177,r178,r179,-256],[r175,r180,r141,r181,256],[],[],[],[],[],[],[],[],[],[],[],[r182,r183,r184,r185,r186,r187,r188,r189,r190,-67296,r191,-23520],[r91,r65,r192,r193,r194,r195,r196,r197,r198,r199,10976],[r113,r47,r200,r201,r202,r203,r204,r205,r206,3136],[r113,r123,r124,r125,r126,r127,r128,r129,-3136],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r72,r207,r208,r209,r210,r211,r212,640],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r72,r164,r171,r172,r173,r174,-896],[],[],[],[],[],[],[],[],[r0,r213,r214,r215,r216,-768],[r175,r180,r141,r181,256],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨0,0,1⟩,[0,r72,r230,r231,r232,r233,r234,r235,r236,r237,-66832,r238,r239,r240]),(⟨0,0,2⟩,[0,r57,r241,r242,r243,r244,r245,r246,-127776,r247,r248,r249,r250]),(⟨0,0,3⟩,[0,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,0,4⟩,[0,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271]),(⟨0,0,5⟩,[0,r272,r262,r273,r274,r275,r276,r277,r278,r279]),(⟨0,0,6⟩,[0,r103,r280,r281,r282,r283,r284,r285,480]),(⟨0,0,7⟩,[0,r113,r286,r287,r288,r289,r290,r291]),(⟨0,1,0⟩,[0,r72,r230,r231,r232,r233,r234,r235,r236,r237,-66832,r238,r239,r240]),(⟨0,1,1⟩,[0,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨0,1,2⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨0,1,3⟩,[r304,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨0,1,4⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,1,5⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨0,2,0⟩,[0,r57,r241,r242,r243,r244,r245,r246,-127776,r247,r248,r249,r250]),(⟨0,2,1⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨0,2,2⟩,[0,r175,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,2,3⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,2,4⟩,[0,r13,r293,r359,r360,r361,r362,r363,r364]),(⟨0,3,0⟩,[0,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,3,1⟩,[r304,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨0,3,2⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,3,3⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨0,3,4⟩,[r113,r123,r210,r373,r374,r375,r376,r377]),(⟨0,3,5⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨0,3,6⟩,[r156,r381,r382,r0,r383,-128]),(⟨0,3,7⟩,[r156,r384,r351,r215,128]),(⟨0,4,0⟩,[0,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271]),(⟨0,4,1⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,4,2⟩,[0,r13,r293,r359,r360,r361,r362,r363,r364]),(⟨0,4,3⟩,[r113,r123,r210,r373,r374,r375,r376,r377]),(⟨0,5,0⟩,[0,r272,r262,r273,r274,r275,r276,r277,r278,r279]),(⟨0,5,1⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨0,5,3⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨0,6,0⟩,[0,r103,r280,r281,r282,r283,r284,r285,480]),(⟨0,6,3⟩,[r156,r381,r382,r0,r383,-128]),(⟨0,7,0⟩,[0,r113,r286,r287,r288,r289,r290,r291]),(⟨0,7,3⟩,[r156,r384,r351,r215,128]),(⟨1,0,0⟩,[0,r72,r230,r231,r232,r233,r234,r235,r236,r237,-66832,r238,r239,r240]),(⟨1,0,1⟩,[0,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨1,0,2⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨1,0,3⟩,[r304,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨1,0,4⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨1,0,5⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨1,1,0⟩,[0,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨1,1,1⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,-33648,r394,-11760]),(⟨1,1,2⟩,[r304,r103,r395,r396,r397,r398,r399,r400,r401,r402,5488]),(⟨1,1,3⟩,[r326,r262,r403,r404,r405,r406,r407,r408,r409,1568]),(⟨1,1,4⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨1,2,0⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨1,2,1⟩,[r304,r103,r395,r396,r397,r398,r399,r400,r401,r402,5488]),(⟨1,3,0⟩,[r304,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨1,3,1⟩,[r326,r262,r403,r404,r405,r406,r407,r408,r409,1568]),(⟨1,3,3⟩,[r113,r47,r410,r411,r412,r413,r414,320]),(⟨1,4,0⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨1,4,1⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨1,5,0⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨2,0,0⟩,[0,r57,r241,r242,r243,r244,r245,r246,-127776,r247,r248,r249,r250]),(⟨2,0,1⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨2,0,2⟩,[0,r175,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,0,3⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,0,4⟩,[0,r13,r293,r359,r360,r361,r362,r363,r364]),(⟨2,1,0⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨2,1,1⟩,[r304,r103,r395,r396,r397,r398,r399,r400,r401,r402,5488]),(⟨2,2,0⟩,[0,r175,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,3,0⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,3,3⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨2,4,0⟩,[0,r13,r293,r359,r360,r361,r362,r363,r364]),(⟨3,0,0⟩,[0,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨3,0,1⟩,[r304,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨3,0,2⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨3,0,3⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨3,0,4⟩,[r113,r123,r210,r373,r374,r375,r376,r377]),(⟨3,0,5⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨3,0,6⟩,[r156,r381,r382,r0,r383,-128]),(⟨3,0,7⟩,[r156,r384,r351,r215,128]),(⟨3,1,0⟩,[r304,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨3,1,1⟩,[r326,r262,r403,r404,r405,r406,r407,r408,r409,1568]),(⟨3,1,3⟩,[r113,r47,r410,r411,r412,r413,r414,320]),(⟨3,2,0⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨3,2,3⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨3,3,0⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨3,3,1⟩,[r113,r47,r410,r411,r412,r413,r414,320]),(⟨3,3,2⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨3,3,3⟩,[r217,r415,r416,r417,r418,-384]),(⟨3,3,4⟩,[r156,r384,r351,r215,128]),(⟨3,4,0⟩,[r113,r123,r210,r373,r374,r375,r376,r377]),(⟨3,4,3⟩,[r156,r384,r351,r215,128]),(⟨3,5,0⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨3,6,0⟩,[r156,r381,r382,r0,r383,-128]),(⟨3,7,0⟩,[r156,r384,r351,r215,128]),(⟨4,0,0⟩,[0,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271]),(⟨4,0,1⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨4,0,2⟩,[0,r13,r293,r359,r360,r361,r362,r363,r364]),(⟨4,0,3⟩,[r113,r123,r210,r373,r374,r375,r376,r377]),(⟨4,1,0⟩,[r326,r327,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨4,1,1⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨4,2,0⟩,[0,r13,r293,r359,r360,r361,r362,r363,r364]),(⟨4,3,0⟩,[r113,r123,r210,r373,r374,r375,r376,r377]),(⟨4,3,3⟩,[r156,r384,r351,r215,128]),(⟨5,0,0⟩,[0,r272,r262,r273,r274,r275,r276,r277,r278,r279]),(⟨5,0,1⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨5,0,3⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨5,1,0⟩,[r326,r130,r180,r336,r337,r338,r339,r340,-1568]),(⟨5,3,0⟩,[r113,r123,r378,r177,r379,r380,-448]),(⟨6,0,0⟩,[0,r103,r280,r281,r282,r283,r284,r285,480]),(⟨6,0,3⟩,[r156,r381,r382,r0,r383,-128]),(⟨6,3,0⟩,[r156,r381,r382,r0,r383,-128]),(⟨7,0,0⟩,[0,r113,r286,r287,r288,r289,r290,r291]),(⟨7,0,3⟩,[r156,r384,r351,r215,128]),(⟨7,3,0⟩,[r156,r384,r351,r215,128])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r419) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r420) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[0,-1024,23168,-213120,1065472,-3243648,6103808,-6565248,2727424,1212544,-814464]),(⟨4,0,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨4,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,0,3⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨4,1,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨4,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨4,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,3,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨4,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨5,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨6,0,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨7,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[0,-1024,23168,-213120,1065472,-3243648,6103808,-6565248,2727424,1212544,-814464]),(⟨0,4,1⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,4,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,4,3⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,5,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,5,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,6,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,7,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,7,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,512,-14144,169088,-1172352,5302464,-16488448,35802240,-53353088,51015424,-25247936,-674048,6696448,-2036160]),(⟨1,0,1⟩,[0,256,-7872,100864,-726080,3305472,-10055296,20784640,-28583808,23928576,-8643264,-2408448,2304960]),(⟨1,0,2⟩,[0,-512,12352,-119872,624000,-1964416,3888640,-4669952,2773632,158592,-1031744,329280]),(⟨1,0,3⟩,[0,-128,5376,-71936,467456,-1752576,4023296,-5558016,4101632,-973184,-241920]),(⟨1,1,0⟩,[0,256,-7872,100864,-726080,3305472,-10055296,20784640,-28583808,23928576,-8643264,-2408448,2304960]),(⟨1,1,1⟩,[-64,1344,-11840,61248,-207744,450944,-476032,-476800,2874304,-5338816,4989376,-1865920]),(⟨1,2,0⟩,[0,-512,12352,-119872,624000,-1964416,3888640,-4669952,2773632,158592,-1031744,329280]),(⟨1,3,0⟩,[0,-128,5376,-71936,467456,-1752576,4023296,-5558016,4101632,-973184,-241920]),(⟨1,3,3⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,4,0⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,4,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,5,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨2,0,0⟩,[0,768,-21504,257344,-1766144,7804160,-23323648,47627648,-64441344,51755520,-15356928,-8281280,5155584]),(⟨2,0,1⟩,[-64,1600,-19456,155008,-853760,3254784,-8533632,14914688,-15740096,6534080,4396672,-5092864]),(⟨2,0,2⟩,[0,-512,11840,-109056,535552,-1581056,2843776,-2849280,928256,878080,-460992]),(⟨2,0,3⟩,[0,-128,5248,-66944,410240,-1446016,3048832,-3609728,1778560,338688]),(⟨2,1,0⟩,[-64,1600,-19456,155008,-853760,3254784,-8533632,14914688,-15740096,6534080,4396672,-5092864]),(⟨2,1,1⟩,[-64,1280,-10688,52736,-169344,335872,-266880,-620032,2430400,-3775744,2612288]),(⟨2,2,0⟩,[0,-512,11840,-109056,535552,-1581056,2843776,-2849280,928256,878080,-460992]),(⟨2,3,0⟩,[0,-128,5248,-66944,410240,-1446016,3048832,-3609728,1778560,338688]),(⟨2,3,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨3,0,0⟩,[0,-1280,28928,-262400,1256576,-3469696,5178496,-1947520,-6548096,10516608,-3651456,-2083200]),(⟨3,0,1⟩,[-64,768,3008,-91648,636800,-2328576,5155200,-7178752,6252736,-3549952,1690304]),(⟨3,0,2⟩,[0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨3,0,3⟩,[0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨3,1,0⟩,[-64,768,3008,-91648,636800,-2328576,5155200,-7178752,6252736,-3549952,1690304]),(⟨3,1,1⟩,[128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨3,2,0⟩,[0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨3,3,0⟩,[0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨3,3,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,4,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨3,4,3⟩,[-512,6144,-15360,-18432,60928]),(⟨3,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,-2176,54080,-538496,2874624,-9241728,18392960,-21531264,11579648,1343232,-2439360]),(⟨4,0,1⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨4,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,0,3⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨4,1,0⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨4,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨4,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,3,0⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨4,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[0,384,-2176,-45952,548992,-2412416,5477504,-6527104,2782080,1128960]),(⟨5,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,0,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨5,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,3,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,0,0⟩,[0,1280,-29312,236288,-875136,1720064,-1671040,291072,228480]),(⟨6,0,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,3,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨7,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[0,-1024,23168,-213120,1065472,-3243648,6103808,-6565248,2727424,1212544,-814464]),(⟨0,0,5⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,0,6⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,0,7⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,1,0⟩,[0,512,-14144,169088,-1172352,5302464,-16488448,35802240,-53353088,51015424,-25247936,-674048,6696448,-2036160]),(⟨0,1,1⟩,[0,256,-7872,100864,-726080,3305472,-10055296,20784640,-28583808,23928576,-8643264,-2408448,2304960]),(⟨0,1,2⟩,[0,-512,12352,-119872,624000,-1964416,3888640,-4669952,2773632,158592,-1031744,329280]),(⟨0,1,3⟩,[0,-128,5376,-71936,467456,-1752576,4023296,-5558016,4101632,-973184,-241920]),(⟨0,1,4⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨0,1,5⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,2,0⟩,[0,768,-21504,257344,-1766144,7804160,-23323648,47627648,-64441344,51755520,-15356928,-8281280,5155584]),(⟨0,2,1⟩,[-64,1600,-19456,155008,-853760,3254784,-8533632,14914688,-15740096,6534080,4396672,-5092864]),(⟨0,2,2⟩,[0,-512,11840,-109056,535552,-1581056,2843776,-2849280,928256,878080,-460992]),(⟨0,2,3⟩,[0,-128,5248,-66944,410240,-1446016,3048832,-3609728,1778560,338688]),(⟨0,2,4⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,3,0⟩,[0,-1280,28928,-262400,1256576,-3469696,5178496,-1947520,-6548096,10516608,-3651456,-2083200]),(⟨0,3,1⟩,[-64,768,3008,-91648,636800,-2328576,5155200,-7178752,6252736,-3549952,1690304]),(⟨0,3,2⟩,[0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨0,3,3⟩,[0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨0,3,4⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,3,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,4,0⟩,[0,-2176,54080,-538496,2874624,-9241728,18392960,-21531264,11579648,1343232,-2439360]),(⟨0,4,1⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨0,4,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,4,3⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨0,5,0⟩,[0,384,-2176,-45952,548992,-2412416,5477504,-6527104,2782080,1128960]),(⟨0,5,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,5,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,6,0⟩,[0,1280,-29312,236288,-875136,1720064,-1671040,291072,228480]),(⟨0,6,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,7,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,7,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,512,-14144,169088,-1172352,5302464,-16488448,35802240,-53353088,51015424,-25247936,-674048,6696448,-2036160]),(⟨1,0,1⟩,[0,256,-7872,100864,-726080,3305472,-10055296,20784640,-28583808,23928576,-8643264,-2408448,2304960]),(⟨1,0,2⟩,[0,-512,12352,-119872,624000,-1964416,3888640,-4669952,2773632,158592,-1031744,329280]),(⟨1,0,3⟩,[0,-128,5376,-71936,467456,-1752576,4023296,-5558016,4101632,-973184,-241920]),(⟨1,0,4⟩,[0,-512,13184,-131200,674944,-1989504,3432576,-3126144,696192,921984]),(⟨1,0,5⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,1,0⟩,[0,512,-15744,201728,-1452160,6610944,-20110592,41569280,-57167616,47857152,-17286528,-4816896,4609920]),(⟨1,1,1⟩,[-128,2688,-23680,122496,-415488,901888,-952064,-953600,5748608,-10677632,9978752,-3731840]),(⟨1,1,4⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,2,0⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨1,2,1⟩,[-64,1280,-10688,52736,-169344,335872,-266880,-620032,2430400,-3775744,2612288]),(⟨1,3,0⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨1,3,1⟩,[128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨1,3,3⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,4,0⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨1,4,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,5,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨2,0,0⟩,[0,768,-21504,257344,-1766144,7804160,-23323648,47627648,-64441344,51755520,-15356928,-8281280,5155584]),(⟨2,0,1⟩,[-64,1600,-19456,155008,-853760,3254784,-8533632,14914688,-15740096,6534080,4396672,-5092864]),(⟨2,0,2⟩,[0,-512,11840,-109056,535552,-1581056,2843776,-2849280,928256,878080,-460992]),(⟨2,0,3⟩,[0,-128,5248,-66944,410240,-1446016,3048832,-3609728,1778560,338688]),(⟨2,0,4⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨2,1,0⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨2,1,1⟩,[-64,1280,-10688,52736,-169344,335872,-266880,-620032,2430400,-3775744,2612288]),(⟨2,2,0⟩,[0,-1024,23680,-218112,1071104,-3162112,5687552,-5698560,1856512,1756160,-921984]),(⟨2,3,0⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨2,3,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨3,0,0⟩,[0,-1280,28928,-262400,1256576,-3469696,5178496,-1947520,-6548096,10516608,-3651456,-2083200]),(⟨3,0,1⟩,[-64,768,3008,-91648,636800,-2328576,5155200,-7178752,6252736,-3549952,1690304]),(⟨3,0,2⟩,[0,1024,-20608,152192,-536192,1023104,-1003904,208768,307328,-131712]),(⟨3,0,3⟩,[0,256,-9728,103680,-471552,1100544,-1286656,466688,96768]),(⟨3,0,4⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨3,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨3,1,0⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨3,1,1⟩,[128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨3,1,3⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨3,2,0⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨3,2,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,3,0⟩,[0,512,-19456,207360,-943104,2201088,-2573312,933376,193536]),(⟨3,3,3⟩,[-1024,13312,-43008,-6144,158720,-121856]),(⟨3,3,4⟩,[-512,6144,-15360,-18432,60928]),(⟨3,4,0⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨3,4,3⟩,[-512,6144,-15360,-18432,60928]),(⟨3,5,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,6,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,-2176,54080,-538496,2874624,-9241728,18392960,-21531264,11579648,1343232,-2439360]),(⟨4,0,1⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨4,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,0,3⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨4,1,0⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨4,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨4,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,3,0⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨4,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[0,384,-2176,-45952,548992,-2412416,5477504,-6527104,2782080,1128960]),(⟨5,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,0,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨5,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,3,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,0,0⟩,[0,1280,-29312,236288,-875136,1720064,-1671040,291072,228480]),(⟨6,0,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,3,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨7,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,-1536,40896,-463296,2978112,-12147840,32772864,-57870720,61218816,-25777920,-15919296,18525504,-27456,-2443392]),(⟨0,0,1⟩,[0,512,-14912,191936,-1450560,7159872,-24073216,55531776,-85565696,80294656,-31812032,-12451520,12933952,729792]),(⟨0,0,2⟩,[0,768,-19968,221824,-1445120,6318080,-19434880,41915648,-60821376,53135616,-18090624,-8215424,5550720]),(⟨0,0,3⟩,[0,-1280,29312,-278144,1455872,-4642816,8922880,-8547328,-1190144,10731264,-5777280,-2373504]),(⟨0,0,4⟩,[0,-2176,54080,-538496,2874624,-9241728,18392960,-21531264,11579648,1343232,-2439360]),(⟨0,0,5⟩,[0,384,-2176,-45952,548992,-2412416,5477504,-6527104,2782080,1128960]),(⟨0,0,6⟩,[0,1280,-29312,236288,-875136,1720064,-1671040,291072,228480]),(⟨0,0,7⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,1,0⟩,[0,512,-14912,191936,-1450560,7159872,-24073216,55531776,-85565696,80294656,-31812032,-12451520,12933952,729792]),(⟨0,1,1⟩,[0,704,-19584,233024,-1597696,7039104,-20829440,41735552,-54819840,41739456,-10518144,-6218688,2370816]),(⟨0,1,2⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨0,1,3⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨0,1,4⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨0,1,5⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,2,0⟩,[0,768,-19968,221824,-1445120,6318080,-19434880,41915648,-60821376,53135616,-18090624,-8215424,5550720]),(⟨0,2,1⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨0,2,2⟩,[0,-1024,23680,-218112,1071104,-3162112,5687552,-5698560,1856512,1756160,-921984]),(⟨0,2,3⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨0,2,4⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,3,0⟩,[0,-1280,29312,-278144,1455872,-4642816,8922880,-8547328,-1190144,10731264,-5777280,-2373504]),(⟨0,3,1⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨0,3,2⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨0,3,3⟩,[0,-256,-7168,145152,-852480,2352384,-3067904,1152256,376320]),(⟨0,3,4⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨0,3,5⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,3,6⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,3,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,4,0⟩,[0,-2176,54080,-538496,2874624,-9241728,18392960,-21531264,11579648,1343232,-2439360]),(⟨0,4,1⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨0,4,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨0,4,3⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨0,5,0⟩,[0,384,-2176,-45952,548992,-2412416,5477504,-6527104,2782080,1128960]),(⟨0,5,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨0,5,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,6,0⟩,[0,1280,-29312,236288,-875136,1720064,-1671040,291072,228480]),(⟨0,6,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,7,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨0,7,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,512,-14912,191936,-1450560,7159872,-24073216,55531776,-85565696,80294656,-31812032,-12451520,12933952,729792]),(⟨1,0,1⟩,[0,704,-19584,233024,-1597696,7039104,-20829440,41735552,-54819840,41739456,-10518144,-6218688,2370816]),(⟨1,0,2⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨1,0,3⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨1,0,4⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨1,0,5⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,1,0⟩,[0,704,-19584,233024,-1597696,7039104,-20829440,41735552,-54819840,41739456,-10518144,-6218688,2370816]),(⟨1,1,1⟩,[-192,4032,-35520,183744,-623232,1352832,-1428096,-1430400,8622912,-16016448,14968128,-5597760]),(⟨1,1,2⟩,[-64,1280,-10688,52736,-169344,335872,-266880,-620032,2430400,-3775744,2612288]),(⟨1,1,3⟩,[128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨1,1,4⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,2,0⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨1,2,1⟩,[-64,1280,-10688,52736,-169344,335872,-266880,-620032,2430400,-3775744,2612288]),(⟨1,3,0⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨1,3,1⟩,[128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨1,3,3⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,4,0⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨1,4,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨1,5,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨2,0,0⟩,[0,768,-19968,221824,-1445120,6318080,-19434880,41915648,-60821376,53135616,-18090624,-8215424,5550720]),(⟨2,0,1⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨2,0,2⟩,[0,-1024,23680,-218112,1071104,-3162112,5687552,-5698560,1856512,1756160,-921984]),(⟨2,0,3⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨2,0,4⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨2,1,0⟩,[-64,1088,-7104,35136,-229760,1290368,-4644992,10244736,-12966464,6692672,3364928,-4763584]),(⟨2,1,1⟩,[-64,1280,-10688,52736,-169344,335872,-266880,-620032,2430400,-3775744,2612288]),(⟨2,2,0⟩,[0,-1024,23680,-218112,1071104,-3162112,5687552,-5698560,1856512,1756160,-921984]),(⟨2,3,0⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨2,3,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨3,0,0⟩,[0,-1280,29312,-278144,1455872,-4642816,8922880,-8547328,-1190144,10731264,-5777280,-2373504]),(⟨3,0,1⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨3,0,2⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨3,0,3⟩,[0,-256,-7168,145152,-852480,2352384,-3067904,1152256,376320]),(⟨3,0,4⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨3,0,5⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,0,6⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨3,1,0⟩,[-64,640,8384,-163584,1104256,-4081152,9178496,-12736768,10354368,-4523136,1448384]),(⟨3,1,1⟩,[128,-2176,14336,-54272,126720,-123648,-176128,867328,-1398656,746368]),(⟨3,1,3⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨3,2,0⟩,[0,896,-15360,85248,-125952,-422912,2044928,-3400960,2085888,206976]),(⟨3,2,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,3,0⟩,[0,-256,-7168,145152,-852480,2352384,-3067904,1152256,376320]),(⟨3,3,1⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨3,3,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,3,3⟩,[-1536,19968,-64512,-9216,238080,-182784]),(⟨3,3,4⟩,[-512,6144,-15360,-18432,60928]),(⟨3,4,0⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨3,4,3⟩,[-512,6144,-15360,-18432,60928]),(⟨3,5,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,6,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,-2176,54080,-538496,2874624,-9241728,18392960,-21531264,11579648,1343232,-2439360]),(⟨4,0,1⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨4,0,2⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,0,3⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨4,1,0⟩,[128,-2688,27520,-185472,801664,-2113152,3256448,-2258816,-702464,1668352]),(⟨4,1,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨4,2,0⟩,[0,1024,-19584,132608,-403584,619520,-384384,-175616,131712]),(⟨4,3,0⟩,[256,-4096,15872,36096,-369408,920064,-883712,55552]),(⟨4,3,3⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[0,384,-2176,-45952,548992,-2412416,5477504,-6527104,2782080,1128960]),(⟨5,0,1⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,0,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨5,1,0⟩,[128,-2048,12288,-41984,84736,-38912,-215040,652288,-746368]),(⟨5,3,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,0,0⟩,[0,1280,-29312,236288,-875136,1720064,-1671040,291072,228480]),(⟨6,0,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,3,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨7,0,0⟩,[0,256,-9472,94208,-377344,723200,-563456,-96768]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928])]


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
    (Poly.add (Poly.scale (K.ofRat r421) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 9).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r419*r420 : ℚ)=r421 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 9 r419 r420 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=9 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 9).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C054

#print axioms Coulomb8.Columns.C054.sound
