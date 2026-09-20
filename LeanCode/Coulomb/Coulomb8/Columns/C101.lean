import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C101

def r0 : ℚ := { num := -12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -6184960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 7540736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -17027072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 1070280704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -2697867264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 646721536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -668614656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 2369859584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 31412224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -434470912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 11665408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 462848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -7393280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 9498624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -374902784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 1387819008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -3401027584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 764530688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -4889772032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 1797439488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 477175808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -46301184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -684032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 7704576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -44810240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 19595264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -23158784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -254124032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 64634880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -1272569856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 332500992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 27979776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -909312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 13066240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -96690176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 407248896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -999825408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 1347821568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -758128640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -81002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 13271040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 167936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 405504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -18051072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 17412096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -366727168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 515477504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -14569472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -7970816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 446464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -5599232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 30904320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -75337728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 528384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 1789952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -1290240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -1998848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 13828096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -38862848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 37453824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 294912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -110592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1425408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -737280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 4841472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -389890048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 1263796224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -380493824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 3332182016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -1887080448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -249741312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 82518016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 110592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 897024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -14487552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 68390912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -21565440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 175476736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -197898240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 389373952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -55476224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -2174976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 14036992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -9244672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 207810560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -57634816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 388370432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -98512896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -8335360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 8192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -1056768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 1056768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -26746880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 52666368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -29581312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -92102656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 1138688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -2109440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 9023488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -1175552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -28672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 876544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -8871936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 6004736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -91840512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 3743744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 71098368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -21962752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 15769600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -2248704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 20549632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -66121728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 12537856, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -56422400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 5951488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 1679360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -483328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 27418624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -59678720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 58449920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -385024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 344064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -25223168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 151134208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -564486144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 1298145280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -1595580416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 342384640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 1503289344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -11247616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 61440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -966656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 48439296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -165404672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 313835520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -268845056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -117018624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 2560000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -2187264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 2482176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -68542464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 131522560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -63578112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -164208640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 1679360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -147456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 9592832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -39878656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 69165056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -22790144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -303104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 1785856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -7831552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 17498112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -12582912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -44318720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 1146880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 561152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -3952640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 9277440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 6533120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -167936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -3092480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 3770368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -8513536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 535140352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -1348933632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 323360768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -334307328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 1184929792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 15706112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -217235456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 5832704, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 231424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -3696640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 4749312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -187451392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 693909504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -1700513792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 382265344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -2444886016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 898719744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 238587904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -23150592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -342016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 3852288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -22405120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 9797632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -11579392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -127062016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 32317440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -636284928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 166250496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 13989888, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -454656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -48345088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 203624448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -499912704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 673910784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -379064320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -40501248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 6635520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 83968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 202752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -9025536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 8706048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -183363584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 257738752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -7284736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -3985408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 223232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2799616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 15452160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -37668864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 264192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 894976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -645120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -999424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 6914048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -19431424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 18726912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 147456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -55296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 712704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -368640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 2420736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -194945024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 631898112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -190246912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 1666091008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -943540224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -124870656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 41259008, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 55296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 448512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -7243776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 34195456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -10782720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 87738368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -98949120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 194686976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -27738112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -1087488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 7018496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -4622336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 103905280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -28817408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 194185216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -49256448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -4167680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -528384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 528384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -13373440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 26333184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -14790656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -46051328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 569344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -47104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -1054720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -59392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 4511744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -587776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -14336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 3719168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -49152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 438272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -4435968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 3002368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -45920256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 1871872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 35549184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -10981376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 7884800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -2048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -1124352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 10274816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -33060864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 6268928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -28211200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 2975744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 684032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 839680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -241664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 13709312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -29839360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 29224960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -192512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 172032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -12611584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 75567104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -282243072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 649072640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -797790208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 171192320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 751644672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -5623808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 30720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -483328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 24219648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -82702336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 156917760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -134422528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -58509312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 1280000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 53248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -1093632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 1241088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -34271232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 65761280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -31789056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -82104320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 839680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 20480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -73728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 4796416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -19939328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 34582528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -11395072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -151552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 892928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -3915776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 8749056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -6291456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -22159360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 573440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -6144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 280576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -1976320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 4638720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 3266560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -83968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[0,r0,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23],[0,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[0,r24,r35,r36,r37,r38,r39,r40,r41,r42,r43],[0,r0,r44,r45,r46,r47,r48,r49,r50,r51],[0,r0,r52,r53,r54,r55,r56,r57,r58],[0,0,r59,r60,r61,r62,r63,r64],[],[],[],[],[],[],[r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[0,r0,r77,r78,r79,r80,r81,r82,r83,r84,r85],[r86,r87,r88,r89,r90,r91,r92,r93,r94,r95],[0,r96,r97,r98,r99,r100,r101,r102,r103],[r65,r104,r105,r106,r107,r108,r109,r110],[0,r111,r112,r113,r114,r115,r116],[],[],[],[],[],[0,r111,r117,r118,r119,r120,r121,r122,r123,r124],[0,r125,r126,r127,r128,r129,r130,r131,r132],[0,r133,r134,r135,r136,r137,r138,-8192],[],[],[],[],[],[],[r133,r139,r140,r141,r142,r143,r144,r145],[0,r111,r112,r113,r114,r115,r116],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155],[r156,r157,r158,r159,r160,r161,r162,r163,r164,r165],[0,r166,r167,r168,r169,r170,r171,r172,r173],[0,r174,r175,r176,r177,r178,r179,r180],[],[],[],[],[],[],[r133,r181,r182,r183,r184,r185,r186,r187,-57344],[r65,r188,r189,r190,r191,r192,r193,r194],[r86,r195,r196,r197,r198,r199,8192],[],[],[],[],[],[0,r200,r201,r202,r203,r204,r205],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218]),(⟨0,0,1⟩,[0,r206,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨0,0,2⟩,[0,r125,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239]),(⟨0,0,3⟩,[0,r125,r240,r193,r241,r242,r243,r244,r245,r246,r247]),(⟨0,0,4⟩,[0,r206,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,0,5⟩,[0,r206,r256,r257,r258,r259,r260,r261,r262]),(⟨0,0,6⟩,[0,0,r263,r264,r265,r266,r267,r268]),(⟨0,1,0⟩,[0,r206,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨0,1,1⟩,[r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨0,1,2⟩,[0,r206,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,1,3⟩,[r156,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,1,4⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨0,1,5⟩,[r269,r307,r308,r309,r310,r311,r312,r313]),(⟨0,1,6⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨0,2,0⟩,[0,r125,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239]),(⟨0,2,1⟩,[0,r206,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,2,2⟩,[0,r314,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨0,2,3⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,2,4⟩,[0,r65,r336,r337,r338,r339,r340,-4096]),(⟨0,3,0⟩,[0,r125,r240,r193,r241,r242,r243,r244,r245,r246,r247]),(⟨0,3,1⟩,[r156,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,3,2⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,3,3⟩,[r65,r104,r341,r342,r343,r344,r345,r346]),(⟨0,3,4⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨0,4,0⟩,[0,r206,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,4,1⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨0,4,2⟩,[0,r65,r336,r337,r338,r339,r340,-4096]),(⟨0,4,3⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨0,5,0⟩,[0,r206,r256,r257,r258,r259,r260,r261,r262]),(⟨0,5,1⟩,[r269,r307,r308,r309,r310,r311,r312,r313]),(⟨0,6,0⟩,[0,0,r263,r264,r265,r266,r267,r268]),(⟨0,6,1⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨1,0,0⟩,[0,r206,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229]),(⟨1,0,1⟩,[r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨1,0,2⟩,[0,r206,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨1,0,3⟩,[r156,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨1,0,4⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨1,0,5⟩,[r269,r307,r308,r309,r310,r311,r312,r313]),(⟨1,0,6⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨1,1,0⟩,[r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨1,1,1⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356]),(⟨1,1,2⟩,[r357,r358,r96,r359,r360,r361,r362,r363,r364,r365]),(⟨1,1,3⟩,[0,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨1,1,4⟩,[0,r374,r375,r376,r377,r378,r379,r380]),(⟨1,2,0⟩,[0,r206,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨1,2,1⟩,[r357,r358,r96,r359,r360,r361,r362,r363,r364,r365]),(⟨1,2,2⟩,[r65,r146,r381,r382,r383,r384,r385,r386,-28672]),(⟨1,2,3⟩,[r269,r387,r388,r389,r390,r391,r392,r393]),(⟨1,2,4⟩,[r156,r394,r25,r395,r396,r397,4096]),(⟨1,3,0⟩,[r156,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨1,3,1⟩,[0,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨1,3,2⟩,[r269,r387,r388,r389,r390,r391,r392,r393]),(⟨1,3,3⟩,[0,r111,r112,r113,r114,r115,r116]),(⟨1,4,0⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨1,4,1⟩,[0,r374,r375,r376,r377,r378,r379,r380]),(⟨1,4,2⟩,[r156,r394,r25,r395,r396,r397,4096]),(⟨1,5,0⟩,[r269,r307,r308,r309,r310,r311,r312,r313]),(⟨1,6,0⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨2,0,0⟩,[0,r125,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239]),(⟨2,0,1⟩,[0,r206,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨2,0,2⟩,[0,r314,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨2,0,3⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨2,0,4⟩,[0,r65,r336,r337,r338,r339,r340,-4096]),(⟨2,1,0⟩,[0,r206,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨2,1,1⟩,[r357,r358,r96,r359,r360,r361,r362,r363,r364,r365]),(⟨2,1,2⟩,[r65,r146,r381,r382,r383,r384,r385,r386,-28672]),(⟨2,1,3⟩,[r269,r387,r388,r389,r390,r391,r392,r393]),(⟨2,1,4⟩,[r156,r394,r25,r395,r396,r397,4096]),(⟨2,2,0⟩,[0,r314,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨2,2,1⟩,[r65,r146,r381,r382,r383,r384,r385,r386,-28672]),(⟨2,3,0⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨2,3,1⟩,[r269,r387,r388,r389,r390,r391,r392,r393]),(⟨2,4,0⟩,[0,r65,r336,r337,r338,r339,r340,-4096]),(⟨2,4,1⟩,[r156,r394,r25,r395,r396,r397,4096]),(⟨3,0,0⟩,[0,r125,r240,r193,r241,r242,r243,r244,r245,r246,r247]),(⟨3,0,1⟩,[r156,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨3,0,2⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨3,0,3⟩,[r65,r104,r341,r342,r343,r344,r345,r346]),(⟨3,0,4⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨3,1,0⟩,[r156,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨3,1,1⟩,[0,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨3,1,2⟩,[r269,r387,r388,r389,r390,r391,r392,r393]),(⟨3,1,3⟩,[0,r111,r112,r113,r114,r115,r116]),(⟨3,2,0⟩,[0,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨3,2,1⟩,[r269,r387,r388,r389,r390,r391,r392,r393]),(⟨3,3,0⟩,[r65,r104,r341,r342,r343,r344,r345,r346]),(⟨3,3,1⟩,[0,r111,r112,r113,r114,r115,r116]),(⟨3,4,0⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨4,0,0⟩,[0,r206,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨4,0,1⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨4,0,2⟩,[0,r65,r336,r337,r338,r339,r340,-4096]),(⟨4,0,3⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨4,1,0⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨4,1,1⟩,[0,r374,r375,r376,r377,r378,r379,r380]),(⟨4,1,2⟩,[r156,r394,r25,r395,r396,r397,4096]),(⟨4,2,0⟩,[0,r65,r336,r337,r338,r339,r340,-4096]),(⟨4,2,1⟩,[r156,r394,r25,r395,r396,r397,4096]),(⟨4,3,0⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨5,0,0⟩,[0,r206,r256,r257,r258,r259,r260,r261,r262]),(⟨5,0,1⟩,[r269,r307,r308,r309,r310,r311,r312,r313]),(⟨5,1,0⟩,[r269,r307,r308,r309,r310,r311,r312,r313]),(⟨6,0,0⟩,[0,0,r263,r264,r265,r266,r267,r268]),(⟨6,0,1⟩,[0,r314,r315,r316,r317,r318,r319]),(⟨6,1,0⟩,[0,r314,r315,r316,r317,r318,r319])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r398) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r399) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[0,6144,-186368,2316288,-15538176,62146560,-152029184,215386112,-144263168,18202624,1376256]),(⟨3,0,1⟩,[-2048,51200,-546816,3500032,-15452160,46995456,-90032128,93976576,-34607104,-12271616]),(⟨3,0,2⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,0,3⟩,[2048,-47104,419840,-2054144,6854656,-14919680,14612480,-673792]),(⟨3,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[-2048,51200,-546816,3500032,-15452160,46995456,-90032128,93976576,-34607104,-12271616]),(⟨3,1,1⟩,[0,24576,-487424,3686400,-13783040,25321472,-9441280,-42795008,52154368]),(⟨3,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,2,0⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,3,0⟩,[2048,-47104,419840,-2054144,6854656,-14919680,14612480,-673792]),(⟨3,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[0,0,-36864,909312,-8630272,41091072,-105705472,142172160,-77910016,-4472832]),(⟨4,0,1⟩,[0,12288,-249856,2011136,-8605696,20713472,-21884928,-8318976,26808320]),(⟨4,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,0⟩,[0,12288,-249856,2011136,-8605696,20713472,-21884928,-8318976,26808320]),(⟨4,1,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨4,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,0,0⟩,[0,-6144,174080,-1832960,8767488,-18302976,10811392,6379520,301056]),(⟨5,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,0,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨6,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544])]

noncomputable def partial12 : Poly := [(⟨1,0,3⟩,[-2048,51200,-509952,2590720,-6821888,5904384,15673344,-48195584,43302912,-7798784]),(⟨1,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[2048,-55296,626688,-3969024,15572992,-37683200,43888640,38211584,-249407488,431773696,-318717952,54591488]),(⟨1,1,1⟩,[0,-12288,262144,-2236416,10190848,-26689536,33013760,27107328,-181403648,292024320,-177422336]),(⟨1,1,2⟩,[-2048,51200,-479232,2125824,-4644864,2752512,13553664,-38105088,25389056,11941888]),(⟨1,1,3⟩,[0,28672,-516096,3362816,-9945088,10227712,19537920,-72208384,66289664]),(⟨1,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,2,0⟩,[0,-12288,262144,-2236416,10190848,-26689536,33013760,27107328,-181403648,292024320,-177422336]),(⟨1,2,1⟩,[0,-4096,98304,-892928,3915776,-8749056,6291456,22159360,-68239360,58003456]),(⟨1,2,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,3,0⟩,[-4096,102400,-989184,4716544,-11466752,8656896,29227008,-86300672,68691968,4143104]),(⟨1,3,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,3,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,4,0⟩,[0,28672,-516096,3362816,-9945088,10227712,19537920,-72208384,66289664]),(⟨1,4,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[0,6144,-182272,2246656,-15108096,61126656,-152672256,223467520,-155752448,7671808,31424512,-6422528]),(⟨2,0,1⟩,[0,0,-36864,884736,-8351744,40165376,-105967616,148815872,-85954560,-14622720,20873216]),(⟨2,0,2⟩,[0,-6144,169984,-1771520,8550400,-18585600,12765184,6694912,-4315136,-1404928]),(⟨2,0,3⟩,[0,12288,-188416,708608,1507328,-14757888,33071104,-34590720,20529152]),(⟨2,0,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[0,-12288,225280,-1351680,1839104,13475840,-72953856,175923200,-267358208,277401600,-156549120]),(⟨2,1,1⟩,[0,-4096,86016,-565248,602112,6971392,-28528640,51601408,-66662400,51179520]),(⟨2,1,3⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[0,-10240,268288,-2664448,12466176,-27334656,19056640,28854272,-72554496,56598528]),(⟨2,2,1⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,3,0⟩,[0,12288,-188416,708608,1507328,-14757888,33071104,-34590720,20529152]),(⟨2,3,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,4,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[0,6144,-223232,3201024,-23889920,102311936,-257996800,364201984,-230217728,3579904,22249472]),(⟨3,0,1⟩,[-2048,51200,-559104,3827712,-18765824,62715904,-124852224,123418624,-33030144,-19095552]),(⟨3,0,2⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,0,3⟩,[4096,-94208,790528,-3108864,6795264,-10407936,10498048,-2379776]),(⟨3,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[-4096,102400,-1038336,5953536,-23410688,65468416,-111298560,85313536,-7641088,-7153664]),(⟨3,1,1⟩,[0,36864,-815104,7000064,-29503488,60141568,-38883328,-44371968,58978304]),(⟨3,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,2,0⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,3,0⟩,[4096,-94208,790528,-3108864,6795264,-10407936,10498048,-2379776]),(⟨3,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[0,-6144,133120,-862208,-79872,22505472,-92940288,148867072,-82225152,-5877760]),(⟨4,0,1⟩,[0,12288,-249856,2011136,-8605696,20713472,-21884928,-8318976,26808320]),(⟨4,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,1,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨4,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨5,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,0,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨6,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[0,6144,-186368,2316288,-15538176,62146560,-152029184,215386112,-144263168,18202624,1376256]),(⟨0,3,1⟩,[-2048,51200,-546816,3500032,-15452160,46995456,-90032128,93976576,-34607104,-12271616]),(⟨0,3,2⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨0,3,3⟩,[2048,-47104,419840,-2054144,6854656,-14919680,14612480,-673792]),(⟨0,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,4,0⟩,[0,0,-36864,909312,-8630272,41091072,-105705472,142172160,-77910016,-4472832]),(⟨0,4,1⟩,[0,12288,-249856,2011136,-8605696,20713472,-21884928,-8318976,26808320]),(⟨0,4,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,5,0⟩,[0,-6144,174080,-1832960,8767488,-18302976,10811392,6379520,301056]),(⟨0,5,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,6,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨0,6,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[0,-6144,194560,-2652160,20723712,-103704576,348006400,-787015680,1156098048,-985669632,323878912,88866816,-29360128]),(⟨1,0,1⟩,[2048,-55296,663552,-4927488,25939968,-99893248,273326080,-497258496,517187584,-153298944,-207503360,150011904]),(⟨1,0,2⟩,[0,-6144,79872,-83968,-2942976,18376704,-53188608,104523776,-183072768,260313088,-183844864]),(⟨1,0,3⟩,[-4096,102400,-1038336,5781504,-20412416,47093760,-61196288,22571008,27076608,-17876992]),(⟨1,0,4⟩,[0,28672,-516096,3362816,-9945088,10227712,19537920,-72208384,66289664]),(⟨1,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[2048,-55296,663552,-4927488,25939968,-99893248,273326080,-497258496,517187584,-153298944,-207503360,150011904]),(⟨1,1,1⟩,[0,-24576,536576,-4825088,24432640,-77725696,149704704,-111386624,-192729088,533045248,-386039808]),(⟨1,1,2⟩,[-2048,47104,-380928,1232896,-729088,-5996544,19845120,-15945728,-42850304,69945344]),(⟨1,1,3⟩,[0,28672,-516096,3362816,-9945088,10227712,19537920,-72208384,66289664]),(⟨1,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,2,0⟩,[0,-6144,79872,-83968,-2942976,18376704,-53188608,104523776,-183072768,260313088,-183844864]),(⟨1,2,1⟩,[-2048,47104,-380928,1232896,-729088,-5996544,19845120,-15945728,-42850304,69945344]),(⟨1,2,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,3,0⟩,[-4096,102400,-1075200,6690816,-29042688,88184832,-166901760,164743168,-50833408,-22349824]),(⟨1,3,1⟩,[0,40960,-765952,5373952,-18550784,30941184,-2347008,-80527360,93097984]),(⟨1,3,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,4,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨1,4,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨1,4,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[0,6144,-145408,1288192,-4741120,-1083392,76765184,-312002560,610842624,-577400832,142639104,88997888]),(⟨2,0,1⟩,[0,-12288,237568,-1703936,5890048,-10870784,10723328,10321920,-97280000,226398208,-187744256]),(⟨2,0,2⟩,[0,-10240,268288,-2664448,12466176,-27334656,19056640,28854272,-72554496,56598528]),(⟨2,0,3⟩,[0,12288,-188416,708608,1507328,-14757888,33071104,-34590720,20529152]),(⟨2,0,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[0,-12288,237568,-1703936,5890048,-10870784,10723328,10321920,-97280000,226398208,-187744256]),(⟨2,1,1⟩,[0,-20480,536576,-5509120,28864512,-85454848,143364096,-96317440,-83898368,140378112]),(⟨2,1,2⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,1,3⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[0,-10240,268288,-2664448,12466176,-27334656,19056640,28854272,-72554496,56598528]),(⟨2,2,1⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,3,0⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨2,3,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,4,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[0,12288,-405504,5353472,-37023744,147378176,-344199168,441618432,-231886848,-28131328,15826944]),(⟨3,0,1⟩,[-4096,102400,-1038336,5953536,-23410688,65468416,-111298560,85313536,-7641088,-7153664]),(⟨3,0,2⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,0,3⟩,[4096,-94208,790528,-3108864,6795264,-10407936,10498048,-2379776]),(⟨3,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[-4096,102400,-1038336,5953536,-23410688,65468416,-111298560,85313536,-7641088,-7153664]),(⟨3,1,1⟩,[0,36864,-815104,7000064,-29503488,60141568,-38883328,-44371968,58978304]),(⟨3,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,2,0⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,3,0⟩,[4096,-94208,839680,-4108288,13709312,-29839360,29224960,-1347584]),(⟨3,3,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[0,-6144,83968,202752,-9025536,60942336,-183363584,257738752,-123840512,-27897856]),(⟨4,0,1⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,1,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨4,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨5,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,0,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨6,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-6144,194560,-2652160,20723712,-103704576,348006400,-787015680,1156098048,-985669632,323878912,88866816,-29360128]),(⟨0,1,1⟩,[2048,-55296,663552,-4927488,25939968,-99893248,273326080,-497258496,517187584,-153298944,-207503360,150011904]),(⟨0,1,2⟩,[0,-6144,79872,-83968,-2942976,18376704,-53188608,104523776,-183072768,260313088,-183844864]),(⟨0,1,3⟩,[-4096,102400,-1038336,5781504,-20412416,47093760,-61196288,22571008,27076608,-17876992]),(⟨0,1,4⟩,[0,28672,-516096,3362816,-9945088,10227712,19537920,-72208384,66289664]),(⟨0,1,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,1,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,2,0⟩,[0,6144,-145408,1288192,-4741120,-1083392,76765184,-312002560,610842624,-577400832,142639104,88997888]),(⟨0,2,1⟩,[0,-12288,237568,-1703936,5890048,-10870784,10723328,10321920,-97280000,226398208,-187744256]),(⟨0,2,2⟩,[0,-10240,268288,-2664448,12466176,-27334656,19056640,28854272,-72554496,56598528]),(⟨0,2,3⟩,[0,12288,-188416,708608,1507328,-14757888,33071104,-34590720,20529152]),(⟨0,2,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,3,0⟩,[0,12288,-405504,5353472,-37023744,147378176,-344199168,441618432,-231886848,-28131328,15826944]),(⟨0,3,1⟩,[-4096,102400,-1038336,5953536,-23410688,65468416,-111298560,85313536,-7641088,-7153664]),(⟨0,3,2⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨0,3,3⟩,[4096,-94208,790528,-3108864,6795264,-10407936,10498048,-2379776]),(⟨0,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,4,0⟩,[0,-6144,83968,202752,-9025536,60942336,-183363584,257738752,-123840512,-27897856]),(⟨0,4,1⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨0,4,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,4,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,5,0⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨0,5,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,6,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨0,6,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[0,-6144,194560,-2652160,20723712,-103704576,348006400,-787015680,1156098048,-985669632,323878912,88866816,-29360128]),(⟨1,0,1⟩,[2048,-55296,663552,-4927488,25939968,-99893248,273326080,-497258496,517187584,-153298944,-207503360,150011904]),(⟨1,0,2⟩,[0,-6144,79872,-83968,-2942976,18376704,-53188608,104523776,-183072768,260313088,-183844864]),(⟨1,0,3⟩,[-4096,102400,-1038336,5781504,-20412416,47093760,-61196288,22571008,27076608,-17876992]),(⟨1,0,4⟩,[0,28672,-516096,3362816,-9945088,10227712,19537920,-72208384,66289664]),(⟨1,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[2048,-55296,700416,-5885952,36306944,-162103296,502763520,-1032728576,1283782656,-738371584,-96288768,245432320]),(⟨1,1,1⟩,[0,-36864,811008,-7413760,38674432,-128761856,266395648,-249880576,-204054528,774066176,-594657280]),(⟨1,1,2⟩,[-2048,43008,-282624,339968,3186688,-14745600,26136576,6213632,-111089664,127948800]),(⟨1,1,3⟩,[0,40960,-753664,5038080,-15122432,14835712,31981568,-106684416,91635712]),(⟨1,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,2,0⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨1,2,1⟩,[-2048,30720,57344,-3383296,24219648,-82702336,156917760,-134422528,-58509312,152320000]),(⟨1,2,2⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨1,2,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,2,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,3,0⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨1,3,1⟩,[0,53248,-1093632,8687616,-34271232,65761280,-31789056,-82104320,99921920]),(⟨1,3,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,4,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨1,4,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨1,4,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[0,6144,-145408,1288192,-4741120,-1083392,76765184,-312002560,610842624,-577400832,142639104,88997888]),(⟨2,0,1⟩,[0,-12288,237568,-1703936,5890048,-10870784,10723328,10321920,-97280000,226398208,-187744256]),(⟨2,0,2⟩,[0,-10240,268288,-2664448,12466176,-27334656,19056640,28854272,-72554496,56598528]),(⟨2,0,3⟩,[0,12288,-188416,708608,1507328,-14757888,33071104,-34590720,20529152]),(⟨2,0,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨2,1,1⟩,[-2048,30720,57344,-3383296,24219648,-82702336,156917760,-134422528,-58509312,152320000]),(⟨2,1,2⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,1,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[0,-16384,438272,-4435968,21016576,-45920256,31821824,35549184,-76869632,55193600]),(⟨2,2,1⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,3,0⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨2,3,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,4,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[0,12288,-405504,5353472,-37023744,147378176,-344199168,441618432,-231886848,-28131328,15826944]),(⟨3,0,1⟩,[-4096,102400,-1038336,5953536,-23410688,65468416,-111298560,85313536,-7641088,-7153664]),(⟨3,0,2⟩,[0,6144,-63488,-157696,3590144,-13694976,23255040,-28096512,25647104]),(⟨3,0,3⟩,[4096,-94208,790528,-3108864,6795264,-10407936,10498048,-2379776]),(⟨3,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨3,1,1⟩,[0,53248,-1093632,8687616,-34271232,65761280,-31789056,-82104320,99921920]),(⟨3,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,1,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,2,0⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨3,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,3,0⟩,[4096,-94208,839680,-4108288,13709312,-29839360,29224960,-1347584]),(⟨3,3,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[0,-6144,83968,202752,-9025536,60942336,-183363584,257738752,-123840512,-27897856]),(⟨4,0,1⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,1,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨4,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨5,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,0,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨6,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-6144,208896,-3092480,26392576,-144730112,535140352,-1348933632,2263525376,-2340151296,1184929792,15706112,-217235456,40828928]),(⟨0,0,1⟩,[0,-6144,231424,-3696640,33245184,-187451392,693909504,-1700513792,2675857408,-2444886016,898719744,238587904,-162054144]),(⟨0,0,2⟩,[0,12288,-342016,3852288,-22405120,68583424,-81055744,-127062016,549396480,-636284928,166250496,97929216]),(⟨0,0,3⟩,[0,12288,-454656,6533120,-48345088,203624448,-499912704,673910784,-379064320,-40501248,46448640]),(⟨0,0,4⟩,[0,-6144,83968,202752,-9025536,60942336,-183363584,257738752,-123840512,-27897856]),(⟨0,0,5⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨0,0,6⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨0,1,0⟩,[0,-6144,231424,-3696640,33245184,-187451392,693909504,-1700513792,2675857408,-2444886016,898719744,238587904,-162054144]),(⟨0,1,1⟩,[2048,-55296,712704,-6266880,41152512,-194945024,631898112,-1331728384,1666091008,-943540224,-124870656,288813056]),(⟨0,1,2⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨0,1,3⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨0,1,4⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨0,1,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,1,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,2,0⟩,[0,12288,-342016,3852288,-22405120,68583424,-81055744,-127062016,549396480,-636284928,166250496,97929216]),(⟨0,2,1⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨0,2,2⟩,[0,-16384,438272,-4435968,21016576,-45920256,31821824,35549184,-76869632,55193600]),(⟨0,2,3⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨0,2,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,3,0⟩,[0,12288,-454656,6533120,-48345088,203624448,-499912704,673910784,-379064320,-40501248,46448640]),(⟨0,3,1⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨0,3,2⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨0,3,3⟩,[4096,-94208,839680,-4108288,13709312,-29839360,29224960,-1347584]),(⟨0,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,4,0⟩,[0,-6144,83968,202752,-9025536,60942336,-183363584,257738752,-123840512,-27897856]),(⟨0,4,1⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨0,4,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,4,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,5,0⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨0,5,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,6,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨0,6,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[0,-6144,231424,-3696640,33245184,-187451392,693909504,-1700513792,2675857408,-2444886016,898719744,238587904,-162054144]),(⟨1,0,1⟩,[2048,-55296,712704,-6266880,41152512,-194945024,631898112,-1331728384,1666091008,-943540224,-124870656,288813056]),(⟨1,0,2⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨1,0,3⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨1,0,4⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨1,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[2048,-55296,712704,-6266880,41152512,-194945024,631898112,-1331728384,1666091008,-943540224,-124870656,288813056]),(⟨1,1,1⟩,[0,-49152,1204224,-12611584,75567104,-282243072,649072640,-797790208,171192320,751644672,-669233152]),(⟨1,1,2⟩,[-2048,30720,57344,-3383296,24219648,-82702336,156917760,-134422528,-58509312,152320000]),(⟨1,1,3⟩,[0,53248,-1093632,8687616,-34271232,65761280,-31789056,-82104320,99921920]),(⟨1,1,4⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨1,2,0⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨1,2,1⟩,[-2048,30720,57344,-3383296,24219648,-82702336,156917760,-134422528,-58509312,152320000]),(⟨1,2,2⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨1,2,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,2,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,3,0⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨1,3,1⟩,[0,53248,-1093632,8687616,-34271232,65761280,-31789056,-82104320,99921920]),(⟨1,3,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,4,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨1,4,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨1,4,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[0,12288,-342016,3852288,-22405120,68583424,-81055744,-127062016,549396480,-636284928,166250496,97929216]),(⟨2,0,1⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨2,0,2⟩,[0,-16384,438272,-4435968,21016576,-45920256,31821824,35549184,-76869632,55193600]),(⟨2,0,3⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨2,0,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[0,-6144,55296,448512,-7243776,34195456,-75479040,87738368,-98949120,194686976,-194166784]),(⟨2,1,1⟩,[-2048,30720,57344,-3383296,24219648,-82702336,156917760,-134422528,-58509312,152320000]),(⟨2,1,2⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,1,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[0,-16384,438272,-4435968,21016576,-45920256,31821824,35549184,-76869632,55193600]),(⟨2,2,1⟩,[4096,-98304,892928,-3915776,8749056,-6291456,-22159360,68239360,-58003456]),(⟨2,3,0⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨2,3,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,4,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[0,12288,-454656,6533120,-48345088,203624448,-499912704,673910784,-379064320,-40501248,46448640]),(⟨3,0,1⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨3,0,2⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨3,0,3⟩,[4096,-94208,839680,-4108288,13709312,-29839360,29224960,-1347584]),(⟨3,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[-4096,102400,-1087488,7018496,-32356352,103905280,-201721856,194185216,-49256448,-29173760]),(⟨3,1,1⟩,[0,53248,-1093632,8687616,-34271232,65761280,-31789056,-82104320,99921920]),(⟨3,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,1,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,2,0⟩,[0,6144,-14336,-1124352,10274816,-33060864,43882496,-28211200,20830208]),(⟨3,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,3,0⟩,[4096,-94208,839680,-4108288,13709312,-29839360,29224960,-1347584]),(⟨3,3,1⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[0,-6144,83968,202752,-9025536,60942336,-183363584,257738752,-123840512,-27897856]),(⟨4,0,1⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[0,28672,-528384,3698688,-13373440,26333184,-14790656,-46051328,67751936]),(⟨4,1,1⟩,[0,20480,-516096,4796416,-19939328,34582528,-11395072,-18034688]),(⟨4,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[0,-6144,223232,-2799616,15452160,-37668864,31438848,6264832,-4515840]),(⟨5,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,0,0⟩,[0,0,49152,-999424,6914048,-19431424,18726912,1032192]),(⟨6,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


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
    (Poly.add (Poly.scale (K.ofRat r400) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 4 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r398*r399 : ℚ)=r400 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 4 10 r398 r399 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 4=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 4 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C101

#print axioms Coulomb8.Columns.C101.sound
