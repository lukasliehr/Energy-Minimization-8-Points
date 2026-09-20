import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C070

def r0 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 4992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -58368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 401088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -1762176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 5010048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -8689536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 6914304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 3811008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -13549056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 9826176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -163776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -2020992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 276480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -164096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 853504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -3014400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 7137792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -10570368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 1030592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 4420352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 11138432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -2441344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -105600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -1664, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 144960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -613120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1974144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -241408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 4375680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -25088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -667968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 4417408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -1384640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -66176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 413568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -1613440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 3923712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -5389696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 2205696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 4790656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1091840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 3479040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 123008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -32448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 231040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -927616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 2236672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -3047936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 1408896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 2167168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -221888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 271168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 62464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -291712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 747648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -905344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -77312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1478016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1261504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 90624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 37376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -203264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 562432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -106752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 19456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 115712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -723712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 55808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -56704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 18304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 47616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -24320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 82176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 17152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -146176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 727680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -2319104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 284160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -6255616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 3748608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 2299520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -1007360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 928000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -353920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -16064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 85632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -259072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 412032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -20224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -674304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1230400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -718272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -25536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 41600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -32320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 228352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -907008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 2162816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -172672, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 1413120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 1978112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -3626048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 268608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -73856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 221824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -325760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 82560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 53120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -50560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -5888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 147712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -225024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -8448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 54016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -41728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 37888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -166144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 375168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -325888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -289280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 850176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -541760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 49408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -258816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 681216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -843008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 107264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 125184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -739584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 74496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -152832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -60672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 645888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -713472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 36096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -25600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -138496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 352256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -57088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 49920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -96000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 326656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -76800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 26880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -15360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -415488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 1056768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -171264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 2496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 200544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -881088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 2505024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -4344768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 3457152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 1905504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -6774528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 4913088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -81888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -1010496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 138240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -82048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 426752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1507200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 3568896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -5285184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 515296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 2210176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 5569216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1220672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -52800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 1952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -832, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 72480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -306560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 987072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -120704, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 2187840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -12544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -333984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 2208704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -692320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -33088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 206784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -806720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 1961856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -2694848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 1102848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 2395328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -545920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 1739520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 61504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -16224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 115520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -463808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 1118336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -1523968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 704448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 1083584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -110944, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 135584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -145856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 373824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -452672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -38656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 739008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -630752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 45312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 18688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -101632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 281216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -53376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 9728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 57856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -361856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -9024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 27904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 9152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 23808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -12160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 41088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 8576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -73088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 363840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -1159552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 142080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -3127808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 1874304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 1149760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -503680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 464000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -176960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -8032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 42816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -129536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 206016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -10112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -337152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 615200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -359136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -12768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 20800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -16160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 114176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -453504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 1081408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -86336, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 706560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 989056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -1813024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 134304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -36928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 110912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -162880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 41280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 26560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -25280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -2944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 73856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -112512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -4224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 27008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -20864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -83072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 187584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -162944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -144640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 425088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -270880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 24704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -129408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 340608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -421504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 62592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -369792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 37248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -76416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -30336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 322944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -356736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -69248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 176128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -28544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -38400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 13440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -207744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 528384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -85632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,-117248,r24,r25,r26],[0,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38],[r27,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49],[0,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59],[r60,r61,r62,r63,r64,r65,r66,r67,r68,r69],[0,r70,r71,r72,r73,r74,r75,r76,r77],[r78,r79,r80,r81,r82,-512,r83,r84],[0,r85,r86,r87,-512,r88,r89],[],[],[],[],[0,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101],[r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113],[0,r50,r114,r115,r116,r117,r118,r119,r120,r121,r122],[],[0,r90,r123,r124,r125,r126,r127,r128,r129],[],[],[],[],[],[],[0,0,r27,r130,r131,r132,r133,r134,r135,r136,r137],[r138,r139,r140,r141,r142,r143,r144,r145,r146,r147],[],[r78,r79,r80,r81,r82,-512,r83,r84],[],[],[],[],[],[0,r148,r149,r150,r151,r152,r153,r154,r155],[],[0,r85,r86,r87,-512,r88,r89],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r156,r86,r157,r158,r159,r160,r161,r162,1536],[r27,r163,r164,r165,r166,r167,r168,r169,1792],[0,0,r170,r171,r172,r173,r174,-512],[r156,r175,r176,r177,r178,r179,-2304],[],[r170,r39,r180,r181,512],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r182,r183,r184,r185,r186,r187,r188,r189,5376],[0,0,r170,r171,r172,r173,r174,-512],[r156,r175,r176,r177,r178,r179,-2304],[],[r170,r39,r180,r181,512],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203]),(⟨0,0,1⟩,[r204,r205,r206,r207,r208,r209,r210,r211,r212,r213,-58624,r214,r215,r216]),(⟨0,0,2⟩,[0,r78,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227]),(⟨0,0,3⟩,[r78,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238]),(⟨0,0,4⟩,[0,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,0,5⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨0,0,6⟩,[0,r259,r260,r261,r262,r263,r264,r265,r266]),(⟨0,0,7⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨0,0,8⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨0,1,0⟩,[r204,r205,r206,r207,r208,r209,r210,r211,r212,r213,-58624,r214,r215,r216]),(⟨0,1,1⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288]),(⟨0,1,2⟩,[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,1,3⟩,[0,r239,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨0,1,5⟩,[0,r277,r310,r311,r312,r313,r314,r315,r316]),(⟨0,2,0⟩,[0,r78,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227]),(⟨0,2,1⟩,[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,2,2⟩,[0,0,r78,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨0,2,3⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r182]),(⟨0,2,5⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨0,3,0⟩,[r78,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238]),(⟨0,3,1⟩,[0,r239,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨0,3,2⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r182]),(⟨0,3,3⟩,[0,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,3,5⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨0,4,0⟩,[0,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,5,0⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨0,5,1⟩,[0,r277,r310,r311,r312,r313,r314,r315,r316]),(⟨0,5,2⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨0,5,3⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨0,6,0⟩,[0,r259,r260,r261,r262,r263,r264,r265,r266]),(⟨0,7,0⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨0,8,0⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨1,0,0⟩,[r204,r205,r206,r207,r208,r209,r210,r211,r212,r213,-58624,r214,r215,r216]),(⟨1,0,1⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288]),(⟨1,0,2⟩,[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨1,0,3⟩,[0,r239,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨1,0,5⟩,[0,r277,r310,r311,r312,r313,r314,r315,r316]),(⟨1,1,0⟩,[0,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288]),(⟨1,2,0⟩,[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨1,2,2⟩,[0,r342,r273,r343,r344,r345,r346,r347,r348,768]),(⟨1,2,3⟩,[r78,r349,r350,r351,r84,r352,r353,r354,896]),(⟨1,2,4⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨1,2,5⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨1,2,7⟩,[r27,r228,r363,r364,256]),(⟨1,3,0⟩,[0,r239,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨1,3,2⟩,[r78,r349,r350,r351,r84,r352,r353,r354,896]),(⟨1,4,2⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨1,5,0⟩,[0,r277,r310,r311,r312,r313,r314,r315,r316]),(⟨1,5,2⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨1,7,2⟩,[r27,r228,r363,r364,256]),(⟨2,0,0⟩,[0,r78,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227]),(⟨2,0,1⟩,[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨2,0,2⟩,[0,0,r78,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨2,0,3⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r182]),(⟨2,0,5⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨2,1,0⟩,[r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨2,1,2⟩,[0,r342,r273,r343,r344,r345,r346,r347,r348,768]),(⟨2,1,3⟩,[r78,r349,r350,r351,r84,r352,r353,r354,896]),(⟨2,1,4⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨2,1,5⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨2,1,7⟩,[r27,r228,r363,r364,256]),(⟨2,2,0⟩,[0,0,r78,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨2,2,1⟩,[0,r342,r273,r343,r344,r345,r346,r347,r348,768]),(⟨2,2,2⟩,[r365,r366,r367,r368,r369,r370,r371,r372,2688]),(⟨2,2,3⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨2,2,4⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨2,2,6⟩,[r27,r228,r363,r364,256]),(⟨2,3,0⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r182]),(⟨2,3,1⟩,[r78,r349,r350,r351,r84,r352,r353,r354,896]),(⟨2,3,2⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨2,4,1⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨2,4,2⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨2,5,0⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨2,5,1⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨2,6,2⟩,[r27,r228,r363,r364,256]),(⟨2,7,1⟩,[r27,r228,r363,r364,256]),(⟨3,0,0⟩,[r78,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238]),(⟨3,0,1⟩,[0,r239,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨3,0,2⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r182]),(⟨3,0,3⟩,[0,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨3,0,5⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨3,1,0⟩,[0,r239,r301,r302,r303,r304,r305,r306,r307,r308,r309]),(⟨3,1,2⟩,[r78,r349,r350,r351,r84,r352,r353,r354,896]),(⟨3,2,0⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r182]),(⟨3,2,1⟩,[r78,r349,r350,r351,r84,r352,r353,r354,896]),(⟨3,2,2⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨3,3,0⟩,[0,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨3,5,0⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨4,0,0⟩,[0,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨4,1,2⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨4,2,1⟩,[0,0,r27,r355,r356,r147,r357,-256]),(⟨4,2,2⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨5,0,0⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨5,0,1⟩,[0,r277,r310,r311,r312,r313,r314,r315,r316]),(⟨5,0,2⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨5,0,3⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨5,1,0⟩,[0,r277,r310,r311,r312,r313,r314,r315,r316]),(⟨5,1,2⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨5,2,0⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨5,2,1⟩,[r342,r358,r359,r360,r361,r362,-1152]),(⟨5,3,0⟩,[0,r272,r273,r274,-256,r275,r276]),(⟨6,0,0⟩,[0,r259,r260,r261,r262,r263,r264,r265,r266]),(⟨6,2,2⟩,[r27,r228,r363,r364,256]),(⟨7,0,0⟩,[r102,r85,r267,r268,r269,-256,r270,r271]),(⟨7,1,2⟩,[r27,r228,r363,r364,256]),(⟨7,2,1⟩,[r27,r228,r363,r364,256]),(⟨8,0,0⟩,[0,r272,r273,r274,-256,r275,r276])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r373) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r374) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[256,-5376,49152,-251136,744960,-1158912,423936,1255680,-1439488,184320]),(⟨5,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨6,0,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[256,-5376,49152,-251136,744960,-1158912,423936,1255680,-1439488,184320]),(⟨0,5,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,5,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,5,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,6,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,7,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,8,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨1,0,0⟩,[128,-3328,39296,-276736,1276544,-3986688,8387328,-11202816,7242112,3581440,-13080704,13233664,-6051968,645120]),(⟨1,0,1⟩,[0,-896,17152,-146176,727680,-2319104,4830720,-6255616,3748608,2299520,-7051520,6496000,-2477440]),(⟨1,0,2⟩,[-128,3200,-32128,173056,-545280,997120,-874496,-253440,1644160,-2015104,1094016,-125440]),(⟨1,0,3⟩,[0,1280,-19456,125696,-443648,909056,-1020672,349440,662784,-1074176,575232]),(⟨1,1,0⟩,[0,-896,17152,-146176,727680,-2319104,4830720,-6255616,3748608,2299520,-7051520,6496000,-2477440]),(⟨1,2,0⟩,[-128,3200,-32128,173056,-545280,997120,-874496,-253440,1644160,-2015104,1094016,-125440]),(⟨1,3,0⟩,[0,1280,-19456,125696,-443648,909056,-1020672,349440,662784,-1074176,575232]),(⟨1,5,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,7,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[0,-896,17408,-151808,782208,-2619392,5826816,-8159488,5331456,3131264,-9746688,8119808,-2661760]),(⟨2,0,1⟩,[0,0,0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨2,0,2⟩,[0,0,-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨2,0,3⟩,[0,0,0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨2,1,0⟩,[0,0,0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨2,2,0⟩,[0,0,-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨2,2,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,3,0⟩,[0,0,0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨2,5,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,7,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[-512,12288,-128512,768768,-2861312,6672384,-8907008,3678720,7735040,-13121536,6857472,-247040]),(⟨3,0,1⟩,[0,2688,-45184,331008,-1370368,3416576,-4850176,2476800,3293440,-6177920,3185280]),(⟨3,0,2⟩,[384,-8704,75776,-334848,779008,-773120,-361472,1627136,-1296512,161280]),(⟨3,0,3⟩,[0,-3840,49408,-258816,681216,-843008,107264,876288,-739584]),(⟨3,1,0⟩,[0,2688,-45184,331008,-1370368,3416576,-4850176,2476800,3293440,-6177920,3185280]),(⟨3,1,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨3,2,0⟩,[384,-8704,75776,-334848,779008,-773120,-361472,1627136,-1296512,161280]),(⟨3,2,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨3,2,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨3,3,0⟩,[0,-3840,49408,-258816,681216,-843008,107264,876288,-739584]),(⟨3,5,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,0,0⟩,[0,3968,-64896,462080,-1855232,4473344,-6095872,2817792,4334336,-7544192,3796352]),(⟨4,1,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,1⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,0,0⟩,[640,-14080,124928,-583424,1495296,-1810688,-154624,2956032,-2523008,181248]),(⟨5,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,1,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,2,1⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨6,0,0⟩,[0,-5632,74752,-406528,1124864,-1494528,272384,1619968,-1447424]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[256,-5376,49152,-251136,744960,-1158912,423936,1255680,-1439488,184320]),(⟨0,0,6⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,0,7⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,0,8⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,1,0⟩,[128,-3328,39296,-276736,1276544,-3986688,8387328,-11202816,7242112,3581440,-13080704,13233664,-6051968,645120]),(⟨0,1,1⟩,[0,-896,17152,-146176,727680,-2319104,4830720,-6255616,3748608,2299520,-7051520,6496000,-2477440]),(⟨0,1,2⟩,[-128,3200,-32128,173056,-545280,997120,-874496,-253440,1644160,-2015104,1094016,-125440]),(⟨0,1,3⟩,[0,1280,-19456,125696,-443648,909056,-1020672,349440,662784,-1074176,575232]),(⟨0,1,5⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,2,0⟩,[0,-896,17408,-151808,782208,-2619392,5826816,-8159488,5331456,3131264,-9746688,8119808,-2661760]),(⟨0,2,1⟩,[0,0,0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨0,2,2⟩,[0,0,-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨0,2,3⟩,[0,0,0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨0,2,5⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,3,0⟩,[-512,12288,-128512,768768,-2861312,6672384,-8907008,3678720,7735040,-13121536,6857472,-247040]),(⟨0,3,1⟩,[0,2688,-45184,331008,-1370368,3416576,-4850176,2476800,3293440,-6177920,3185280]),(⟨0,3,2⟩,[384,-8704,75776,-334848,779008,-773120,-361472,1627136,-1296512,161280]),(⟨0,3,3⟩,[0,-3840,49408,-258816,681216,-843008,107264,876288,-739584]),(⟨0,3,5⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,4,0⟩,[0,3968,-64896,462080,-1855232,4473344,-6095872,2817792,4334336,-7544192,3796352]),(⟨0,5,0⟩,[640,-14080,124928,-583424,1495296,-1810688,-154624,2956032,-2523008,181248]),(⟨0,5,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,5,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,5,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,6,0⟩,[0,-5632,74752,-406528,1124864,-1494528,272384,1619968,-1447424]),(⟨0,7,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,8,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨1,0,0⟩,[128,-3328,39296,-276736,1276544,-3986688,8387328,-11202816,7242112,3581440,-13080704,13233664,-6051968,645120]),(⟨1,0,1⟩,[0,-896,17152,-146176,727680,-2319104,4830720,-6255616,3748608,2299520,-7051520,6496000,-2477440]),(⟨1,0,2⟩,[-128,3200,-32128,173056,-545280,997120,-874496,-253440,1644160,-2015104,1094016,-125440]),(⟨1,0,3⟩,[0,1280,-19456,125696,-443648,909056,-1020672,349440,662784,-1074176,575232]),(⟨1,0,5⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,1,0⟩,[0,-1792,34304,-292352,1455360,-4638208,9661440,-12511232,7497216,4599040,-14103040,12992000,-4954880]),(⟨1,2,0⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨1,2,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,3,0⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨1,3,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨1,4,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨1,5,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,5,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨1,7,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[0,-896,17408,-151808,782208,-2619392,5826816,-8159488,5331456,3131264,-9746688,8119808,-2661760]),(⟨2,0,1⟩,[0,0,0,-1792,27136,-173056,591360,-1095168,816640,578560,-1451520,707840]),(⟨2,0,2⟩,[0,0,-256,5376,-41216,147712,-225024,-8448,378112,-292096,35840]),(⟨2,0,3⟩,[0,0,0,2560,-28672,121344,-217088,73216,212992,-164352]),(⟨2,0,5⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,1,0⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨2,1,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,2,0⟩,[0,0,-512,10752,-82432,295424,-450048,-16896,756224,-584192,71680]),(⟨2,2,2⟩,[-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨2,2,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,3,0⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨2,3,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,3,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,4,1⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,4,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨2,5,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,5,1⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨2,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,7,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[-512,12288,-128512,768768,-2861312,6672384,-8907008,3678720,7735040,-13121536,6857472,-247040]),(⟨3,0,1⟩,[0,2688,-45184,331008,-1370368,3416576,-4850176,2476800,3293440,-6177920,3185280]),(⟨3,0,2⟩,[384,-8704,75776,-334848,779008,-773120,-361472,1627136,-1296512,161280]),(⟨3,0,3⟩,[0,-3840,49408,-258816,681216,-843008,107264,876288,-739584]),(⟨3,0,5⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨3,1,0⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨3,1,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨3,2,0⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨3,2,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨3,2,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨3,3,0⟩,[0,-7680,98816,-517632,1362432,-1686016,214528,1752576,-1479168]),(⟨3,5,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,0,0⟩,[0,3968,-64896,462080,-1855232,4473344,-6095872,2817792,4334336,-7544192,3796352]),(⟨4,1,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,1⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,0,0⟩,[640,-14080,124928,-583424,1495296,-1810688,-154624,2956032,-2523008,181248]),(⟨5,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,1,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,2,1⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨6,0,0⟩,[0,-5632,74752,-406528,1124864,-1494528,272384,1619968,-1447424]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-384,9984,-116736,802176,-3524352,10020096,-17379072,13828608,7622016,-27098112,19652352,-327552,-4041984,552960]),(⟨0,0,1⟩,[128,-3328,41984,-328192,1707008,-6028800,14275584,-21140736,14428288,8840704,-27905024,22276864,-4882688,-1478400]),(⟨0,0,2⟩,[0,-512,7808,-56576,289920,-1226240,3948288,-8207872,8751360,-351232,-9351552,8834816,-2769280]),(⟨0,0,3⟩,[-512,12288,-132352,827136,-3226880,7847424,-10779392,4411392,9581312,-15285760,6958080,246016]),(⟨0,0,4⟩,[0,3968,-64896,462080,-1855232,4473344,-6095872,2817792,4334336,-7544192,3796352]),(⟨0,0,5⟩,[640,-14080,124928,-583424,1495296,-1810688,-154624,2956032,-2523008,181248]),(⟨0,0,6⟩,[0,-5632,74752,-406528,1124864,-1494528,272384,1619968,-1447424]),(⟨0,0,7⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,0,8⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,1,0⟩,[128,-3328,41984,-328192,1707008,-6028800,14275584,-21140736,14428288,8840704,-27905024,22276864,-4882688,-1478400]),(⟨0,1,1⟩,[0,-1792,34304,-292352,1455360,-4638208,9661440,-12511232,7497216,4599040,-14103040,12992000,-4954880]),(⟨0,1,2⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨0,1,3⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨0,1,5⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,2,0⟩,[0,-512,7808,-56576,289920,-1226240,3948288,-8207872,8751360,-351232,-9351552,8834816,-2769280]),(⟨0,2,1⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨0,2,2⟩,[0,0,-512,10752,-82432,295424,-450048,-16896,756224,-584192,71680]),(⟨0,2,3⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨0,2,5⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,3,0⟩,[-512,12288,-132352,827136,-3226880,7847424,-10779392,4411392,9581312,-15285760,6958080,246016]),(⟨0,3,1⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨0,3,2⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨0,3,3⟩,[0,-7680,98816,-517632,1362432,-1686016,214528,1752576,-1479168]),(⟨0,3,5⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,4,0⟩,[0,3968,-64896,462080,-1855232,4473344,-6095872,2817792,4334336,-7544192,3796352]),(⟨0,5,0⟩,[640,-14080,124928,-583424,1495296,-1810688,-154624,2956032,-2523008,181248]),(⟨0,5,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨0,5,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,5,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨0,6,0⟩,[0,-5632,74752,-406528,1124864,-1494528,272384,1619968,-1447424]),(⟨0,7,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨0,8,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨1,0,0⟩,[128,-3328,41984,-328192,1707008,-6028800,14275584,-21140736,14428288,8840704,-27905024,22276864,-4882688,-1478400]),(⟨1,0,1⟩,[0,-1792,34304,-292352,1455360,-4638208,9661440,-12511232,7497216,4599040,-14103040,12992000,-4954880]),(⟨1,0,2⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨1,0,3⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨1,0,5⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,1,0⟩,[0,-1792,34304,-292352,1455360,-4638208,9661440,-12511232,7497216,4599040,-14103040,12992000,-4954880]),(⟨1,2,0⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨1,2,2⟩,[0,1536,-26112,148992,-305664,-121344,1291776,-1426944,72192,365568]),(⟨1,2,3⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨1,2,4⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨1,2,5⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨1,2,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨1,3,0⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨1,3,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨1,4,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨1,5,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨1,5,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨1,7,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,0,0⟩,[0,-512,7808,-56576,289920,-1226240,3948288,-8207872,8751360,-351232,-9351552,8834816,-2769280]),(⟨2,0,1⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨2,0,2⟩,[0,0,-512,10752,-82432,295424,-450048,-16896,756224,-584192,71680]),(⟨2,0,3⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨2,0,5⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,1,0⟩,[-128,3200,-32128,171264,-518144,824064,-283136,-1348608,2460800,-1436544,-357504,582400]),(⟨2,1,2⟩,[0,1536,-26112,148992,-305664,-121344,1291776,-1426944,72192,365568]),(⟨2,1,3⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,1,4⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,1,5⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨2,1,7⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,2,0⟩,[0,0,-512,10752,-82432,295424,-450048,-16896,756224,-584192,71680]),(⟨2,2,1⟩,[0,1536,-26112,148992,-305664,-121344,1291776,-1426944,72192,365568]),(⟨2,2,2⟩,[-1536,26112,-153600,376320,-215040,-830976,2113536,-2397696,1279488]),(⟨2,2,3⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,2,4⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨2,2,6⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,3,0⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨2,3,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨2,3,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,4,1⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,4,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨2,5,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨2,5,1⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨2,6,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,7,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[-512,12288,-132352,827136,-3226880,7847424,-10779392,4411392,9581312,-15285760,6958080,246016]),(⟨3,0,1⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨3,0,2⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨3,0,3⟩,[0,-7680,98816,-517632,1362432,-1686016,214528,1752576,-1479168]),(⟨3,0,5⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨3,1,0⟩,[0,3968,-64640,456704,-1814016,4325632,-5870848,2826240,3956224,-7252096,3760512]),(⟨3,1,2⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨3,2,0⟩,[384,-8704,75776,-332288,750336,-651776,-578560,1700352,-1083520,-3072]),(⟨3,2,1⟩,[-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨3,2,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨3,3,0⟩,[0,-7680,98816,-517632,1362432,-1686016,214528,1752576,-1479168]),(⟨3,5,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨4,0,0⟩,[0,3968,-64896,462080,-1855232,4473344,-6095872,2817792,4334336,-7544192,3796352]),(⟨4,1,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,1⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨4,2,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,0,0⟩,[640,-14080,124928,-583424,1495296,-1810688,-154624,2956032,-2523008,181248]),(⟨5,0,1⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,0,2⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,0,3⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨5,1,0⟩,[0,-1792,25344,-147712,443648,-651520,165120,743680,-707840]),(⟨5,1,2⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,2,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨5,2,1⟩,[1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨5,3,0⟩,[0,2560,-26112,95232,-121856,-48640,164352]),(⟨6,0,0⟩,[0,-5632,74752,-406528,1124864,-1494528,272384,1619968,-1447424]),(⟨6,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,0,0⟩,[-256,5120,-36096,111616,-113408,-121856,256256,-35840]),(⟨7,1,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨7,2,1⟩,[-1024,12288,-30720,-36864,121856]),(⟨8,0,0⟩,[0,2560,-26112,95232,-121856,-48640,164352])]


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
    (Poly.add (Poly.scale (K.ofRat r375) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r373*r374 : ℚ)=r375 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 12 r373 r374 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C070

#print axioms Coulomb8.Columns.C070.sound
