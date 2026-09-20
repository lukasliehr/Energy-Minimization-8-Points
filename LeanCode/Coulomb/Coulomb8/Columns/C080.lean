import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C080

def r0 : ℚ := { num := 36, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -708, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 5988, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -29148, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 89604, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -176796, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 214428, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -134916, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 9432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 32064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -6912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -12, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -2328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 14080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -56400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 151968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -273000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 312064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -197860, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 38128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 16192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -4, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -1336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 8280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -34672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 97496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -177400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 197272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 25144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 4096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -15792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 35160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -40656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 9600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 29200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -24124, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 4, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -324, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 3228, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -14412, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 35692, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -51180, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 40244, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -12484, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -24, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 3032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 5320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 1600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -1760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -2136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 14400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -57096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 144256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -236616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 244384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -142296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 33424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 12, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -12872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 42952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -74960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 70392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -28420, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 2384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -10280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 24224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -33176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 25040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -7192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -48, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -2880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 6208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -6928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 8, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -5720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -12600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 3528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 2744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 4224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -2424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 15072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -48696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 91728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -102120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 60480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -2776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 10352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -24648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 37664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -33544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -8, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 2400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -5496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 6512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 48, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 2880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -6208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 6928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 18, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -354, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 2994, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -14574, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 44802, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -88398, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 107214, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -67458, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 4716, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 16032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -6, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -1164, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 7040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -28200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 75984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -136500, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 156032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -98930, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 19064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 8096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -2, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -668, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 4140, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -17336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 48748, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -88700, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 98636, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 12572, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -7896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 17580, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -20328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 4800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 14600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -12062, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 2, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -162, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 1614, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -7206, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 17846, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -25590, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 20122, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -6242, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -580, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 1516, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 2660, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 88, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -56, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 72, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -1068, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 7200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -28548, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 72128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -118308, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 122192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -71148, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 16712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 6, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -84, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 468, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -6436, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 21476, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -37480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 35196, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -14210, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -116, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 1192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -5140, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 12112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -16588, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 12520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -3596, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -1440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 3104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -3464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 684, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -2860, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -6300, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 1764, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 1372, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 2112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -1212, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 7536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -24348, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 45864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -51060, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 30240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -1388, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 5176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -12324, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 18832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -16772, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 56, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -308, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 1200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -2748, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 3256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 24, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 1440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -3104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 3464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 1, den := 136, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10],[r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21],[r22,r23,r24,r25,r26,r27,r28,r29,-6940,r30],[r0,r31,r32,r33,r34,r35,r36,r37,r38],[r39,r40,r41,r42,r43,r44,r45,r46],[r47,r48,r49,r50,r51,r52,r53],[r54,r55,-16,r56,r57,r58],[0,r59,r60,r61,r62],[r55,r63,r64,r65],[0,r23,r66],[],[],[],[0,r67,r68,r69,r70,r71,r72,r73,r74,r75],[r76,r77,r78,r79,r80,r81,r82,r83,r84],[0,r85,r86,r87,r88,r89,r90,r91],[0,r92,r93,r94,r95,r96,176],[],[0,r59,r60,r61,r62],[0,r97,r48,-32],[],[],[],[],[r98,r77,r99,r100,728,r101,r102,r103],[r47,r48,r49,r50,r51,r52,r53],[],[],[r55,r63,r64,r65],[],[],[],[],[0,r104,r105,r106,-512,r107],[],[],[0,r23,r66],[],[],[],[],[],[],[],[],[],[],[],[],[0,r67,r108,r109,r110,r111,r112,r113,-744],[r47,r114,r115,r116,r117,r118,r119,784],[r120,r121,r122,r123,r124,r125,-216],[r126,r127,r128,r129,r130,-176],[],[0,r97,r48,-32],[r131,r132,32],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143]),(⟨0,0,1⟩,[r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154]),(⟨0,0,2⟩,[r155,r156,r157,r158,r159,r160,r161,r162,-3470,r163]),(⟨0,0,3⟩,[r133,r164,r165,r166,r167,r168,r169,r170,r171]),(⟨0,0,4⟩,[r172,r173,r174,r175,r176,r177,r178,r179]),(⟨0,0,5⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨0,0,6⟩,[r98,r120,-8,r186,r187,r188]),(⟨0,0,7⟩,[0,r92,r189,r190,r191]),(⟨0,0,8⟩,[r120,r192,r193,r194]),(⟨0,0,9⟩,[0,r156,r195]),(⟨0,1,0⟩,[r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154]),(⟨0,1,1⟩,[0,r196,r197,r198,r199,r200,r201,r202,r203,r204]),(⟨0,1,2⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨0,1,3⟩,[0,r214,r215,r216,r217,r218,r219,r220]),(⟨0,1,4⟩,[0,r47,r221,r222,r223,r224,88]),(⟨0,1,6⟩,[0,r92,r189,r190,r191]),(⟨0,1,7⟩,[0,r55,r180,-16]),(⟨0,2,0⟩,[r155,r156,r157,r158,r159,r160,r161,r162,-3470,r163]),(⟨0,2,1⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨0,2,2⟩,[r39,r206,r225,r226,364,r227,r228,r229]),(⟨0,2,3⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨0,2,6⟩,[r120,r192,r193,r194]),(⟨0,3,0⟩,[r133,r164,r165,r166,r167,r168,r169,r170,r171]),(⟨0,3,1⟩,[0,r214,r215,r216,r217,r218,r219,r220]),(⟨0,3,2⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨0,3,3⟩,[0,r230,r231,r232,-256,r233]),(⟨0,3,6⟩,[0,r156,r195]),(⟨0,4,0⟩,[r172,r173,r174,r175,r176,r177,r178,r179]),(⟨0,4,1⟩,[0,r47,r221,r222,r223,r224,88]),(⟨0,5,0⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨0,6,0⟩,[r98,r120,-8,r186,r187,r188]),(⟨0,6,1⟩,[0,r92,r189,r190,r191]),(⟨0,6,2⟩,[r120,r192,r193,r194]),(⟨0,6,3⟩,[0,r156,r195]),(⟨0,7,0⟩,[0,r92,r189,r190,r191]),(⟨0,7,1⟩,[0,r55,r180,-16]),(⟨0,8,0⟩,[r120,r192,r193,r194]),(⟨0,9,0⟩,[0,r156,r195]),(⟨1,0,0⟩,[r144,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154]),(⟨1,0,1⟩,[0,r196,r197,r198,r199,r200,r201,r202,r203,r204]),(⟨1,0,2⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨1,0,3⟩,[0,r214,r215,r216,r217,r218,r219,r220]),(⟨1,0,4⟩,[0,r47,r221,r222,r223,r224,88]),(⟨1,0,6⟩,[0,r92,r189,r190,r191]),(⟨1,0,7⟩,[0,r55,r180,-16]),(⟨1,1,0⟩,[0,r196,r197,r198,r199,r200,r201,r202,r203,r204]),(⟨1,1,1⟩,[0,r196,r234,r235,r236,r237,r238,r239,-372]),(⟨1,1,2⟩,[r11,r240,r241,r242,r243,r244,r245,392]),(⟨1,1,3⟩,[r22,r246,r247,r248,r249,r250,-108]),(⟨1,1,4⟩,[r251,r252,r253,r254,r255,-88]),(⟨1,1,6⟩,[0,r55,r180,-16]),(⟨1,1,7⟩,[r54,r256,16]),(⟨1,2,0⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨1,2,1⟩,[r11,r240,r241,r242,r243,r244,r245,392]),(⟨1,3,0⟩,[0,r214,r215,r216,r217,r218,r219,r220]),(⟨1,3,1⟩,[r22,r246,r247,r248,r249,r250,-108]),(⟨1,4,0⟩,[0,r47,r221,r222,r223,r224,88]),(⟨1,4,1⟩,[r251,r252,r253,r254,r255,-88]),(⟨1,6,0⟩,[0,r92,r189,r190,r191]),(⟨1,6,1⟩,[0,r55,r180,-16]),(⟨1,7,0⟩,[0,r55,r180,-16]),(⟨1,7,1⟩,[r54,r256,16]),(⟨2,0,0⟩,[r155,r156,r157,r158,r159,r160,r161,r162,-3470,r163]),(⟨2,0,1⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨2,0,2⟩,[r39,r206,r225,r226,364,r227,r228,r229]),(⟨2,0,3⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨2,0,6⟩,[r120,r192,r193,r194]),(⟨2,1,0⟩,[r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨2,1,1⟩,[r11,r240,r241,r242,r243,r244,r245,392]),(⟨2,2,0⟩,[r39,r206,r225,r226,364,r227,r228,r229]),(⟨2,3,0⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨2,6,0⟩,[r120,r192,r193,r194]),(⟨3,0,0⟩,[r133,r164,r165,r166,r167,r168,r169,r170,r171]),(⟨3,0,1⟩,[0,r214,r215,r216,r217,r218,r219,r220]),(⟨3,0,2⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨3,0,3⟩,[0,r230,r231,r232,-256,r233]),(⟨3,0,6⟩,[0,r156,r195]),(⟨3,1,0⟩,[0,r214,r215,r216,r217,r218,r219,r220]),(⟨3,1,1⟩,[r22,r246,r247,r248,r249,r250,-108]),(⟨3,2,0⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨3,3,0⟩,[0,r230,r231,r232,-256,r233]),(⟨3,6,0⟩,[0,r156,r195]),(⟨4,0,0⟩,[r172,r173,r174,r175,r176,r177,r178,r179]),(⟨4,0,1⟩,[0,r47,r221,r222,r223,r224,88]),(⟨4,1,0⟩,[0,r47,r221,r222,r223,r224,88]),(⟨4,1,1⟩,[r251,r252,r253,r254,r255,-88]),(⟨5,0,0⟩,[r11,r180,r181,r182,r183,r184,r185]),(⟨6,0,0⟩,[r98,r120,-8,r186,r187,r188]),(⟨6,0,1⟩,[0,r92,r189,r190,r191]),(⟨6,0,2⟩,[r120,r192,r193,r194]),(⟨6,0,3⟩,[0,r156,r195]),(⟨6,1,0⟩,[0,r92,r189,r190,r191]),(⟨6,1,1⟩,[0,r55,r180,-16]),(⟨6,2,0⟩,[r120,r192,r193,r194]),(⟨6,3,0⟩,[0,r156,r195]),(⟨7,0,0⟩,[0,r92,r189,r190,r191]),(⟨7,0,1⟩,[0,r55,r180,-16]),(⟨7,1,0⟩,[0,r55,r180,-16]),(⟨7,1,1⟩,[r54,r256,16]),(⟨8,0,0⟩,[r120,r192,r193,r194]),(⟨9,0,0⟩,[0,r156,r195])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r257) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r258) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[64,-832,4032,-9920,10752,-2048]),(⟨6,0,1⟩,[0,-384,2816,-7040,6656]),(⟨6,0,2⟩,[-64,704,-1216,-448]),(⟨6,0,3⟩,[0,512,-1536]),(⟨6,1,0⟩,[0,-384,2816,-7040,6656]),(⟨6,1,1⟩,[0,-128,1280,-2176]),(⟨6,2,0⟩,[-64,704,-1216,-448]),(⟨6,3,0⟩,[0,512,-1536]),(⟨7,0,0⟩,[0,-384,2816,-7040,6656]),(⟨7,0,1⟩,[0,-128,1280,-2176]),(⟨7,1,0⟩,[0,-128,1280,-2176]),(⟨7,1,1⟩,[128,-1280,2176]),(⟨8,0,0⟩,[-64,704,-1216,-448]),(⟨9,0,0⟩,[0,512,-1536])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[64,-832,4032,-9920,10752,-2048]),(⟨0,6,1⟩,[0,-384,2816,-7040,6656]),(⟨0,6,2⟩,[-64,704,-1216,-448]),(⟨0,6,3⟩,[0,512,-1536]),(⟨0,7,0⟩,[0,-384,2816,-7040,6656]),(⟨0,7,1⟩,[0,-128,1280,-2176]),(⟨0,8,0⟩,[-64,704,-1216,-448]),(⟨0,9,0⟩,[0,512,-1536]),(⟨1,0,0⟩,[-48,960,-8448,44224,-153120,366144,-610944,695488,-501808,192640,-25088]),(⟨1,0,1⟩,[0,288,-4128,26400,-99744,245600,-405984,440288,-284256,81536]),(⟨1,0,2⟩,[48,-864,5664,-19552,40384,-50208,31584,-1568,-5488]),(⟨1,0,3⟩,[0,-384,3840,-16512,40448,-60544,51968,-18816]),(⟨1,1,0⟩,[0,288,-4128,26400,-99744,245600,-405984,440288,-284256,81536]),(⟨1,1,1⟩,[0,96,-1632,10464,-36320,77472,-103840,80416,-26656]),(⟨1,2,0⟩,[48,-864,5664,-19552,40384,-50208,31584,-1568,-5488]),(⟨1,3,0⟩,[0,-384,3840,-16512,40448,-60544,51968,-18816]),(⟨1,6,0⟩,[0,-384,2816,-7040,6656]),(⟨1,6,1⟩,[0,-128,1280,-2176]),(⟨1,7,0⟩,[0,-128,1280,-2176]),(⟨1,7,1⟩,[128,-1280,2176]),(⟨2,0,0⟩,[-16,656,-7888,48816,-184912,457904,-746992,771472,-451808,106624]),(⟨2,0,1⟩,[0,192,-3296,23296,-91872,222016,-331424,283136,-108192]),(⟨2,0,2⟩,[16,-336,2736,-11440,24752,-25200,7056,5488]),(⟨2,0,3⟩,[0,-128,1664,-9216,25088,-33152,18816]),(⟨2,1,0⟩,[0,192,-3296,23296,-91872,222016,-331424,283136,-108192]),(⟨2,1,1⟩,[-96,1664,-11104,41408,-98592,150656,-134176,53312]),(⟨2,2,0⟩,[16,-336,2736,-11440,24752,-25200,7056,5488]),(⟨2,3,0⟩,[0,-128,1664,-9216,25088,-33152,18816]),(⟨2,6,0⟩,[-64,704,-1216,-448]),(⟨3,0,0⟩,[144,-2368,15232,-52032,98400,-84288,-28032,122560,-75760]),(⟨3,0,1⟩,[0,-544,5696,-24608,56448,-72160,48192,-9952]),(⟨3,0,2⟩,[-96,1408,-6304,13056,-12960,2432,2464]),(⟨3,0,3⟩,[0,768,-5120,13312,-17408,8448]),(⟨3,1,0⟩,[0,-544,5696,-24608,56448,-72160,48192,-9952]),(⟨3,1,1⟩,[-32,448,-2464,9600,-21984,26048,-14688]),(⟨3,2,0⟩,[-96,1408,-6304,13056,-12960,2432,2464]),(⟨3,3,0⟩,[0,768,-5120,13312,-17408,8448]),(⟨3,6,0⟩,[0,512,-1536]),(⟨4,0,0⟩,[16,-1296,12912,-57648,142768,-204720,160976,-49936]),(⟨4,0,1⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨4,1,0⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨4,1,1⟩,[192,-2624,11520,-24832,27712,-11968]),(⟨5,0,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨6,0,0⟩,[64,-64,-1088,3392,-6656,6400]),(⟨6,0,1⟩,[0,-384,2816,-7040,6656]),(⟨6,0,2⟩,[-64,704,-1216,-448]),(⟨6,0,3⟩,[0,512,-1536]),(⟨6,1,0⟩,[0,-384,2816,-7040,6656]),(⟨6,1,1⟩,[0,-128,1280,-2176]),(⟨6,2,0⟩,[-64,704,-1216,-448]),(⟨6,3,0⟩,[0,512,-1536]),(⟨7,0,0⟩,[0,-384,2816,-7040,6656]),(⟨7,0,1⟩,[0,-128,1280,-2176]),(⟨7,1,0⟩,[0,-128,1280,-2176]),(⟨7,1,1⟩,[128,-1280,2176]),(⟨8,0,0⟩,[-64,704,-1216,-448]),(⟨9,0,0⟩,[0,512,-1536])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[64,-832,4032,-9920,10752,-2048]),(⟨0,0,7⟩,[0,-384,2816,-7040,6656]),(⟨0,0,8⟩,[-64,704,-1216,-448]),(⟨0,0,9⟩,[0,512,-1536]),(⟨0,1,0⟩,[-48,960,-8448,44224,-153120,366144,-610944,695488,-501808,192640,-25088]),(⟨0,1,1⟩,[0,288,-4128,26400,-99744,245600,-405984,440288,-284256,81536]),(⟨0,1,2⟩,[48,-864,5664,-19552,40384,-50208,31584,-1568,-5488]),(⟨0,1,3⟩,[0,-384,3840,-16512,40448,-60544,51968,-18816]),(⟨0,1,6⟩,[0,-384,2816,-7040,6656]),(⟨0,1,7⟩,[0,-128,1280,-2176]),(⟨0,2,0⟩,[-16,656,-7888,48816,-184912,457904,-746992,771472,-451808,106624]),(⟨0,2,1⟩,[0,192,-3296,23296,-91872,222016,-331424,283136,-108192]),(⟨0,2,2⟩,[16,-336,2736,-11440,24752,-25200,7056,5488]),(⟨0,2,3⟩,[0,-128,1664,-9216,25088,-33152,18816]),(⟨0,2,6⟩,[-64,704,-1216,-448]),(⟨0,3,0⟩,[144,-2368,15232,-52032,98400,-84288,-28032,122560,-75760]),(⟨0,3,1⟩,[0,-544,5696,-24608,56448,-72160,48192,-9952]),(⟨0,3,2⟩,[-96,1408,-6304,13056,-12960,2432,2464]),(⟨0,3,3⟩,[0,768,-5120,13312,-17408,8448]),(⟨0,3,6⟩,[0,512,-1536]),(⟨0,4,0⟩,[16,-1296,12912,-57648,142768,-204720,160976,-49936]),(⟨0,4,1⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨0,5,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨0,6,0⟩,[64,-64,-1088,3392,-6656,6400]),(⟨0,6,1⟩,[0,-384,2816,-7040,6656]),(⟨0,6,2⟩,[-64,704,-1216,-448]),(⟨0,6,3⟩,[0,512,-1536]),(⟨0,7,0⟩,[0,-384,2816,-7040,6656]),(⟨0,7,1⟩,[0,-128,1280,-2176]),(⟨0,8,0⟩,[-64,704,-1216,-448]),(⟨0,9,0⟩,[0,512,-1536]),(⟨1,0,0⟩,[-48,960,-8448,44224,-153120,366144,-610944,695488,-501808,192640,-25088]),(⟨1,0,1⟩,[0,288,-4128,26400,-99744,245600,-405984,440288,-284256,81536]),(⟨1,0,2⟩,[48,-864,5664,-19552,40384,-50208,31584,-1568,-5488]),(⟨1,0,3⟩,[0,-384,3840,-16512,40448,-60544,51968,-18816]),(⟨1,0,6⟩,[0,-384,2816,-7040,6656]),(⟨1,0,7⟩,[0,-128,1280,-2176]),(⟨1,1,0⟩,[0,576,-8256,52800,-199488,491200,-811968,880576,-568512,163072]),(⟨1,1,1⟩,[0,192,-3264,20928,-72640,154944,-207680,160832,-53312]),(⟨1,1,6⟩,[0,-128,1280,-2176]),(⟨1,1,7⟩,[128,-1280,2176]),(⟨1,2,0⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨1,2,1⟩,[-96,1664,-11104,41408,-98592,150656,-134176,53312]),(⟨1,3,0⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨1,3,1⟩,[-32,448,-2464,9600,-21984,26048,-14688]),(⟨1,4,0⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨1,4,1⟩,[192,-2624,11520,-24832,27712,-11968]),(⟨1,6,0⟩,[0,-384,2816,-7040,6656]),(⟨1,6,1⟩,[0,-128,1280,-2176]),(⟨1,7,0⟩,[0,-128,1280,-2176]),(⟨1,7,1⟩,[128,-1280,2176]),(⟨2,0,0⟩,[-16,656,-7888,48816,-184912,457904,-746992,771472,-451808,106624]),(⟨2,0,1⟩,[0,192,-3296,23296,-91872,222016,-331424,283136,-108192]),(⟨2,0,2⟩,[16,-336,2736,-11440,24752,-25200,7056,5488]),(⟨2,0,3⟩,[0,-128,1664,-9216,25088,-33152,18816]),(⟨2,0,6⟩,[-64,704,-1216,-448]),(⟨2,1,0⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨2,1,1⟩,[-96,1664,-11104,41408,-98592,150656,-134176,53312]),(⟨2,2,0⟩,[32,-672,5472,-22880,49504,-50400,14112,10976]),(⟨2,3,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨2,6,0⟩,[-64,704,-1216,-448]),(⟨3,0,0⟩,[144,-2368,15232,-52032,98400,-84288,-28032,122560,-75760]),(⟨3,0,1⟩,[0,-544,5696,-24608,56448,-72160,48192,-9952]),(⟨3,0,2⟩,[-96,1408,-6304,13056,-12960,2432,2464]),(⟨3,0,3⟩,[0,768,-5120,13312,-17408,8448]),(⟨3,0,6⟩,[0,512,-1536]),(⟨3,1,0⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨3,1,1⟩,[-32,448,-2464,9600,-21984,26048,-14688]),(⟨3,2,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨3,3,0⟩,[0,1536,-10240,26624,-34816,16896]),(⟨3,6,0⟩,[0,512,-1536]),(⟨4,0,0⟩,[16,-1296,12912,-57648,142768,-204720,160976,-49936]),(⟨4,0,1⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨4,1,0⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨4,1,1⟩,[192,-2624,11520,-24832,27712,-11968]),(⟨5,0,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨6,0,0⟩,[64,-64,-1088,3392,-6656,6400]),(⟨6,0,1⟩,[0,-384,2816,-7040,6656]),(⟨6,0,2⟩,[-64,704,-1216,-448]),(⟨6,0,3⟩,[0,512,-1536]),(⟨6,1,0⟩,[0,-384,2816,-7040,6656]),(⟨6,1,1⟩,[0,-128,1280,-2176]),(⟨6,2,0⟩,[-64,704,-1216,-448]),(⟨6,3,0⟩,[0,512,-1536]),(⟨7,0,0⟩,[0,-384,2816,-7040,6656]),(⟨7,0,1⟩,[0,-128,1280,-2176]),(⟨7,1,0⟩,[0,-128,1280,-2176]),(⟨7,1,1⟩,[128,-1280,2176]),(⟨8,0,0⟩,[-64,704,-1216,-448]),(⟨9,0,0⟩,[0,512,-1536])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,144,-2832,23952,-116592,358416,-707184,857712,-539664,37728,128256,-27648]),(⟨0,0,1⟩,[-48,960,-9312,56320,-225600,607872,-1092000,1248256,-791440,152512,64768]),(⟨0,0,2⟩,[-16,512,-5344,33120,-138688,389984,-709600,789088,-471920,100576]),(⟨0,0,3⟩,[144,-2368,16384,-63168,140640,-162624,38400,116800,-96496]),(⟨0,0,4⟩,[16,-1296,12912,-57648,142768,-204720,160976,-49936]),(⟨0,0,5⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨0,0,6⟩,[64,-64,-1088,3392,-6656,6400]),(⟨0,0,7⟩,[0,-384,2816,-7040,6656]),(⟨0,0,8⟩,[-64,704,-1216,-448]),(⟨0,0,9⟩,[0,512,-1536]),(⟨0,1,0⟩,[-48,960,-9312,56320,-225600,607872,-1092000,1248256,-791440,152512,64768]),(⟨0,1,1⟩,[0,576,-8544,57600,-228384,577024,-946464,977536,-569184,133696]),(⟨0,1,2⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨0,1,3⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨0,1,4⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨0,1,6⟩,[0,-384,2816,-7040,6656]),(⟨0,1,7⟩,[0,-128,1280,-2176]),(⟨0,2,0⟩,[-16,512,-5344,33120,-138688,389984,-709600,789088,-471920,100576]),(⟨0,2,1⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨0,2,2⟩,[32,-672,5472,-22880,49504,-50400,14112,10976]),(⟨0,2,3⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨0,2,6⟩,[-64,704,-1216,-448]),(⟨0,3,0⟩,[144,-2368,16384,-63168,140640,-162624,38400,116800,-96496]),(⟨0,3,1⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨0,3,2⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨0,3,3⟩,[0,1536,-10240,26624,-34816,16896]),(⟨0,3,6⟩,[0,512,-1536]),(⟨0,4,0⟩,[16,-1296,12912,-57648,142768,-204720,160976,-49936]),(⟨0,4,1⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨0,5,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨0,6,0⟩,[64,-64,-1088,3392,-6656,6400]),(⟨0,6,1⟩,[0,-384,2816,-7040,6656]),(⟨0,6,2⟩,[-64,704,-1216,-448]),(⟨0,6,3⟩,[0,512,-1536]),(⟨0,7,0⟩,[0,-384,2816,-7040,6656]),(⟨0,7,1⟩,[0,-128,1280,-2176]),(⟨0,8,0⟩,[-64,704,-1216,-448]),(⟨0,9,0⟩,[0,512,-1536]),(⟨1,0,0⟩,[-48,960,-9312,56320,-225600,607872,-1092000,1248256,-791440,152512,64768]),(⟨1,0,1⟩,[0,576,-8544,57600,-228384,577024,-946464,977536,-569184,133696]),(⟨1,0,2⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨1,0,3⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨1,0,4⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨1,0,6⟩,[0,-384,2816,-7040,6656]),(⟨1,0,7⟩,[0,-128,1280,-2176]),(⟨1,1,0⟩,[0,576,-8544,57600,-228384,577024,-946464,977536,-569184,133696]),(⟨1,1,1⟩,[0,576,-9696,60288,-194784,366912,-408480,241920,-50592]),(⟨1,1,2⟩,[-96,1664,-11104,41408,-98592,150656,-134176,53312]),(⟨1,1,3⟩,[-32,448,-2464,9600,-21984,26048,-14688]),(⟨1,1,4⟩,[192,-2624,11520,-24832,27712,-11968]),(⟨1,1,6⟩,[0,-128,1280,-2176]),(⟨1,1,7⟩,[128,-1280,2176]),(⟨1,2,0⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨1,2,1⟩,[-96,1664,-11104,41408,-98592,150656,-134176,53312]),(⟨1,3,0⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨1,3,1⟩,[-32,448,-2464,9600,-21984,26048,-14688]),(⟨1,4,0⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨1,4,1⟩,[192,-2624,11520,-24832,27712,-11968]),(⟨1,6,0⟩,[0,-384,2816,-7040,6656]),(⟨1,6,1⟩,[0,-128,1280,-2176]),(⟨1,7,0⟩,[0,-128,1280,-2176]),(⟨1,7,1⟩,[128,-1280,2176]),(⟨2,0,0⟩,[-16,512,-5344,33120,-138688,389984,-709600,789088,-471920,100576]),(⟨2,0,1⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨2,0,2⟩,[32,-672,5472,-22880,49504,-50400,14112,10976]),(⟨2,0,3⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨2,0,6⟩,[-64,704,-1216,-448]),(⟨2,1,0⟩,[48,-672,2368,3744,-51488,171808,-299840,281568,-113680]),(⟨2,1,1⟩,[-96,1664,-11104,41408,-98592,150656,-134176,53312]),(⟨2,2,0⟩,[32,-672,5472,-22880,49504,-50400,14112,10976]),(⟨2,3,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨2,6,0⟩,[-64,704,-1216,-448]),(⟨3,0,0⟩,[144,-2368,16384,-63168,140640,-162624,38400,116800,-96496]),(⟨3,0,1⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨3,0,2⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨3,0,3⟩,[0,1536,-10240,26624,-34816,16896]),(⟨3,0,6⟩,[0,512,-1536]),(⟨3,1,0⟩,[0,-928,9536,-41120,96896,-132704,100160,-28768]),(⟨3,1,1⟩,[-32,448,-2464,9600,-21984,26048,-14688]),(⟨3,2,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨3,3,0⟩,[0,1536,-10240,26624,-34816,16896]),(⟨3,6,0⟩,[0,512,-1536]),(⟨4,0,0⟩,[16,-1296,12912,-57648,142768,-204720,160976,-49936]),(⟨4,0,1⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨4,1,0⟩,[0,-192,2624,-11520,24832,-27712,11968]),(⟨4,1,1⟩,[192,-2624,11520,-24832,27712,-11968]),(⟨5,0,0⟩,[-96,1280,-4640,3840,12128,-30720,21280]),(⟨6,0,0⟩,[64,-64,-1088,3392,-6656,6400]),(⟨6,0,1⟩,[0,-384,2816,-7040,6656]),(⟨6,0,2⟩,[-64,704,-1216,-448]),(⟨6,0,3⟩,[0,512,-1536]),(⟨6,1,0⟩,[0,-384,2816,-7040,6656]),(⟨6,1,1⟩,[0,-128,1280,-2176]),(⟨6,2,0⟩,[-64,704,-1216,-448]),(⟨6,3,0⟩,[0,512,-1536]),(⟨7,0,0⟩,[0,-384,2816,-7040,6656]),(⟨7,0,1⟩,[0,-128,1280,-2176]),(⟨7,1,0⟩,[0,-128,1280,-2176]),(⟨7,1,1⟩,[128,-1280,2176]),(⟨8,0,0⟩,[-64,704,-1216,-448]),(⟨9,0,0⟩,[0,512,-1536])]


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
    (Poly.add (Poly.scale (K.ofRat r259) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r257*r258 : ℚ)=r259 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 10 r257 r258 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C080

#print axioms Coulomb8.Columns.C080.sound
