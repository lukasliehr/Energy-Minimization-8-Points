import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C186

def r0 : ℚ := { num := 2, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -16, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 80, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -256, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 100, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -464, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 2384, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -832, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1014, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -16, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 96, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -48, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 704, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1328, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1504, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -624, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 32, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -16, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -64, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -368, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 1376, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -944, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 64, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -256, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 640, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -768, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 320, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 32, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -128, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 64, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -640, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 800, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -2, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 16, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -80, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 256, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -100, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 464, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -2384, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 832, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1014, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -32, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 404, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -368, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 2752, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1184, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 858, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 8, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 136, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -32, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 2536, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 1080, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -32, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 704, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -1744, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 608, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -400, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 256, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -1664, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 256, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -1216, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 128, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -320, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 128, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -160, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -10, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -516, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 4016, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -7156, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 2560, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -8342, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -2, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 104, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 428, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -1408, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -232, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -320, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -234, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -5, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 68, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -1072, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 2950, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -3568, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 4420, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -352, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 325, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 16, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 320, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 80, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 384, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -160, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 8, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -344, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -400, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 1136, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -2888, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 3008, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -1360, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -2672, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 48, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -40, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -64, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -304, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -272, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 104, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 512, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -384, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 640, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -128, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 608, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 64, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -80, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -272, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 1888, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 16, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -24, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 160, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -496, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -32, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -8, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -4, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 296, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -4, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -512, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 4, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 200, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -1520, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 2592, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -468, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -86, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -244, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -688, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 2452, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -3392, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 4694, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -68, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 416, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -304, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 288, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 1976, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 8912, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -864, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 156, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -8, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 60, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -712, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -128, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -96, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 544, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -992, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 6176, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -2336, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -824, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 2480, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -4304, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 5504, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -2144, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 24, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -1280, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 3488, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -1552, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -328, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 1280, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -2432, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -64, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 240, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -704, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -3632, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 1536, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -352, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -8, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -88, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 904, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -8, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 352, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 80, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 24, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -208, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 1336, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -3648, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 6192, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -6960, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 6840, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 832, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -176, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -1088, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 1984, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -416, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 1664, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -5440, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 7552, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -8992, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -608, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 192, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -752, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 632, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1616, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 2304, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1048, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 1024, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -512, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 272, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 1112, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -80, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -704, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 8, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -72, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 1, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 40, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 50, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -696, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 1192, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -1248, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1521, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 144, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 1056, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -1992, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 2256, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -936, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -184, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 688, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1416, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 960, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1152, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 480, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 400, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -100, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 1392, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -2384, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 2496, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -3042, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -144, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 72, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1056, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 1992, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -2256, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 936, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 4, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -24, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 684, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 3476, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -4168, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 4836, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -124, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 656, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -1492, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 1608, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 396, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 512, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -1728, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 2432, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -2112, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -288, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -720, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -1256, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 3424, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -6584, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 6960, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -6840, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -4, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 76, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -456, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -876, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 212, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -848, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 2680, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -3664, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 4692, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 304, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 1128, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -316, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -200, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 800, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 3104, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -5960, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -408, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 576, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -816, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -3336, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -576, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -100, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -48, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 760, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -1296, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 234, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 268, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -940, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -228, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 12, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -72, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 108, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -36, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 216, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -640, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -4, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -268, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 940, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1336, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 228, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 1088, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -2304, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 528, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -232, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -60, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -192, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -240, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 584, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -736, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -1672, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 4176, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -600, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 92, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -260, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 872, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -68, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -480, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 264, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 80, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 160, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 136, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 15, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -146, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 296, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -286, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 360, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -751, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1248, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -1521, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 20, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 652, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -1000, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 1404, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 164, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 264, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -688, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 1416, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -176, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -568, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 1152, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 176, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -30, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 292, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -592, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 572, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 1502, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -2496, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 3042, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -20, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -652, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 1000, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -1404, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 312, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 1560, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -2888, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 4168, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -4836, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 124, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -656, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 1492, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -1608, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -396, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 1728, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -2432, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 2112, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 720, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 52, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -132, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 456, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 876, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -212, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 848, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -2680, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 3664, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -4692, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -1128, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 316, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 40, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -1024, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -3104, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 5960, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 408, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -1984, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 816, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 3336, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 2, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 8, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 100, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -760, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 1296, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -234, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -12, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 72, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -108, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 36, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -216, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -80, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 1520, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -2592, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 468, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -528, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 232, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 60, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -584, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 736, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 1672, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -4176, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 600, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -92, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 208, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 260, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -872, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 68, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -264, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -136, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -1, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 106, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 48, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -148, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 148, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 1, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8],[0,0,0,r9,r10,r11,r12,r13,r14,r15],[0,0,r1,r16,r17,r18,r19,r20,r21],[0,0,0,r22,r23,r24,r25,r26],[0,0,r27,r28,r29,r30,r31],[],[],[],[],[],[],[0,0,r32,r33,r34,r35,r36,r37,r38,r39,r40],[0,r32,r33,r41,r41,r42,r43,r44,r45,r46],[0,0,r47,r48,r49,r50,r51,r21,r52],[0,r33,r53,r1,r54,r55,r56,r57],[0,0,r18,r58,r59,r60,r61],[0,r41,r62,r63,r64,r65],[],[],[],[],[],[r0,r1,r66,r10,r67,r68,r69,r70,r71,r39,r40],[0,r72,r27,r73,r74,r75,r76,r77,r78,r79],[r80,r27,r81,r82,r83,r84,r85,r86,r87],[0,r88,r18,r62,r89,r90,r91,r92],[r93,r41,r53,r10,r94,r89,r95],[],[],[],[],[0,0,r3,r96,r97,r98,r99,r100,r101],[0,r41,r102,r103,r104,r105,r106,r107],[0,0,r108,r109,r24,r110,r111],[0,r2,r18,r112,r113,r114],[],[],[],[0,r1,r115,r116,r45,r48,r117],[0,r118,r119,r120,r121,r122],[r123,r33,r124,r17,r125],[],[],[0,0,r126],[],[],[],[0,r127,r53,r128,r74,r129,r10,r130,r131,r132],[r32,r33,r133,r10,r134,r135,r136,r137,r138,r7,r8],[0,r139,r140,r141,r142,r143,-32,r144,r145,r146],[r72,r27,r147,r104,r148,r28,r149,r74,6],[0,r16,r150,r22,r64,r151],[r33,r104,r16,r104,r11],[],[],[],[],[0,r88,r152,r153,r65,r154,r155,r156,r14,r15],[r93,r9,r16,r104,r157,r158,r159,r160,r161],[0,r34,r128,r162,r163,r164,r165,r166],[0,0,r22,r30,r167,r168,r12],[0,r2,r18,r65,r169,r170],[],[],[],[0,r102,r171,r58,r113,r172,r173,r174],[r175,r27,r176,r113,r177,r10,r178],[0,r17,r89,r179,r18,r180],[r175,r27,r9,r27,r181],[],[],[],[],[],[],[],[],[0,0,r16,r182,r183,r184,r185,r186,r187],[0,r9,r35,r92,r188,r189,r190,r191],[0,0,r192,r193,r194,r195,r196],[0,r34,r89,r197,r198,r199],[r175,r27,r2,r121,r200],[],[],[r1,r2,r16,r197,r158,r201,r202],[0,r73,r192,r1,r142,r203],[0,0,r126,r204,r205],[0,r28,r35,r28],[],[r93,r41,r206,r50,r207],[0,r113,r28,r198],[0,0,r3],[0,0,r108],[0,r208,r26,r16,r209,r210],[r211,r53,r102,r53,r212],[0,r62,r3,r111],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,2⟩,[0,0,r213,r147,r214,r150,r215,r216,r217,r218,r219]),(⟨0,0,3⟩,[0,0,0,r118,r220,r212,r221,r222,r223,r224]),(⟨0,0,4⟩,[0,0,r147,r102,r178,r152,r225,r226,r227]),(⟨0,0,5⟩,[0,0,0,r10,r109,r228,r229,r230]),(⟨0,0,6⟩,[0,0,r88,r18,r231,r78,r232]),(⟨0,1,1⟩,[0,0,r72,r88,r208,r58,r233,r234,r235,r236,r237]),(⟨0,1,2⟩,[0,0,0,r162,r238,r239,r240,r241,r242,r243]),(⟨0,1,3⟩,[0,0,r244,r245,r246,r201,r247,r248,r249]),(⟨0,1,4⟩,[0,r127,r118,r250,r251,r252,r253,r254]),(⟨0,1,5⟩,[0,0,r150,r255,r256,r257,r258]),(⟨0,1,6⟩,[0,r9,r22,r259,r260,r261]),(⟨0,2,0⟩,[0,0,r213,r147,r214,r150,r215,r216,r217,r218,r219]),(⟨0,2,1⟩,[0,0,0,r162,r238,r239,r240,r241,r242,r243]),(⟨0,2,2⟩,[0,0,r103,r170,r262,r263,r264,r265,r266]),(⟨0,2,3⟩,[0,r267,r162,r244,r115,r268,r269,r270]),(⟨0,2,4⟩,[0,0,r271,r272,r273,r274,r275]),(⟨0,2,5⟩,[0,r214,r92,r276,r259,r277]),(⟨0,2,6⟩,[r127,r9,r103,r128,r278]),(⟨0,3,0⟩,[0,0,0,r118,r220,r212,r221,r222,r223,r224]),(⟨0,3,1⟩,[0,0,r244,r245,r246,r201,r247,r248,r249]),(⟨0,3,2⟩,[0,r267,r162,r244,r115,r268,r269,r270]),(⟨0,3,3⟩,[0,0,r279,r280,-48,r281,r282]),(⟨0,3,4⟩,[0,r118,r10,r9,r92,r283]),(⟨0,3,5⟩,[0,0,r260,r284,r191]),(⟨0,3,6⟩,[0,r22,r150,r285]),(⟨0,4,0⟩,[0,0,r147,r102,r178,r152,r225,r226,r227]),(⟨0,4,1⟩,[0,r127,r118,r250,r251,r252,r253,r254]),(⟨0,4,2⟩,[0,0,r271,r272,r273,r274,r275]),(⟨0,4,3⟩,[0,r118,r10,r9,r92,r283]),(⟨0,4,4⟩,[r147,r16,r286,32,r287]),(⟨0,4,5⟩,[0,r18,r64,r288]),(⟨0,4,6⟩,[0,0,r58]),(⟨0,5,0⟩,[0,0,0,r10,r109,r228,r229,r230]),(⟨0,5,1⟩,[0,0,r150,r255,r256,r257,r258]),(⟨0,5,2⟩,[0,r214,r92,r276,r259,r277]),(⟨0,5,3⟩,[0,0,r260,r284,r191]),(⟨0,5,4⟩,[0,r18,r64,r288]),(⟨0,5,5⟩,[0,0,r205]),(⟨0,6,0⟩,[0,0,r88,r18,r231,r78,r232]),(⟨0,6,1⟩,[0,r9,r22,r259,r260,r261]),(⟨0,6,2⟩,[r127,r9,r103,r128,r278]),(⟨0,6,3⟩,[0,r22,r150,r285]),(⟨0,6,4⟩,[0,0,r58]),(⟨1,0,2⟩,[0,r72,r88,r178,r128,r289,r290,r291,r292,r293]),(⟨1,0,3⟩,[0,0,r244,r245,r294,r102,r295,r183,r296]),(⟨1,0,4⟩,[0,r297,r298,r299,r102,r300,r301,r296]),(⟨1,0,5⟩,[0,0,r18,r58,r22,r302,r303]),(⟨1,0,6⟩,[0,r9,r22,r53,r18,r180]),(⟨1,1,1⟩,[0,r127,r53,r128,r74,r129,r10,r130,r131,r132]),(⟨1,1,2⟩,[0,0,r304,r181,r305,r290,r306,r307,r308]),(⟨1,1,3⟩,[0,r53,r198,r57,r26,r309,r310,r311]),(⟨1,1,4⟩,[r267,r162,r304,r290,4,r312,r313]),(⟨1,1,5⟩,[0,r102,r314,r10,r198,r315]),(⟨1,1,6⟩,[r211,r53,r102,r53,r212]),(⟨1,2,0⟩,[0,r72,r88,r178,r128,r289,r290,r291,r292,r293]),(⟨1,2,1⟩,[0,0,r304,r181,r305,r290,r306,r307,r308]),(⟨1,2,2⟩,[0,r214,r316,r317,r318,r319,r320,r321]),(⟨1,2,3⟩,[r127,r118,r322,r182,r323,r324,r325]),(⟨1,2,4⟩,[0,r298,r142,r290,r326,r327]),(⟨1,2,5⟩,[0,0,r22,r150,r328]),(⟨1,2,6⟩,[0,r22,r150,r328]),(⟨1,3,0⟩,[0,0,r244,r245,r294,r102,r295,r183,r296]),(⟨1,3,1⟩,[0,r53,r198,r57,r26,r309,r310,r311]),(⟨1,3,2⟩,[r127,r118,r322,r182,r323,r324,r325]),(⟨1,3,3⟩,[0,r329,r78,r53,r12,r330]),(⟨1,3,4⟩,[r147,r16,r48,r331,r332]),(⟨1,3,5⟩,[0,r18,r64,r260]),(⟨1,4,0⟩,[0,r297,r298,r299,r102,r300,r301,r296]),(⟨1,4,1⟩,[r267,r162,r304,r290,4,r312,r313]),(⟨1,4,2⟩,[0,r298,r142,r290,r326,r327]),(⟨1,4,3⟩,[r147,r16,r48,r331,r332]),(⟨1,5,0⟩,[0,0,r18,r58,r22,r302,r303]),(⟨1,5,1⟩,[0,r102,r314,r10,r198,r315]),(⟨1,5,2⟩,[0,0,r22,r150,r328]),(⟨1,5,3⟩,[0,r18,r64,r260]),(⟨1,6,0⟩,[0,r9,r22,r53,r18,r180]),(⟨1,6,1⟩,[r211,r53,r102,r53,r212]),(⟨1,6,2⟩,[0,r22,r150,r328]),(⟨2,0,2⟩,[r213,r147,r333,r162,r334,r335,r336,r337,r338,r339,r340]),(⟨2,0,3⟩,[0,r267,r162,r341,r259,r342,r343,r344,r242,r243]),(⟨2,0,4⟩,[r267,r162,r211,r182,r345,r346,r182,r347,r348]),(⟨2,0,5⟩,[0,r211,r53,r349,r56,r350,r351,r326]),(⟨2,0,6⟩,[r127,r9,r178,r352,r304,r26,r57]),(⟨2,1,1⟩,[r72,r88,r353,r290,r354,r355,r356,r261,r357,r358,r359]),(⟨2,1,2⟩,[0,r127,r118,r360,r142,r361,r362,r363,r223,r224]),(⟨2,1,3⟩,[r127,r118,r118,r364,r7,r365,r366,r367,r368]),(⟨2,1,4⟩,[0,r267,r162,r369,r370,r371,r372,r373]),(⟨2,1,5⟩,[0,0,r64,r205,r374,r375,r376]),(⟨2,1,6⟩,[0,r88,r18,r142,r328,r377]),(⟨2,2,0⟩,[r213,r147,r333,r162,r334,r335,r336,r337,r338,r339,r340]),(⟨2,2,1⟩,[0,r127,r118,r360,r142,r361,r362,r363,r223,r224]),(⟨2,2,2⟩,[0,0,r16,r182,r183,r184,r185,r186,r187]),(⟨2,2,3⟩,[0,r267,r211,r378,r102,r379,r380,r381]),(⟨2,2,4⟩,[0,0,r382,r383,r384,r385,r386]),(⟨2,2,5⟩,[0,r103,r331,r141,r142,r387]),(⟨2,2,6⟩,[r267,r88,r214,r48,r388]),(⟨2,3,0⟩,[0,r267,r162,r341,r259,r342,r343,r344,r242,r243]),(⟨2,3,1⟩,[r127,r118,r118,r364,r7,r365,r366,r367,r368]),(⟨2,3,2⟩,[0,r267,r211,r378,r102,r379,r380,r381]),(⟨2,3,3⟩,[r147,r16,r389,r390,40,r391,r392]),(⟨2,3,4⟩,[0,r162,r152,r88,r331,r393]),(⟨2,3,5⟩,[0,0,r328,r303,r394]),(⟨2,3,6⟩,[0,r18,r64,r288]),(⟨2,4,0⟩,[r267,r162,r211,r182,r345,r346,r182,r347,r348]),(⟨2,4,1⟩,[0,r267,r162,r369,r370,r371,r372,r373]),(⟨2,4,2⟩,[0,0,r382,r383,r384,r385,r386]),(⟨2,4,3⟩,[0,r162,r152,r88,r331,r393]),(⟨2,4,4⟩,[r211,r53,r395,-32,r396]),(⟨2,4,5⟩,[0,r22,r150,r285]),(⟨2,4,6⟩,[0,0,r23]),(⟨2,5,0⟩,[0,r211,r53,r349,r56,r350,r351,r326]),(⟨2,5,1⟩,[0,0,r64,r205,r374,r375,r376]),(⟨2,5,2⟩,[0,r103,r331,r141,r142,r387]),(⟨2,5,3⟩,[0,0,r328,r303,r394]),(⟨2,5,4⟩,[0,r22,r150,r285]),(⟨2,5,5⟩,[0,0,r255]),(⟨2,6,0⟩,[r127,r9,r178,r352,r304,r26,r57]),(⟨2,6,1⟩,[0,r88,r18,r142,r328,r377]),(⟨2,6,2⟩,[r267,r88,r214,r48,r388]),(⟨2,6,3⟩,[0,r18,r64,r288]),(⟨2,6,4⟩,[0,0,r23]),(⟨3,0,2⟩,[0,r397,r9,r398,r48,r399,r102,r400,r401,r402]),(⟨3,0,3⟩,[0,0,r304,r181,r305,r290,r306,r307,r308]),(⟨3,0,4⟩,[0,r403,r404,r405,r290,r406,r407,r308]),(⟨3,0,5⟩,[0,0,r22,r23,r18,r24,r284]),(⟨3,0,6⟩,[0,r88,r18,r16,r22,r408]),(⟨3,1,1⟩,[0,r267,r16,r48,r231,r279,r152,r409,r410,r411]),(⟨3,1,2⟩,[0,0,r244,r245,r294,r102,r295,r183,r296]),(⟨3,1,3⟩,[0,r16,r314,r232,r78,r190,r202,r412]),(⟨3,1,4⟩,[r127,r118,r244,r102,-4,r413,r414]),(⟨3,1,5⟩,[0,r290,r198,r152,r314,r415]),(⟨3,1,6⟩,[r147,r16,r290,r16,r239]),(⟨3,2,0⟩,[0,r397,r9,r398,r48,r399,r102,r400,r401,r402]),(⟨3,2,1⟩,[0,0,r244,r245,r294,r102,r295,r183,r296]),(⟨3,2,2⟩,[0,r103,r170,r416,r417,r418,r419,r420]),(⟨3,2,3⟩,[r267,r162,r421,r422,r423,r424,r425]),(⟨3,2,4⟩,[0,r404,r259,r102,r230,r426]),(⟨3,2,5⟩,[0,0,r18,r64,r260]),(⟨3,2,6⟩,[0,r18,r64,r260]),(⟨3,3,0⟩,[0,0,r304,r181,r305,r290,r306,r307,r308]),(⟨3,3,1⟩,[0,r16,r314,r232,r78,r190,r202,r412]),(⟨3,3,2⟩,[r267,r162,r421,r422,r423,r424,r425]),(⟨3,3,3⟩,[0,r208,r26,r16,r209,r210]),(⟨3,3,4⟩,[r211,r53,r128,r92,r427]),(⟨3,3,5⟩,[0,r22,r150,r328]),(⟨3,4,0⟩,[0,r403,r404,r405,r290,r406,r407,r308]),(⟨3,4,1⟩,[r127,r118,r244,r102,-4,r413,r414]),(⟨3,4,2⟩,[0,r404,r259,r102,r230,r426]),(⟨3,4,3⟩,[r211,r53,r128,r92,r427]),(⟨3,5,0⟩,[0,0,r22,r23,r18,r24,r284]),(⟨3,5,1⟩,[0,r290,r198,r152,r314,r415]),(⟨3,5,2⟩,[0,0,r18,r64,r260]),(⟨3,5,3⟩,[0,r22,r150,r328]),(⟨3,6,0⟩,[0,r88,r18,r16,r22,r408]),(⟨3,6,1⟩,[r147,r16,r290,r16,r239]),(⟨3,6,2⟩,[0,r18,r64,r260]),(⟨4,0,2⟩,[r428,r211,r9,r9,r429,r245,r18,r430,-9]),(⟨4,0,3⟩,[0,r127,r118,r127,r220,r431,r178,12]),(⟨4,0,4⟩,[r127,r118,0,r331,r405,r245,8]),(⟨4,0,5⟩,[0,r147,r16,r329,r74,-8]),(⟨4,0,6⟩,[r267,r88,r214,r48,-4]),(⟨4,1,1⟩,[r397,r9,r16,r16,r382,r430,r64,r432,18]),(⟨4,1,2⟩,[0,r267,r162,r267,r238,r433,r398,-12]),(⟨4,1,3⟩,[r267,r162,r267,r238,r433,r398,-12]),(⟨4,2,0⟩,[r428,r211,r9,r9,r429,r245,r18,r430,-9]),(⟨4,2,1⟩,[0,r267,r162,r267,r238,r433,r398,-12]),(⟨4,2,2⟩,[0,0,r211,r53,r208,r231,8]),(⟨4,2,3⟩,[0,r211,r53,r208,r231,8]),(⟨4,3,0⟩,[0,r127,r118,r127,r220,r431,r178,12]),(⟨4,3,1⟩,[r267,r162,r267,r238,r433,r398,-12]),(⟨4,3,2⟩,[0,r211,r53,r208,r231,8]),(⟨4,3,3⟩,[r211,r53,r208,r231,8]),(⟨4,4,0⟩,[r127,r118,0,r331,r405,r245,8]),(⟨4,5,0⟩,[0,r147,r16,r329,r74,-8]),(⟨4,6,0⟩,[r267,r88,r214,r48,-4])]


noncomputable def sourceLeft : Poly := [(⟨0,0,1⟩,[0,-1,4,-12,16,-39]),(⟨0,0,2⟩,[0,0,12,-24,12]),(⟨0,0,3⟩,[0,4,-8,20]),(⟨0,1,0⟩,[0,1,-4,12,-16,39]),(⟨0,1,2⟩,[0,-10,20,-42]),(⟨0,1,3⟩,[-2,4,-18]),(⟨0,2,0⟩,[0,0,-12,24,-12]),(⟨0,2,1⟩,[0,10,-20,42]),(⟨0,2,3⟩,[0,-16]),(⟨0,3,0⟩,[0,-4,8,-20]),(⟨0,3,1⟩,[2,-4,18]),(⟨0,3,2⟩,[0,16]),(⟨1,0,1⟩,[1,-4,0,8,-21]),(⟨1,0,2⟩,[0,-2,4,14]),(⟨1,0,3⟩,[-2,4,14]),(⟨1,1,0⟩,[-1,4,0,-8,21]),(⟨1,2,0⟩,[0,2,-4,-14]),(⟨1,3,0⟩,[2,-4,-14])]
noncomputable def sourceRight : Poly := [(⟨0,0,1⟩,[0,-1,4,-12,16,-39]),(⟨0,0,2⟩,[0,0,12,-24,12]),(⟨0,0,3⟩,[0,4,-8,20]),(⟨0,1,0⟩,[0,1,-4,12,-16,39]),(⟨0,1,2⟩,[0,-10,20,-42]),(⟨0,1,3⟩,[-2,4,-18]),(⟨0,2,0⟩,[0,0,-12,24,-12]),(⟨0,2,1⟩,[0,10,-20,42]),(⟨0,2,3⟩,[0,-16]),(⟨0,3,0⟩,[0,-4,8,-20]),(⟨0,3,1⟩,[2,-4,18]),(⟨0,3,2⟩,[0,16]),(⟨1,0,1⟩,[1,-4,0,8,-21]),(⟨1,0,2⟩,[0,-2,4,14]),(⟨1,0,3⟩,[-2,4,14]),(⟨1,1,0⟩,[-1,4,0,-8,21]),(⟨1,2,0⟩,[0,2,-4,-14]),(⟨1,3,0⟩,[2,-4,-14])]

theorem left_checked :
    (Poly.add (Data.S7_odd.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r434) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S7_odd.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r434) sourceRight))).isZero := by decide +kernel

noncomputable def partial18 : Poly := []

theorem partial_sound18 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 18)
      sourceRight).eval u v t=partial18.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨1,2,0⟩,[0,2,-4,-14]),(⟨1,3,0⟩,[2,-4,-14])]

noncomputable def partial16 : Poly := [(⟨1,2,1⟩,[0,0,-2,12,-26,24,26,-68,546]),(⟨1,2,2⟩,[0,0,0,24,-96,-48,288,-168]),(⟨1,2,3⟩,[0,0,8,-32,16,32,-280]),(⟨1,3,0⟩,[0,0,2,-12,26,-24,-26,68,-546]),(⟨1,3,1⟩,[0,-2,12,-26,24,26,-68,546]),(⟨1,3,2⟩,[0,0,4,-16,-72,176,420]),(⟨1,3,3⟩,[0,4,-16,-8,48,-28]),(⟨1,4,0⟩,[0,2,-12,2,72,22,-220,-378]),(⟨1,4,1⟩,[0,0,20,-80,24,112,-588]),(⟨1,4,2⟩,[0,-20,80,-24,-112,588]),(⟨1,4,3⟩,[-4,16,-56,80,476]),(⟨1,5,0⟩,[0,0,-32,128,32,-320,448]),(⟨1,5,1⟩,[0,24,-96,48,96,-840]),(⟨1,5,2⟩,[0,0,32,-64,-224]),(⟨1,5,3⟩,[0,-32,64,224]),(⟨1,6,0⟩,[0,-8,32,-16,-32,280]),(⟨1,6,1⟩,[4,-16,24,-16,-252]),(⟨1,6,2⟩,[0,32,-64,-224]),(⟨2,2,1⟩,[0,2,-12,2,72,-74,-28,294]),(⟨2,2,2⟩,[0,0,-4,16,40,-112,-196]),(⟨2,2,3⟩,[0,-4,16,40,-112,-196]),(⟨2,3,0⟩,[0,-2,12,-2,-72,74,28,-294]),(⟨2,3,1⟩,[2,-12,2,72,-74,-28,294]),(⟨2,3,2⟩,[0,-4,16,40,-112,-196]),(⟨2,3,3⟩,[-4,16,40,-112,-196]),(⟨2,4,0⟩,[-2,12,2,-88,34,140,-98]),(⟨2,5,0⟩,[0,8,-32,-80,224,392]),(⟨2,6,0⟩,[4,-16,-40,112,196])]


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

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[0,-1,8,-28,56,-50,-24,380,-648,819]),(⟨1,0,3⟩,[0,0,14,-84,134,24,-470,668,-798]),(⟨1,0,4⟩,[0,6,-36,54,24,-126,108,-798]),(⟨1,0,5⟩,[0,0,-32,128,32,-320,448]),(⟨1,0,6⟩,[0,-8,32,-16,-32,280]),(⟨1,1,1⟩,[0,2,-16,56,-112,100,48,-760,1296,-1638]),(⟨1,1,2⟩,[0,0,-14,84,-134,-24,470,-668,798]),(⟨1,1,3⟩,[0,-16,96,-200,160,544,-1152,1848]),(⟨1,1,4⟩,[-2,12,-14,-24,98,-116,-210]),(⟨1,1,5⟩,[0,24,-96,48,96,-840]),(⟨1,1,6⟩,[4,-16,24,-16,-252]),(⟨1,2,0⟩,[0,-1,8,-28,56,-50,-24,380,-648,819]),(⟨1,2,1⟩,[0,0,-14,84,-134,-24,470,-668,798]),(⟨1,2,2⟩,[0,20,-120,292,-368,-836,2088,-2100]),(⟨1,2,3⟩,[2,-12,46,-104,-130,436,-238]),(⟨1,2,4⟩,[0,-36,144,-24,-240,924]),(⟨1,2,5⟩,[0,0,32,-64,-224]),(⟨1,2,6⟩,[0,32,-64,-224]),(⟨1,3,0⟩,[0,0,14,-84,134,24,-470,668,-798]),(⟨1,3,1⟩,[0,-16,96,-200,160,544,-1152,1848]),(⟨1,3,2⟩,[2,-12,46,-104,-130,436,-238]),(⟨1,3,3⟩,[0,40,-160,-16,352,-728]),(⟨1,3,4⟩,[-4,16,-56,80,476]),(⟨1,3,5⟩,[0,-32,64,224]),(⟨1,4,0⟩,[0,6,-36,54,24,-126,108,-798]),(⟨1,4,1⟩,[-2,12,-14,-24,98,-116,-210]),(⟨1,4,2⟩,[0,-36,144,-24,-240,924]),(⟨1,4,3⟩,[-4,16,-56,80,476]),(⟨1,5,0⟩,[0,0,-32,128,32,-320,448]),(⟨1,5,1⟩,[0,24,-96,48,96,-840]),(⟨1,5,2⟩,[0,0,32,-64,-224]),(⟨1,5,3⟩,[0,-32,64,224]),(⟨1,6,0⟩,[0,-8,32,-16,-32,280]),(⟨1,6,1⟩,[4,-16,24,-16,-252]),(⟨1,6,2⟩,[0,32,-64,-224]),(⟨2,0,2⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,0,3⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,0,4⟩,[-4,24,0,-160,108,168,-392]),(⟨2,0,5⟩,[0,8,-32,-80,224,392]),(⟨2,0,6⟩,[4,-16,-40,112,196]),(⟨2,1,1⟩,[-2,16,-32,-32,212,-336,-128,672,-882]),(⟨2,1,2⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,1,3⟩,[4,-24,4,144,-148,-56,588]),(⟨2,2,0⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,2,1⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,2,2⟩,[0,0,-8,32,80,-224,-392]),(⟨2,2,3⟩,[0,-8,32,80,-224,-392]),(⟨2,3,0⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,3,1⟩,[4,-24,4,144,-148,-56,588]),(⟨2,3,2⟩,[0,-8,32,80,-224,-392]),(⟨2,3,3⟩,[-8,32,80,-224,-392]),(⟨2,4,0⟩,[-4,24,0,-160,108,168,-392]),(⟨2,5,0⟩,[0,8,-32,-80,224,392]),(⟨2,6,0⟩,[4,-16,-40,112,196])]


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

noncomputable def partial8 : Poly := [(⟨0,2,4⟩,[0,0,16,-64,192,-256,624]),(⟨0,2,5⟩,[0,0,0,-192,384,-192]),(⟨0,2,6⟩,[0,0,-64,128,-320]),(⟨0,3,1⟩,[0,0,4,-24,100,-240,524,-632,780]),(⟨0,3,2⟩,[0,-2,12,-106,344,-838,1020,-942]),(⟨0,3,3⟩,[0,0,-24,96,-272,352,-1432]),(⟨0,3,4⟩,[0,8,-32,336,-608,552]),(⟨0,3,5⟩,[0,0,224,-448,992]),(⟨0,3,6⟩,[0,32,-64,288]),(⟨0,4,0⟩,[0,0,-4,24,-100,240,-524,632,-780]),(⟨0,4,1⟩,[0,2,-12,58,-152,358,-444,702]),(⟨0,4,2⟩,[0,0,56,-224,720,-992,1464]),(⟨0,4,3⟩,[0,-12,48,-8,-80,-204]),(⟨0,4,4⟩,[-4,16,-408,784,-1668]),(⟨0,4,5⟩,[0,-32,64,-288]),(⟨0,4,6⟩,[0,0,256]),(⟨0,5,0⟩,[0,0,0,48,-192,480,-576,240]),(⟨0,5,1⟩,[0,0,-64,256,-864,1216,-1056]),(⟨0,5,2⟩,[0,20,-80,152,-144,564]),(⟨0,5,3⟩,[0,0,288,-576,1312]),(⟨0,5,4⟩,[0,-64,128,-576]),(⟨0,5,5⟩,[0,0,-512]),(⟨0,6,0⟩,[0,0,16,-64,224,-320,400]),(⟨0,6,1⟩,[0,-16,64,-288,448,-720]),(⟨0,6,2⟩,[4,-16,-40,112,-316]),(⟨0,6,3⟩,[0,64,-128,576]),(⟨0,6,4⟩,[0,0,256]),(⟨1,0,2⟩,[0,-1,8,-28,56,-50,-24,380,-648,819]),(⟨1,0,3⟩,[0,0,14,-84,134,24,-470,668,-798]),(⟨1,0,4⟩,[0,6,-36,54,24,-126,108,-798]),(⟨1,0,5⟩,[0,0,-32,128,32,-320,448]),(⟨1,0,6⟩,[0,-8,32,-16,-32,280]),(⟨1,1,1⟩,[0,2,-16,56,-112,100,48,-760,1296,-1638]),(⟨1,1,2⟩,[0,0,-14,84,-134,-24,470,-668,798]),(⟨1,1,3⟩,[0,-16,96,-200,160,544,-1152,1848]),(⟨1,1,4⟩,[-2,12,-14,-24,98,-116,-210]),(⟨1,1,5⟩,[0,24,-96,48,96,-840]),(⟨1,1,6⟩,[4,-16,24,-16,-252]),(⟨1,2,0⟩,[0,-1,8,-28,56,-50,-24,380,-648,819]),(⟨1,2,1⟩,[0,0,-14,84,-134,-24,470,-668,798]),(⟨1,2,2⟩,[0,20,-120,292,-368,-836,2088,-2100]),(⟨1,2,3⟩,[2,-12,46,-104,-130,436,-238]),(⟨1,2,4⟩,[0,-52,208,-24,-368,1260]),(⟨1,2,5⟩,[0,0,64,-128,-448]),(⟨1,2,6⟩,[0,64,-128,-448]),(⟨1,3,0⟩,[0,0,14,-84,134,24,-470,668,-798]),(⟨1,3,1⟩,[0,-20,120,-252,208,692,-1480,2268]),(⟨1,3,2⟩,[4,-24,88,-192,-188,696,-896]),(⟨1,3,3⟩,[0,76,-304,-24,656,-1428]),(⟨1,3,4⟩,[-8,32,-112,160,952]),(⟨1,3,5⟩,[0,-64,128,448]),(⟨1,4,0⟩,[0,10,-60,106,-24,-274,436,-1218]),(⟨1,4,1⟩,[-4,24,-48,32,172,-344,168]),(⟨1,4,2⟩,[0,-52,208,-24,-368,1260]),(⟨1,4,3⟩,[-4,16,-88,144,700]),(⟨1,5,0⟩,[0,0,-40,160,16,-352,728]),(⟨1,5,1⟩,[0,28,-112,72,80,-1092]),(⟨1,5,2⟩,[0,0,64,-128,-448]),(⟨1,5,3⟩,[0,-64,128,448]),(⟨1,6,0⟩,[0,-16,64,-32,-64,560]),(⟨1,6,1⟩,[8,-32,48,-32,-504]),(⟨1,6,2⟩,[0,64,-128,-448]),(⟨2,0,2⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,0,3⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,0,4⟩,[-4,24,0,-160,108,168,-392]),(⟨2,0,5⟩,[0,8,-32,-80,224,392]),(⟨2,0,6⟩,[4,-16,-40,112,196]),(⟨2,1,1⟩,[-2,16,-32,-32,212,-336,-128,672,-882]),(⟨2,1,2⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,1,3⟩,[4,-24,4,144,-148,-56,588]),(⟨2,2,0⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,2,1⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,2,2⟩,[0,0,-8,32,80,-224,-392]),(⟨2,2,3⟩,[0,-8,32,80,-224,-392]),(⟨2,3,0⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,3,1⟩,[4,-24,4,144,-148,-56,588]),(⟨2,3,2⟩,[0,-8,32,80,-224,-392]),(⟨2,3,3⟩,[-8,32,80,-224,-392]),(⟨2,4,0⟩,[-4,24,0,-160,108,168,-392]),(⟨2,5,0⟩,[0,8,-32,-80,224,392]),(⟨2,6,0⟩,[4,-16,-40,112,196])]


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

noncomputable def partial4 : Poly := [(⟨0,1,3⟩,[0,0,10,-60,242,-568,1214,-1452,1638]),(⟨0,1,4⟩,[0,2,-12,-62,328,-746,804,198]),(⟨0,1,5⟩,[0,0,-64,256,-864,1216,-1056]),(⟨0,1,6⟩,[0,-8,32,-144,224,-360]),(⟨0,2,1⟩,[0,0,0,12,-72,252,-528,996,-1128,468]),(⟨0,2,2⟩,[0,0,-20,120,-628,1712,-3292,3480,-3420]),(⟨0,2,3⟩,[0,-2,12,14,-136,266,-228,-438]),(⟨0,2,4⟩,[0,0,156,-624,1960,-2672,3228]),(⟨0,2,5⟩,[0,40,-160,496,-672,1320]),(⟨0,2,6⟩,[4,-16,24,-16,4]),(⟨0,3,0⟩,[0,0,0,-12,72,-252,528,-996,1128,-468]),(⟨0,3,1⟩,[0,0,14,-84,342,-808,1738,-2084,2418]),(⟨0,3,2⟩,[0,-2,12,134,-616,1370,-1476,66]),(⟨0,3,3⟩,[0,0,-176,704,-2080,2752,-4528]),(⟨0,3,4⟩,[0,-32,128,-352,448,-960]),(⟨0,3,5⟩,[0,0,384,-768,1664]),(⟨0,3,6⟩,[0,64,-128,576]),(⟨0,4,0⟩,[0,0,-4,24,44,-336,340,56,-636]),(⟨0,4,1⟩,[0,2,-12,-182,808,-1850,2052,-306]),(⟨0,4,2⟩,[0,0,196,-784,2488,-3408,4068]),(⟨0,4,3⟩,[0,-24,96,-16,-160,-408]),(⟨0,4,4⟩,[-8,32,-816,1568,-3336]),(⟨0,4,5⟩,[0,-64,128,-576]),(⟨0,4,6⟩,[0,0,256]),(⟨0,5,0⟩,[0,0,0,96,-384,960,-1152,480]),(⟨0,5,1⟩,[0,0,-128,512,-1728,2432,-2112]),(⟨0,5,2⟩,[0,40,-160,304,-288,1128]),(⟨0,5,3⟩,[0,0,448,-896,1984]),(⟨0,5,4⟩,[0,-64,128,-576]),(⟨0,5,5⟩,[0,0,-512]),(⟨0,6,0⟩,[0,0,16,-64,224,-320,400]),(⟨0,6,1⟩,[0,-16,64,-288,448,-720]),(⟨0,6,2⟩,[4,-16,-40,112,-316]),(⟨0,6,3⟩,[0,64,-128,576]),(⟨0,6,4⟩,[0,0,256]),(⟨1,0,2⟩,[0,-1,8,-28,56,-50,-24,380,-648,819]),(⟨1,0,3⟩,[0,0,14,-84,134,24,-470,668,-798]),(⟨1,0,4⟩,[0,6,-36,54,24,-126,108,-798]),(⟨1,0,5⟩,[0,0,-32,128,32,-320,448]),(⟨1,0,6⟩,[0,-8,32,-16,-32,280]),(⟨1,1,1⟩,[0,2,-16,56,-112,100,48,-760,1296,-1638]),(⟨1,1,2⟩,[0,0,-14,84,-134,-24,470,-668,798]),(⟨1,1,3⟩,[0,-26,156,-322,248,914,-1908,2730]),(⟨1,1,4⟩,[-4,24,-28,-48,196,-232,-420]),(⟨1,1,5⟩,[0,48,-192,96,192,-1680]),(⟨1,1,6⟩,[8,-32,48,-32,-504]),(⟨1,2,0⟩,[0,-1,8,-28,56,-50,-24,380,-648,819]),(⟨1,2,1⟩,[0,0,-26,156,-242,-72,914,-1268,1050]),(⟨1,2,2⟩,[0,40,-240,560,-640,-1624,3888,-4032]),(⟨1,2,3⟩,[4,-24,84,-176,-276,840,-196]),(⟨1,2,4⟩,[0,-72,288,-48,-480,1848]),(⟨1,2,5⟩,[0,0,64,-128,-448]),(⟨1,2,6⟩,[0,64,-128,-448]),(⟨1,3,0⟩,[0,0,26,-156,242,72,-914,1268,-1050]),(⟨1,3,1⟩,[0,-30,180,-374,296,1062,-2236,3150]),(⟨1,3,2⟩,[4,-24,68,-112,-212,584,-308]),(⟨1,3,3⟩,[0,72,-288,-48,672,-1176]),(⟨1,3,4⟩,[-8,32,-112,160,952]),(⟨1,3,5⟩,[0,-64,128,448]),(⟨1,4,0⟩,[0,10,-60,82,72,-226,148,-1050]),(⟨1,4,1⟩,[-4,24,-28,-48,196,-232,-420]),(⟨1,4,2⟩,[0,-72,288,-48,-480,1848]),(⟨1,4,3⟩,[-8,32,-112,160,952]),(⟨1,5,0⟩,[0,0,-64,256,64,-640,896]),(⟨1,5,1⟩,[0,48,-192,96,192,-1680]),(⟨1,5,2⟩,[0,0,64,-128,-448]),(⟨1,5,3⟩,[0,-64,128,448]),(⟨1,6,0⟩,[0,-16,64,-32,-64,560]),(⟨1,6,1⟩,[8,-32,48,-32,-504]),(⟨1,6,2⟩,[0,64,-128,-448]),(⟨2,0,2⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,0,3⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,0,4⟩,[-4,24,0,-160,108,168,-392]),(⟨2,0,5⟩,[0,8,-32,-80,224,392]),(⟨2,0,6⟩,[4,-16,-40,112,196]),(⟨2,1,1⟩,[-2,16,-32,-32,212,-336,-128,672,-882]),(⟨2,1,2⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,1,3⟩,[4,-24,4,144,-148,-56,588]),(⟨2,2,0⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,2,1⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,2,2⟩,[0,0,-8,32,80,-224,-392]),(⟨2,2,3⟩,[0,-8,32,80,-224,-392]),(⟨2,3,0⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,3,1⟩,[4,-24,4,144,-148,-56,588]),(⟨2,3,2⟩,[0,-8,32,80,-224,-392]),(⟨2,3,3⟩,[-8,32,80,-224,-392]),(⟨2,4,0⟩,[-4,24,0,-160,108,168,-392]),(⟨2,5,0⟩,[0,8,-32,-80,224,392]),(⟨2,6,0⟩,[4,-16,-40,112,196])]


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

noncomputable def partial0 : Poly := [(⟨0,0,2⟩,[0,0,1,-8,40,-128,350,-696,1192,-1248,1521]),(⟨0,0,3⟩,[0,0,0,-24,144,-504,1056,-1992,2256,-936]),(⟨0,0,4⟩,[0,0,-8,48,-56,-96,-184,688,-1416]),(⟨0,0,5⟩,[0,0,0,96,-384,960,-1152,480]),(⟨0,0,6⟩,[0,0,16,-64,224,-320,400]),(⟨0,1,1⟩,[0,0,-2,16,-80,256,-700,1392,-2384,2496,-3042]),(⟨0,1,2⟩,[0,0,0,24,-144,504,-1056,1992,-2256,936]),(⟨0,1,3⟩,[0,0,28,-168,684,-1616,3476,-4168,4836]),(⟨0,1,4⟩,[0,4,-24,-124,656,-1492,1608,396]),(⟨0,1,5⟩,[0,0,-128,512,-1728,2432,-2112]),(⟨0,1,6⟩,[0,-16,64,-288,448,-720]),(⟨0,2,0⟩,[0,0,1,-8,40,-128,350,-696,1192,-1248,1521]),(⟨0,2,1⟩,[0,0,0,24,-144,504,-1056,1992,-2256,936]),(⟨0,2,2⟩,[0,0,-40,240,-1256,3424,-6584,6960,-6840]),(⟨0,2,3⟩,[0,-4,24,28,-272,532,-456,-876]),(⟨0,2,4⟩,[0,0,212,-848,2680,-3664,4692]),(⟨0,2,5⟩,[0,40,-160,304,-288,1128]),(⟨0,2,6⟩,[4,-16,-40,112,-316]),(⟨0,3,0⟩,[0,0,0,-24,144,-504,1056,-1992,2256,-936]),(⟨0,3,1⟩,[0,0,28,-168,684,-1616,3476,-4168,4836]),(⟨0,3,2⟩,[0,-4,24,28,-272,532,-456,-876]),(⟨0,3,3⟩,[0,0,-200,800,-2352,3104,-5960]),(⟨0,3,4⟩,[0,-24,96,-16,-160,-408]),(⟨0,3,5⟩,[0,0,448,-896,1984]),(⟨0,3,6⟩,[0,64,-128,576]),(⟨0,4,0⟩,[0,0,-8,48,-56,-96,-184,688,-1416]),(⟨0,4,1⟩,[0,4,-24,-124,656,-1492,1608,396]),(⟨0,4,2⟩,[0,0,212,-848,2680,-3664,4692]),(⟨0,4,3⟩,[0,-24,96,-16,-160,-408]),(⟨0,4,4⟩,[-8,32,-816,1568,-3336]),(⟨0,4,5⟩,[0,-64,128,-576]),(⟨0,4,6⟩,[0,0,256]),(⟨0,5,0⟩,[0,0,0,96,-384,960,-1152,480]),(⟨0,5,1⟩,[0,0,-128,512,-1728,2432,-2112]),(⟨0,5,2⟩,[0,40,-160,304,-288,1128]),(⟨0,5,3⟩,[0,0,448,-896,1984]),(⟨0,5,4⟩,[0,-64,128,-576]),(⟨0,5,5⟩,[0,0,-512]),(⟨0,6,0⟩,[0,0,16,-64,224,-320,400]),(⟨0,6,1⟩,[0,-16,64,-288,448,-720]),(⟨0,6,2⟩,[4,-16,-40,112,-316]),(⟨0,6,3⟩,[0,64,-128,576]),(⟨0,6,4⟩,[0,0,256]),(⟨1,0,2⟩,[0,-2,16,-56,112,-100,-48,760,-1296,1638]),(⟨1,0,3⟩,[0,0,28,-168,268,48,-940,1336,-1596]),(⟨1,0,4⟩,[0,12,-72,108,48,-252,216,-1596]),(⟨1,0,5⟩,[0,0,-64,256,64,-640,896]),(⟨1,0,6⟩,[0,-16,64,-32,-64,560]),(⟨1,1,1⟩,[0,4,-32,112,-224,200,96,-1520,2592,-3276]),(⟨1,1,2⟩,[0,0,-28,168,-268,-48,940,-1336,1596]),(⟨1,1,3⟩,[0,-32,192,-400,320,1088,-2304,3696]),(⟨1,1,4⟩,[-4,24,-28,-48,196,-232,-420]),(⟨1,1,5⟩,[0,48,-192,96,192,-1680]),(⟨1,1,6⟩,[8,-32,48,-32,-504]),(⟨1,2,0⟩,[0,-2,16,-56,112,-100,-48,760,-1296,1638]),(⟨1,2,1⟩,[0,0,-28,168,-268,-48,940,-1336,1596]),(⟨1,2,2⟩,[0,40,-240,584,-736,-1672,4176,-4200]),(⟨1,2,3⟩,[4,-24,92,-208,-260,872,-476]),(⟨1,2,4⟩,[0,-72,288,-48,-480,1848]),(⟨1,2,5⟩,[0,0,64,-128,-448]),(⟨1,2,6⟩,[0,64,-128,-448]),(⟨1,3,0⟩,[0,0,28,-168,268,48,-940,1336,-1596]),(⟨1,3,1⟩,[0,-32,192,-400,320,1088,-2304,3696]),(⟨1,3,2⟩,[4,-24,92,-208,-260,872,-476]),(⟨1,3,3⟩,[0,80,-320,-32,704,-1456]),(⟨1,3,4⟩,[-8,32,-112,160,952]),(⟨1,3,5⟩,[0,-64,128,448]),(⟨1,4,0⟩,[0,12,-72,108,48,-252,216,-1596]),(⟨1,4,1⟩,[-4,24,-28,-48,196,-232,-420]),(⟨1,4,2⟩,[0,-72,288,-48,-480,1848]),(⟨1,4,3⟩,[-8,32,-112,160,952]),(⟨1,5,0⟩,[0,0,-64,256,64,-640,896]),(⟨1,5,1⟩,[0,48,-192,96,192,-1680]),(⟨1,5,2⟩,[0,0,64,-128,-448]),(⟨1,5,3⟩,[0,-64,128,448]),(⟨1,6,0⟩,[0,-16,64,-32,-64,560]),(⟨1,6,1⟩,[8,-32,48,-32,-504]),(⟨1,6,2⟩,[0,64,-128,-448]),(⟨2,0,2⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,0,3⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,0,4⟩,[-4,24,0,-160,108,168,-392]),(⟨2,0,5⟩,[0,8,-32,-80,224,392]),(⟨2,0,6⟩,[4,-16,-40,112,196]),(⟨2,1,1⟩,[-2,16,-32,-32,212,-336,-128,672,-882]),(⟨2,1,2⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,1,3⟩,[4,-24,4,144,-148,-56,588]),(⟨2,2,0⟩,[1,-8,16,16,-106,168,64,-336,441]),(⟨2,2,1⟩,[0,4,-24,4,144,-148,-56,588]),(⟨2,2,2⟩,[0,0,-8,32,80,-224,-392]),(⟨2,2,3⟩,[0,-8,32,80,-224,-392]),(⟨2,3,0⟩,[0,-4,24,-4,-144,148,56,-588]),(⟨2,3,1⟩,[4,-24,4,144,-148,-56,588]),(⟨2,3,2⟩,[0,-8,32,80,-224,-392]),(⟨2,3,3⟩,[-8,32,80,-224,-392]),(⟨2,4,0⟩,[-4,24,0,-160,108,168,-392]),(⟨2,5,0⟩,[0,8,-32,-80,224,392]),(⟨2,6,0⟩,[4,-16,-40,112,196])]


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
    (Poly.add (Poly.scale (K.ofRat r213) (Poly.mul Data.S7_odd.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S7_odd.weightedProduct 0 0).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r434*r434 : ℚ)=r213 := by decide +kernel
  exact Block.sos_scaled_product Data.S7_odd 0 0 r434 r434 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=0 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S7_odd.upperColumn 0 0).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C186

#print axioms Coulomb8.Columns.C186.sound
