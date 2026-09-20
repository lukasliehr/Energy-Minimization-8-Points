import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C060

def r0 : ℚ := { num := -27, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 315, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -1539, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 4023, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -5805, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 3825, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 531, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -2007, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 45, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 81, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -213, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 279, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -3405, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -8283, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 1521, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -1635, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -465, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 39, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -123, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 503, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -703, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 1305, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -3045, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 2001, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1057, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -59, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -15, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 75, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -571, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 279, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -1029, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 831, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1059, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 15, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -139, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 599, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1547, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 2565, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -2729, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 1733, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -497, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 107, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -49, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 881, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -269, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 593, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -93, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -35, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -13, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 9, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -201, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 691, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -1621, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 2697, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -3195, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 2625, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -343, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 343, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -27, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 439, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -555, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 1845, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -507, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 1365, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -441, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 601, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -1569, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 2669, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -2953, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 1971, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -595, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 21, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -33, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 59, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -119, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -119, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 49, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -19, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 227, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -173, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1205, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 485, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 35, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 57, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -259, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 99, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 19, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -27, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 315, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -1539, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 4023, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -5805, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 3825, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 531, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -2007, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 45, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 81, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -213, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 279, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -3405, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -8283, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 1521, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -1635, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -465, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -3, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 39, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -123, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 503, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -703, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 1305, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -3045, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 2001, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -1057, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -59, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -1, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -15, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 75, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -571, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -1029, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 831, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -1059, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 15, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -139, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 599, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -1547, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 2565, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -2729, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1733, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -497, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 3, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 107, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -49, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 881, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -269, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 593, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -93, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -11, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -35, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -13, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -201, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 691, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -1621, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 2697, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -3195, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 2625, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -343, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 343, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -27, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 439, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -555, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 1845, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -507, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 1365, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -441, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 601, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -1569, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 2669, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -2953, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 1971, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -595, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 21, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -33, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 59, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -119, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 49, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 7, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 11, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -13, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -19, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 227, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -173, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1205, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 485, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -21, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 35, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -49, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 57, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -43, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 71, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -259, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 99, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 19, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 1, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9],[0,r10,r11,r12,r13,414,r14,r15,r16,r17,42],[r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36],[r37,r38,r39,r40,r41,r42,r43,r44],[r45,r46,r47,r48,r49,r50,r51],[r34,9,-26,45,r52,20],[r53,0,r54,6,r55],[r56,r54,r57,r58],[r59,2,r60],[],[r61],[],[r62,r63,r64,r65,r66,r67,r68,r69,r70,r71],[r28,r37,r72,r73,r74,r75,r76,r77,r78],[r37,r38,r79,r80,r81,r82,r83,r84],[],[r62,r85,r86,r87,r88,r89],[r90,r46,r91,r54,r92],[],[],[],[],[],[0,0,r93,r94,-13,28,r95,r96],[r45,r97,r98,r99,r100,r31,r101],[],[r102,r103,r104,r105,r106],[0,0,r61,r107],[],[],[],[],[r60,r108,-43,71,r109,r110],[],[r56,r54,r111,r54],[r59,2,r60],[],[],[],[],[],[],[],[],[],[r61],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121]),(⟨0,0,1⟩,[0,r122,r123,r124,r125,207,r126,r127,r128,r129,21]),(⟨0,0,2⟩,[r130,r131,r132,r133,r134,r135,r136,r137,r138,r139]),(⟨0,0,3⟩,[r140,r141,r142,r143,r12,r144,r59,r145,r146]),(⟨0,0,4⟩,[r147,r148,r149,r150,r151,r152,r153,r154]),(⟨0,0,5⟩,[r155,r156,r157,r158,r159,r160,r161]),(⟨0,0,6⟩,[r59,r63,-13,r8,r162,10]),(⟨0,0,7⟩,[r163,0,r164,3,r165]),(⟨0,0,8⟩,[r166,r164,r85,r167]),(⟨0,0,9⟩,[r62,1,r168]),(⟨0,0,11⟩,[r90]),(⟨0,1,0⟩,[0,r122,r123,r124,r125,207,r126,r127,r128,r129,21]),(⟨0,1,1⟩,[r18,r169,r170,r171,r172,r173,r174,r175,r176,r177]),(⟨0,1,2⟩,[r140,r147,r178,r179,r180,r181,r182,r183,r184]),(⟨0,1,3⟩,[r147,r148,r185,r186,r187,r188,r189,r190]),(⟨0,1,5⟩,[r18,r191,r192,r193,r194,r195]),(⟨0,1,6⟩,[r53,r156,r103,r164,r196]),(⟨0,2,0⟩,[r130,r131,r132,r133,r134,r135,r136,r137,r138,r139]),(⟨0,2,1⟩,[r140,r147,r178,r179,r180,r181,r182,r183,r184]),(⟨0,2,2⟩,[0,0,r102,r197,r198,14,r88,r89]),(⟨0,2,3⟩,[r155,r199,r200,r201,r202,r143,r203]),(⟨0,2,5⟩,[r28,r204,r205,r206,r207]),(⟨0,2,6⟩,[0,0,r90,r93]),(⟨0,3,0⟩,[r140,r141,r142,r143,r12,r144,r59,r145,r146]),(⟨0,3,1⟩,[r147,r148,r185,r186,r187,r188,r189,r190]),(⟨0,3,2⟩,[r155,r199,r200,r201,r202,r143,r203]),(⟨0,3,3⟩,[r168,r208,r209,r210,r211,r212]),(⟨0,3,5⟩,[r166,r164,r213,r164]),(⟨0,3,6⟩,[r62,1,r168]),(⟨0,4,0⟩,[r147,r148,r149,r150,r151,r152,r153,r154]),(⟨0,5,0⟩,[r155,r156,r157,r158,r159,r160,r161]),(⟨0,5,1⟩,[r18,r191,r192,r193,r194,r195]),(⟨0,5,2⟩,[r28,r204,r205,r206,r207]),(⟨0,5,3⟩,[r166,r164,r213,r164]),(⟨0,5,6⟩,[r90]),(⟨0,6,0⟩,[r59,r63,-13,r8,r162,10]),(⟨0,6,1⟩,[r53,r156,r103,r164,r196]),(⟨0,6,2⟩,[0,0,r90,r93]),(⟨0,6,3⟩,[r62,1,r168]),(⟨0,6,5⟩,[r90]),(⟨0,7,0⟩,[r163,0,r164,3,r165]),(⟨0,8,0⟩,[r166,r164,r85,r167]),(⟨0,9,0⟩,[r62,1,r168]),(⟨0,11,0⟩,[r90]),(⟨1,0,0⟩,[0,r122,r123,r124,r125,207,r126,r127,r128,r129,21]),(⟨1,0,1⟩,[r18,r169,r170,r171,r172,r173,r174,r175,r176,r177]),(⟨1,0,2⟩,[r140,r147,r178,r179,r180,r181,r182,r183,r184]),(⟨1,0,3⟩,[r147,r148,r185,r186,r187,r188,r189,r190]),(⟨1,0,5⟩,[r18,r191,r192,r193,r194,r195]),(⟨1,0,6⟩,[r53,r156,r103,r164,r196]),(⟨1,1,0⟩,[r18,r169,r170,r171,r172,r173,r174,r175,r176,r177]),(⟨1,2,0⟩,[r140,r147,r178,r179,r180,r181,r182,r183,r184]),(⟨1,3,0⟩,[r147,r148,r185,r186,r187,r188,r189,r190]),(⟨1,5,0⟩,[r18,r191,r192,r193,r194,r195]),(⟨1,6,0⟩,[r53,r156,r103,r164,r196]),(⟨2,0,0⟩,[r130,r131,r132,r133,r134,r135,r136,r137,r138,r139]),(⟨2,0,1⟩,[r140,r147,r178,r179,r180,r181,r182,r183,r184]),(⟨2,0,2⟩,[0,0,r102,r197,r198,14,r88,r89]),(⟨2,0,3⟩,[r155,r199,r200,r201,r202,r143,r203]),(⟨2,0,5⟩,[r28,r204,r205,r206,r207]),(⟨2,0,6⟩,[0,0,r90,r93]),(⟨2,1,0⟩,[r140,r147,r178,r179,r180,r181,r182,r183,r184]),(⟨2,2,0⟩,[0,0,r102,r197,r198,14,r88,r89]),(⟨2,3,0⟩,[r155,r199,r200,r201,r202,r143,r203]),(⟨2,5,0⟩,[r28,r204,r205,r206,r207]),(⟨2,6,0⟩,[0,0,r90,r93]),(⟨3,0,0⟩,[r140,r141,r142,r143,r12,r144,r59,r145,r146]),(⟨3,0,1⟩,[r147,r148,r185,r186,r187,r188,r189,r190]),(⟨3,0,2⟩,[r155,r199,r200,r201,r202,r143,r203]),(⟨3,0,3⟩,[r168,r208,r209,r210,r211,r212]),(⟨3,0,5⟩,[r166,r164,r213,r164]),(⟨3,0,6⟩,[r62,1,r168]),(⟨3,1,0⟩,[r147,r148,r185,r186,r187,r188,r189,r190]),(⟨3,2,0⟩,[r155,r199,r200,r201,r202,r143,r203]),(⟨3,3,0⟩,[r168,r208,r209,r210,r211,r212]),(⟨3,5,0⟩,[r166,r164,r213,r164]),(⟨3,6,0⟩,[r62,1,r168]),(⟨4,0,0⟩,[r147,r148,r149,r150,r151,r152,r153,r154]),(⟨5,0,0⟩,[r155,r156,r157,r158,r159,r160,r161]),(⟨5,0,1⟩,[r18,r191,r192,r193,r194,r195]),(⟨5,0,2⟩,[r28,r204,r205,r206,r207]),(⟨5,0,3⟩,[r166,r164,r213,r164]),(⟨5,0,6⟩,[r90]),(⟨5,1,0⟩,[r18,r191,r192,r193,r194,r195]),(⟨5,2,0⟩,[r28,r204,r205,r206,r207]),(⟨5,3,0⟩,[r166,r164,r213,r164]),(⟨5,6,0⟩,[r90]),(⟨6,0,0⟩,[r59,r63,-13,r8,r162,10]),(⟨6,0,1⟩,[r53,r156,r103,r164,r196]),(⟨6,0,2⟩,[0,0,r90,r93]),(⟨6,0,3⟩,[r62,1,r168]),(⟨6,0,5⟩,[r90]),(⟨6,1,0⟩,[r53,r156,r103,r164,r196]),(⟨6,2,0⟩,[0,0,r90,r93]),(⟨6,3,0⟩,[r62,1,r168]),(⟨6,5,0⟩,[r90]),(⟨7,0,0⟩,[r163,0,r164,3,r165]),(⟨8,0,0⟩,[r166,r164,r85,r167]),(⟨9,0,0⟩,[r62,1,r168]),(⟨11,0,0⟩,[r90])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r90) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r53) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[0,18,-120,300,-324,66,108]),(⟨5,0,1⟩,[-6,42,-132,236,-238,98]),(⟨5,0,2⟩,[-2,20,-84,140,-98]),(⟨5,0,3⟩,[12,-44,76,-44]),(⟨5,0,6⟩,[8]),(⟨5,1,0⟩,[-6,42,-132,236,-238,98]),(⟨5,2,0⟩,[-2,20,-84,140,-98]),(⟨5,3,0⟩,[12,-44,76,-44]),(⟨5,6,0⟩,[8]),(⟨6,0,0⟩,[-6,42,-132,236,-238,98]),(⟨7,0,0⟩,[-2,20,-84,140,-98]),(⟨8,0,0⟩,[12,-44,76,-44]),(⟨11,0,0⟩,[8])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[0,18,-120,300,-324,66,108]),(⟨0,5,1⟩,[-6,42,-132,236,-238,98]),(⟨0,5,2⟩,[-2,20,-84,140,-98]),(⟨0,5,3⟩,[12,-44,76,-44]),(⟨0,5,6⟩,[8]),(⟨0,6,0⟩,[-6,42,-132,236,-238,98]),(⟨0,7,0⟩,[-2,20,-84,140,-98]),(⟨0,8,0⟩,[12,-44,76,-44]),(⟨0,11,0⟩,[8]),(⟨1,0,0⟩,[0,9,-105,540,-1611,3066,-3801,2892,-957,-363,378]),(⟨1,0,1⟩,[-3,36,-201,691,-1621,2697,-3195,2625,-1372,343]),(⟨1,0,2⟩,[-1,15,-102,391,-936,1477,-1554,1029,-343]),(⟨1,0,3⟩,[6,-52,208,-498,774,-792,508,-154]),(⟨1,0,6⟩,[4,-20,40,-44,28]),(⟨1,1,0⟩,[-3,36,-201,691,-1621,2697,-3195,2625,-1372,343]),(⟨1,2,0⟩,[-1,15,-102,391,-936,1477,-1554,1029,-343]),(⟨1,3,0⟩,[6,-52,208,-498,774,-792,508,-154]),(⟨1,5,0⟩,[-6,42,-132,236,-238,98]),(⟨1,6,0⟩,[4,-20,40,-44,28]),(⟨2,0,0⟩,[-3,36,-201,709,-1759,3117,-3819,3015,-1330,235]),(⟨2,0,1⟩,[0,0,-6,48,-174,368,-474,336,-98]),(⟨2,0,2⟩,[0,0,-2,22,-104,224,-238,98]),(⟨2,0,3⟩,[0,0,12,-56,120,-120,44]),(⟨2,0,6⟩,[0,0,8,-8]),(⟨2,1,0⟩,[0,0,-6,48,-174,368,-474,336,-98]),(⟨2,2,0⟩,[0,0,-2,22,-104,224,-238,98]),(⟨2,3,0⟩,[0,0,12,-56,120,-120,44]),(⟨2,5,0⟩,[-2,20,-84,140,-98]),(⟨2,6,0⟩,[0,0,8,-8]),(⟨3,0,0⟩,[-1,-12,144,-572,1116,-900,-468,1500,-927]),(⟨3,0,1⟩,[9,-87,393,-1071,1895,-2161,1463,-441]),(⟨3,0,2⟩,[3,-38,215,-636,1085,-1022,441]),(⟨3,0,3⟩,[-18,114,-344,568,-518,198]),(⟨3,0,6⟩,[-12,32,-36]),(⟨3,1,0⟩,[9,-87,393,-1071,1895,-2161,1463,-441]),(⟨3,2,0⟩,[3,-38,215,-636,1085,-1022,441]),(⟨3,3,0⟩,[-18,114,-344,568,-518,198]),(⟨3,5,0⟩,[12,-44,76,-44]),(⟨3,6,0⟩,[-12,32,-36]),(⟨4,0,0⟩,[15,-139,599,-1547,2565,-2729,1733,-497]),(⟨5,0,0⟩,[3,-20,107,-392,881,-1076,593]),(⟨5,0,1⟩,[-6,42,-132,236,-238,98]),(⟨5,0,2⟩,[-2,20,-84,140,-98]),(⟨5,0,3⟩,[12,-44,76,-44]),(⟨5,0,6⟩,[8]),(⟨5,1,0⟩,[-6,42,-132,236,-238,98]),(⟨5,2,0⟩,[-2,20,-84,140,-98]),(⟨5,3,0⟩,[12,-44,76,-44]),(⟨5,6,0⟩,[8]),(⟨6,0,0⟩,[-24,156,-476,804,-756,296]),(⟨6,5,0⟩,[8]),(⟨7,0,0⟩,[2,0,-44,96,-70]),(⟨8,0,0⟩,[12,-44,84,-52]),(⟨9,0,0⟩,[-12,32,-36]),(⟨11,0,0⟩,[8])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[0,18,-120,300,-324,66,108]),(⟨0,0,6⟩,[-6,42,-132,236,-238,98]),(⟨0,0,7⟩,[-2,20,-84,140,-98]),(⟨0,0,8⟩,[12,-44,76,-44]),(⟨0,0,11⟩,[8]),(⟨0,1,0⟩,[0,9,-105,540,-1611,3066,-3801,2892,-957,-363,378]),(⟨0,1,1⟩,[-3,36,-201,691,-1621,2697,-3195,2625,-1372,343]),(⟨0,1,2⟩,[-1,15,-102,391,-936,1477,-1554,1029,-343]),(⟨0,1,3⟩,[6,-52,208,-498,774,-792,508,-154]),(⟨0,1,5⟩,[-6,42,-132,236,-238,98]),(⟨0,1,6⟩,[4,-20,40,-44,28]),(⟨0,2,0⟩,[-3,36,-201,709,-1759,3117,-3819,3015,-1330,235]),(⟨0,2,1⟩,[0,0,-6,48,-174,368,-474,336,-98]),(⟨0,2,2⟩,[0,0,-2,22,-104,224,-238,98]),(⟨0,2,3⟩,[0,0,12,-56,120,-120,44]),(⟨0,2,5⟩,[-2,20,-84,140,-98]),(⟨0,2,6⟩,[0,0,8,-8]),(⟨0,3,0⟩,[-1,-12,144,-572,1116,-900,-468,1500,-927]),(⟨0,3,1⟩,[9,-87,393,-1071,1895,-2161,1463,-441]),(⟨0,3,2⟩,[3,-38,215,-636,1085,-1022,441]),(⟨0,3,3⟩,[-18,114,-344,568,-518,198]),(⟨0,3,5⟩,[12,-44,76,-44]),(⟨0,3,6⟩,[-12,32,-36]),(⟨0,4,0⟩,[15,-139,599,-1547,2565,-2729,1733,-497]),(⟨0,5,0⟩,[3,-20,107,-392,881,-1076,593]),(⟨0,5,1⟩,[-6,42,-132,236,-238,98]),(⟨0,5,2⟩,[-2,20,-84,140,-98]),(⟨0,5,3⟩,[12,-44,76,-44]),(⟨0,5,6⟩,[8]),(⟨0,6,0⟩,[-24,156,-476,804,-756,296]),(⟨0,6,5⟩,[8]),(⟨0,7,0⟩,[2,0,-44,96,-70]),(⟨0,8,0⟩,[12,-44,84,-52]),(⟨0,9,0⟩,[-12,32,-36]),(⟨0,11,0⟩,[8]),(⟨1,0,0⟩,[0,9,-105,540,-1611,3066,-3801,2892,-957,-363,378]),(⟨1,0,1⟩,[-3,36,-201,691,-1621,2697,-3195,2625,-1372,343]),(⟨1,0,2⟩,[-1,15,-102,391,-936,1477,-1554,1029,-343]),(⟨1,0,3⟩,[6,-52,208,-498,774,-792,508,-154]),(⟨1,0,5⟩,[-6,42,-132,236,-238,98]),(⟨1,0,6⟩,[4,-20,40,-44,28]),(⟨1,1,0⟩,[-6,72,-402,1382,-3242,5394,-6390,5250,-2744,686]),(⟨1,2,0⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨1,3,0⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨1,5,0⟩,[-6,42,-132,236,-238,98]),(⟨1,6,0⟩,[4,-20,40,-44,28]),(⟨2,0,0⟩,[-3,36,-201,709,-1759,3117,-3819,3015,-1330,235]),(⟨2,0,1⟩,[0,0,-6,48,-174,368,-474,336,-98]),(⟨2,0,2⟩,[0,0,-2,22,-104,224,-238,98]),(⟨2,0,3⟩,[0,0,12,-56,120,-120,44]),(⟨2,0,5⟩,[-2,20,-84,140,-98]),(⟨2,0,6⟩,[0,0,8,-8]),(⟨2,1,0⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨2,2,0⟩,[0,0,-4,44,-208,448,-476,196]),(⟨2,3,0⟩,[3,-38,227,-692,1205,-1142,485]),(⟨2,5,0⟩,[-2,20,-84,140,-98]),(⟨2,6,0⟩,[0,0,8,-8]),(⟨3,0,0⟩,[-1,-12,144,-572,1116,-900,-468,1500,-927]),(⟨3,0,1⟩,[9,-87,393,-1071,1895,-2161,1463,-441]),(⟨3,0,2⟩,[3,-38,215,-636,1085,-1022,441]),(⟨3,0,3⟩,[-18,114,-344,568,-518,198]),(⟨3,0,5⟩,[12,-44,76,-44]),(⟨3,0,6⟩,[-12,32,-36]),(⟨3,1,0⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨3,2,0⟩,[3,-38,227,-692,1205,-1142,485]),(⟨3,3,0⟩,[-36,228,-688,1136,-1036,396]),(⟨3,5,0⟩,[12,-44,76,-44]),(⟨3,6,0⟩,[-12,32,-36]),(⟨4,0,0⟩,[15,-139,599,-1547,2565,-2729,1733,-497]),(⟨5,0,0⟩,[3,-20,107,-392,881,-1076,593]),(⟨5,0,1⟩,[-6,42,-132,236,-238,98]),(⟨5,0,2⟩,[-2,20,-84,140,-98]),(⟨5,0,3⟩,[12,-44,76,-44]),(⟨5,0,6⟩,[8]),(⟨5,1,0⟩,[-6,42,-132,236,-238,98]),(⟨5,2,0⟩,[-2,20,-84,140,-98]),(⟨5,3,0⟩,[12,-44,76,-44]),(⟨5,6,0⟩,[8]),(⟨6,0,0⟩,[-24,156,-476,804,-756,296]),(⟨6,0,5⟩,[8]),(⟨6,1,0⟩,[4,-20,40,-44,28]),(⟨6,2,0⟩,[0,0,8,-8]),(⟨6,3,0⟩,[-12,32,-36]),(⟨6,5,0⟩,[8]),(⟨7,0,0⟩,[2,0,-44,96,-70]),(⟨8,0,0⟩,[12,-44,84,-52]),(⟨9,0,0⟩,[-12,32,-36]),(⟨11,0,0⟩,[8])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,-27,315,-1539,4023,-5805,3825,531,-2007,360,324]),(⟨0,0,1⟩,[0,18,-213,1116,-3405,6624,-8283,6084,-1635,-930,672]),(⟨0,0,2⟩,[-3,39,-246,1006,-2812,5220,-6090,4002,-1057,-59]),(⟨0,0,3⟩,[-1,-30,300,-1142,2232,-2058,-24,1662,-1059]),(⟨0,0,4⟩,[15,-139,599,-1547,2565,-2729,1733,-497]),(⟨0,0,5⟩,[3,-20,107,-392,881,-1076,593]),(⟨0,0,6⟩,[-24,144,-416,720,-744,320]),(⟨0,0,7⟩,[2,0,-44,96,-70]),(⟨0,0,8⟩,[12,-44,84,-52]),(⟨0,0,9⟩,[-12,32,-36]),(⟨0,0,11⟩,[8]),(⟨0,1,0⟩,[0,18,-213,1116,-3405,6624,-8283,6084,-1635,-930,672]),(⟨0,1,1⟩,[-6,72,-402,1382,-3242,5394,-6390,5250,-2744,686]),(⟨0,1,2⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨0,1,3⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨0,1,5⟩,[-6,42,-132,236,-238,98]),(⟨0,1,6⟩,[4,-20,40,-44,28]),(⟨0,2,0⟩,[-3,39,-246,1006,-2812,5220,-6090,4002,-1057,-59]),(⟨0,2,1⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨0,2,2⟩,[0,0,-4,44,-208,448,-476,196]),(⟨0,2,3⟩,[3,-38,227,-692,1205,-1142,485]),(⟨0,2,5⟩,[-2,20,-84,140,-98]),(⟨0,2,6⟩,[0,0,8,-8]),(⟨0,3,0⟩,[-1,-30,300,-1142,2232,-2058,-24,1662,-1059]),(⟨0,3,1⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨0,3,2⟩,[3,-38,227,-692,1205,-1142,485]),(⟨0,3,3⟩,[-36,228,-688,1136,-1036,396]),(⟨0,3,5⟩,[12,-44,76,-44]),(⟨0,3,6⟩,[-12,32,-36]),(⟨0,4,0⟩,[15,-139,599,-1547,2565,-2729,1733,-497]),(⟨0,5,0⟩,[3,-20,107,-392,881,-1076,593]),(⟨0,5,1⟩,[-6,42,-132,236,-238,98]),(⟨0,5,2⟩,[-2,20,-84,140,-98]),(⟨0,5,3⟩,[12,-44,76,-44]),(⟨0,5,6⟩,[8]),(⟨0,6,0⟩,[-24,144,-416,720,-744,320]),(⟨0,6,1⟩,[4,-20,40,-44,28]),(⟨0,6,2⟩,[0,0,8,-8]),(⟨0,6,3⟩,[-12,32,-36]),(⟨0,6,5⟩,[8]),(⟨0,7,0⟩,[2,0,-44,96,-70]),(⟨0,8,0⟩,[12,-44,84,-52]),(⟨0,9,0⟩,[-12,32,-36]),(⟨0,11,0⟩,[8]),(⟨1,0,0⟩,[0,18,-213,1116,-3405,6624,-8283,6084,-1635,-930,672]),(⟨1,0,1⟩,[-6,72,-402,1382,-3242,5394,-6390,5250,-2744,686]),(⟨1,0,2⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨1,0,3⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨1,0,5⟩,[-6,42,-132,236,-238,98]),(⟨1,0,6⟩,[4,-20,40,-44,28]),(⟨1,1,0⟩,[-6,72,-402,1382,-3242,5394,-6390,5250,-2744,686]),(⟨1,2,0⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨1,3,0⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨1,5,0⟩,[-6,42,-132,236,-238,98]),(⟨1,6,0⟩,[4,-20,40,-44,28]),(⟨2,0,0⟩,[-3,39,-246,1006,-2812,5220,-6090,4002,-1057,-59]),(⟨2,0,1⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨2,0,2⟩,[0,0,-4,44,-208,448,-476,196]),(⟨2,0,3⟩,[3,-38,227,-692,1205,-1142,485]),(⟨2,0,5⟩,[-2,20,-84,140,-98]),(⟨2,0,6⟩,[0,0,8,-8]),(⟨2,1,0⟩,[-1,15,-108,439,-1110,1845,-2028,1365,-441]),(⟨2,2,0⟩,[0,0,-4,44,-208,448,-476,196]),(⟨2,3,0⟩,[3,-38,227,-692,1205,-1142,485]),(⟨2,5,0⟩,[-2,20,-84,140,-98]),(⟨2,6,0⟩,[0,0,8,-8]),(⟨3,0,0⟩,[-1,-30,300,-1142,2232,-2058,-24,1662,-1059]),(⟨3,0,1⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨3,0,2⟩,[3,-38,227,-692,1205,-1142,485]),(⟨3,0,3⟩,[-36,228,-688,1136,-1036,396]),(⟨3,0,5⟩,[12,-44,76,-44]),(⟨3,0,6⟩,[-12,32,-36]),(⟨3,1,0⟩,[15,-139,601,-1569,2669,-2953,1971,-595]),(⟨3,2,0⟩,[3,-38,227,-692,1205,-1142,485]),(⟨3,3,0⟩,[-36,228,-688,1136,-1036,396]),(⟨3,5,0⟩,[12,-44,76,-44]),(⟨3,6,0⟩,[-12,32,-36]),(⟨4,0,0⟩,[15,-139,599,-1547,2565,-2729,1733,-497]),(⟨5,0,0⟩,[3,-20,107,-392,881,-1076,593]),(⟨5,0,1⟩,[-6,42,-132,236,-238,98]),(⟨5,0,2⟩,[-2,20,-84,140,-98]),(⟨5,0,3⟩,[12,-44,76,-44]),(⟨5,0,6⟩,[8]),(⟨5,1,0⟩,[-6,42,-132,236,-238,98]),(⟨5,2,0⟩,[-2,20,-84,140,-98]),(⟨5,3,0⟩,[12,-44,76,-44]),(⟨5,6,0⟩,[8]),(⟨6,0,0⟩,[-24,144,-416,720,-744,320]),(⟨6,0,1⟩,[4,-20,40,-44,28]),(⟨6,0,2⟩,[0,0,8,-8]),(⟨6,0,3⟩,[-12,32,-36]),(⟨6,0,5⟩,[8]),(⟨6,1,0⟩,[4,-20,40,-44,28]),(⟨6,2,0⟩,[0,0,8,-8]),(⟨6,3,0⟩,[-12,32,-36]),(⟨6,5,0⟩,[8]),(⟨7,0,0⟩,[2,0,-44,96,-70]),(⟨8,0,0⟩,[12,-44,84,-52]),(⟨9,0,0⟩,[-12,32,-36]),(⟨11,0,0⟩,[8])]


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
    (Poly.add (Poly.scale (K.ofRat r214) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 2).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r90*r53 : ℚ)=r214 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 2 r90 r53 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=2 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 2).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C060

#print axioms Coulomb8.Columns.C060.sound
