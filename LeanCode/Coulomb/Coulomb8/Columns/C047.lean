import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C047

def r0 : ℚ := { num := 27, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 1251, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -693, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 3033, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -99, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -1323, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 171, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 81, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 51, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 1407, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -2367, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -447, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -297, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 141, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 847, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 1021, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -427, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -13, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 143, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -393, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 473, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -207, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -11, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 13, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -407, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -737, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 243, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -7, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 55, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -101, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 197, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -415, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 175, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 7, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -15, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -9, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 99, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -163, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -509, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 953, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -259, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 245, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -113, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 235, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -609, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 455, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -147, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 25, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -47, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 101, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -259, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 181, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 21, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -33, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 59, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -119, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 89, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -77, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 623, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -343, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 343, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 17, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 69, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 63, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 35, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 11, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 19, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 27, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 1251, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -693, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 3033, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -99, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -1323, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 171, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 81, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 51, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -63, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1407, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -2367, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 285, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -447, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -297, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 141, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 3, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 21, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -85, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 847, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -317, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 1021, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -67, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -427, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -13, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 143, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -393, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 473, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -207, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -11, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 13, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -407, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -737, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 243, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -7, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 55, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -101, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 197, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -415, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 175, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 5, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -15, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 99, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -163, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -509, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 953, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 245, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 17, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -113, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 235, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -609, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 455, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -147, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 25, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -47, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 101, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -259, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 181, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -13, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 21, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -33, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 59, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -119, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 49, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 89, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -77, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 623, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -343, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 343, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 17, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -17, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 69, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -37, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 63, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -21, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 35, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -49, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -7, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 15, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -15, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -11, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 19, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 1, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,-18,r1,r2,r3,r4,r5,r6,r7],[0,r8,r9,-63,r10,r11,285,r12,r13,r14],[r15,-3,21,-85,r16,-317,r17,-67,r18],[r19,r20,r21,r22,r23,r24,r25,r26],[r27,r28,r29,50,r30,r28,r31],[r32,r33,r34,r35,r36,r37],[r38,r39,r20,r40,r41],[r42,r39,r43,r39],[r21,1,r44],[r42,r45],[r42],[],[],[r46,r47,r48,r49,176,r50,r51,r52,r53],[r19,-3,17,r54,r55,r56,r57,r58],[r20,r59,r60,r61,r62,r63,-13],[r64,r65,r66,r67,r68,r69],[],[r21,r70,r71,r70],[],[],[],[],[],[r72,r44,r73,r74,r75,r76,r77],[r45,r78,-17,r79,-37,r80],[r81,r70,r82,r83,r84],[],[r21,1,r44],[],[],[],[],[r85,-7,15,-15,r86],[r87,r88,r89,r88],[],[r42,r45],[],[],[],[],[],[r42],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r90,-9,r91,r92,r93,r94,r95,r96,r97]),(⟨0,0,1⟩,[0,r98,r99,r100,r101,r102,r103,r104,r105,r106]),(⟨0,0,2⟩,[r107,r39,r108,r109,r110,r111,r112,r113,r114]),(⟨0,0,3⟩,[r72,r64,r81,r115,r116,r117,r118,r119]),(⟨0,0,4⟩,[r120,r121,r122,25,r123,r121,r124]),(⟨0,0,5⟩,[r125,r126,r127,r128,r129,r130]),(⟨0,0,6⟩,[r131,r20,r64,r132,r133]),(⟨0,0,7⟩,[r19,r20,r70,r20]),(⟨0,0,8⟩,[r81,r42,r32]),(⟨0,0,9⟩,[r19,r21]),(⟨0,0,10⟩,[r19]),(⟨0,1,0⟩,[0,r98,r99,r100,r101,r102,r103,r104,r105,r106]),(⟨0,1,1⟩,[r15,r71,r134,r135,88,r136,r137,r62,r138]),(⟨0,1,2⟩,[r72,r39,r139,r140,r141,r142,r143,r144]),(⟨0,1,3⟩,[r64,r145,r146,r147,r148,r149,r150]),(⟨0,1,4⟩,[r151,r152,r153,r154,r155,r156]),(⟨0,1,6⟩,[r81,r38,r8,r38]),(⟨0,2,0⟩,[r107,r39,r108,r109,r110,r111,r112,r113,r114]),(⟨0,2,1⟩,[r72,r39,r139,r140,r141,r142,r143,r144]),(⟨0,2,2⟩,[r157,r32,r158,r159,r160,r161,r162]),(⟨0,2,3⟩,[r21,r163,r164,r165,r166,r167]),(⟨0,2,4⟩,[r168,r38,r169,r170,r171]),(⟨0,2,6⟩,[r81,r42,r32]),(⟨0,3,0⟩,[r72,r64,r81,r115,r116,r117,r118,r119]),(⟨0,3,1⟩,[r64,r145,r146,r147,r148,r149,r150]),(⟨0,3,2⟩,[r21,r163,r164,r165,r166,r167]),(⟨0,3,3⟩,[r87,r172,r173,r174,r175]),(⟨0,3,4⟩,[r46,r176,r177,r176]),(⟨0,3,6⟩,[r19,r21]),(⟨0,4,0⟩,[r120,r121,r122,25,r123,r121,r124]),(⟨0,4,1⟩,[r151,r152,r153,r154,r155,r156]),(⟨0,4,2⟩,[r168,r38,r169,r170,r171]),(⟨0,4,3⟩,[r46,r176,r177,r176]),(⟨0,4,6⟩,[r19]),(⟨0,5,0⟩,[r125,r126,r127,r128,r129,r130]),(⟨0,6,0⟩,[r131,r20,r64,r132,r133]),(⟨0,6,1⟩,[r81,r38,r8,r38]),(⟨0,6,2⟩,[r81,r42,r32]),(⟨0,6,3⟩,[r19,r21]),(⟨0,6,4⟩,[r19]),(⟨0,7,0⟩,[r19,r20,r70,r20]),(⟨0,8,0⟩,[r81,r42,r32]),(⟨0,9,0⟩,[r19,r21]),(⟨0,10,0⟩,[r19]),(⟨1,0,0⟩,[0,r98,r99,r100,r101,r102,r103,r104,r105,r106]),(⟨1,0,1⟩,[r15,r71,r134,r135,88,r136,r137,r62,r138]),(⟨1,0,2⟩,[r72,r39,r139,r140,r141,r142,r143,r144]),(⟨1,0,3⟩,[r64,r145,r146,r147,r148,r149,r150]),(⟨1,0,4⟩,[r151,r152,r153,r154,r155,r156]),(⟨1,0,6⟩,[r81,r38,r8,r38]),(⟨1,1,0⟩,[r15,r71,r134,r135,88,r136,r137,r62,r138]),(⟨1,2,0⟩,[r72,r39,r139,r140,r141,r142,r143,r144]),(⟨1,3,0⟩,[r64,r145,r146,r147,r148,r149,r150]),(⟨1,4,0⟩,[r151,r152,r153,r154,r155,r156]),(⟨1,6,0⟩,[r81,r38,r8,r38]),(⟨2,0,0⟩,[r107,r39,r108,r109,r110,r111,r112,r113,r114]),(⟨2,0,1⟩,[r72,r39,r139,r140,r141,r142,r143,r144]),(⟨2,0,2⟩,[r157,r32,r158,r159,r160,r161,r162]),(⟨2,0,3⟩,[r21,r163,r164,r165,r166,r167]),(⟨2,0,4⟩,[r168,r38,r169,r170,r171]),(⟨2,0,6⟩,[r81,r42,r32]),(⟨2,1,0⟩,[r72,r39,r139,r140,r141,r142,r143,r144]),(⟨2,2,0⟩,[r157,r32,r158,r159,r160,r161,r162]),(⟨2,3,0⟩,[r21,r163,r164,r165,r166,r167]),(⟨2,4,0⟩,[r168,r38,r169,r170,r171]),(⟨2,6,0⟩,[r81,r42,r32]),(⟨3,0,0⟩,[r72,r64,r81,r115,r116,r117,r118,r119]),(⟨3,0,1⟩,[r64,r145,r146,r147,r148,r149,r150]),(⟨3,0,2⟩,[r21,r163,r164,r165,r166,r167]),(⟨3,0,3⟩,[r87,r172,r173,r174,r175]),(⟨3,0,4⟩,[r46,r176,r177,r176]),(⟨3,0,6⟩,[r19,r21]),(⟨3,1,0⟩,[r64,r145,r146,r147,r148,r149,r150]),(⟨3,2,0⟩,[r21,r163,r164,r165,r166,r167]),(⟨3,3,0⟩,[r87,r172,r173,r174,r175]),(⟨3,4,0⟩,[r46,r176,r177,r176]),(⟨3,6,0⟩,[r19,r21]),(⟨4,0,0⟩,[r120,r121,r122,25,r123,r121,r124]),(⟨4,0,1⟩,[r151,r152,r153,r154,r155,r156]),(⟨4,0,2⟩,[r168,r38,r169,r170,r171]),(⟨4,0,3⟩,[r46,r176,r177,r176]),(⟨4,0,6⟩,[r19]),(⟨4,1,0⟩,[r151,r152,r153,r154,r155,r156]),(⟨4,2,0⟩,[r168,r38,r169,r170,r171]),(⟨4,3,0⟩,[r46,r176,r177,r176]),(⟨4,6,0⟩,[r19]),(⟨5,0,0⟩,[r125,r126,r127,r128,r129,r130]),(⟨6,0,0⟩,[r131,r20,r64,r132,r133]),(⟨6,0,1⟩,[r81,r38,r8,r38]),(⟨6,0,2⟩,[r81,r42,r32]),(⟨6,0,3⟩,[r19,r21]),(⟨6,0,4⟩,[r19]),(⟨6,1,0⟩,[r81,r38,r8,r38]),(⟨6,2,0⟩,[r81,r42,r32]),(⟨6,3,0⟩,[r19,r21]),(⟨6,4,0⟩,[r19]),(⟨7,0,0⟩,[r19,r20,r70,r20]),(⟨8,0,0⟩,[r81,r42,r32]),(⟨9,0,0⟩,[r19,r21]),(⟨10,0,0⟩,[r19])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r19) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r72) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[0,18,-120,300,-324,66,108]),(⟨4,0,1⟩,[-6,42,-132,236,-238,98]),(⟨4,0,2⟩,[-2,20,-84,140,-98]),(⟨4,0,3⟩,[12,-44,76,-44]),(⟨4,0,6⟩,[8]),(⟨4,1,0⟩,[-6,42,-132,236,-238,98]),(⟨4,2,0⟩,[-2,20,-84,140,-98]),(⟨4,3,0⟩,[12,-44,76,-44]),(⟨4,6,0⟩,[8]),(⟨5,0,0⟩,[-6,42,-132,236,-238,98]),(⟨6,0,0⟩,[-2,20,-84,140,-98]),(⟨7,0,0⟩,[12,-44,76,-44]),(⟨10,0,0⟩,[8])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[0,18,-120,300,-324,66,108]),(⟨0,4,1⟩,[-6,42,-132,236,-238,98]),(⟨0,4,2⟩,[-2,20,-84,140,-98]),(⟨0,4,3⟩,[12,-44,76,-44]),(⟨0,4,6⟩,[8]),(⟨0,5,0⟩,[-6,42,-132,236,-238,98]),(⟨0,6,0⟩,[-2,20,-84,140,-98]),(⟨0,7,0⟩,[12,-44,76,-44]),(⟨0,10,0⟩,[8]),(⟨1,0,0⟩,[0,-9,105,-531,1497,-2493,2319,-837,-321,270]),(⟨1,0,1⟩,[3,-36,198,-652,1408,-2036,1906,-1036,245]),(⟨1,0,2⟩,[1,-15,101,-375,827,-1085,791,-245]),(⟨1,0,3⟩,[-6,52,-202,440,-562,388,-110]),(⟨1,0,6⟩,[-4,20,-36,20]),(⟨1,1,0⟩,[3,-36,198,-652,1408,-2036,1906,-1036,245]),(⟨1,2,0⟩,[1,-15,101,-375,827,-1085,791,-245]),(⟨1,3,0⟩,[-6,52,-202,440,-562,388,-110]),(⟨1,4,0⟩,[-6,42,-132,236,-238,98]),(⟨1,6,0⟩,[-4,20,-36,20]),(⟨2,0,0⟩,[3,-45,294,-1105,2590,-3767,3118,-1051,-133]),(⟨2,0,1⟩,[3,-33,171,-529,1053,-1351,1029,-343]),(⟨2,0,2⟩,[1,-14,89,-308,623,-686,343]),(⟨2,0,3⟩,[-6,46,-168,328,-354,154]),(⟨2,0,6⟩,[-4,16,-28]),(⟨2,1,0⟩,[3,-33,171,-529,1053,-1351,1029,-343]),(⟨2,2,0⟩,[1,-14,89,-308,623,-686,343]),(⟨2,3,0⟩,[-6,46,-168,328,-354,154]),(⟨2,4,0⟩,[-2,20,-84,140,-98]),(⟨2,6,0⟩,[-4,16,-28]),(⟨3,0,0⟩,[4,-30,134,-484,1256,-2046,1862,-696]),(⟨3,0,1⟩,[-6,48,-174,368,-474,336,-98]),(⟨3,0,2⟩,[-2,22,-104,224,-238,98]),(⟨3,0,3⟩,[12,-56,120,-120,44]),(⟨3,0,6⟩,[8,-8]),(⟨3,1,0⟩,[-6,48,-174,368,-474,336,-98]),(⟨3,2,0⟩,[-2,22,-104,224,-238,98]),(⟨3,3,0⟩,[12,-56,120,-120,44]),(⟨3,4,0⟩,[12,-44,76,-44]),(⟨3,6,0⟩,[8,-8]),(⟨4,0,0⟩,[-11,104,-407,800,-737,104,243]),(⟨4,0,1⟩,[-6,42,-132,236,-238,98]),(⟨4,0,2⟩,[-2,20,-84,140,-98]),(⟨4,0,3⟩,[12,-44,76,-44]),(⟨4,0,6⟩,[8]),(⟨4,1,0⟩,[-6,42,-132,236,-238,98]),(⟨4,2,0⟩,[-2,20,-84,140,-98]),(⟨4,3,0⟩,[12,-44,76,-44]),(⟨4,6,0⟩,[8]),(⟨5,0,0⟩,[-14,110,-404,788,-830,350]),(⟨6,0,0⟩,[10,-36,36,20,-54]),(⟨6,4,0⟩,[8]),(⟨7,0,0⟩,[8,-24,40,-24]),(⟨8,0,0⟩,[-4,16,-28]),(⟨9,0,0⟩,[8,-8]),(⟨10,0,0⟩,[8])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[0,18,-120,300,-324,66,108]),(⟨0,0,5⟩,[-6,42,-132,236,-238,98]),(⟨0,0,6⟩,[-2,20,-84,140,-98]),(⟨0,0,7⟩,[12,-44,76,-44]),(⟨0,0,10⟩,[8]),(⟨0,1,0⟩,[0,-9,105,-531,1497,-2493,2319,-837,-321,270]),(⟨0,1,1⟩,[3,-36,198,-652,1408,-2036,1906,-1036,245]),(⟨0,1,2⟩,[1,-15,101,-375,827,-1085,791,-245]),(⟨0,1,3⟩,[-6,52,-202,440,-562,388,-110]),(⟨0,1,4⟩,[-6,42,-132,236,-238,98]),(⟨0,1,6⟩,[-4,20,-36,20]),(⟨0,2,0⟩,[3,-45,294,-1105,2590,-3767,3118,-1051,-133]),(⟨0,2,1⟩,[3,-33,171,-529,1053,-1351,1029,-343]),(⟨0,2,2⟩,[1,-14,89,-308,623,-686,343]),(⟨0,2,3⟩,[-6,46,-168,328,-354,154]),(⟨0,2,4⟩,[-2,20,-84,140,-98]),(⟨0,2,6⟩,[-4,16,-28]),(⟨0,3,0⟩,[4,-30,134,-484,1256,-2046,1862,-696]),(⟨0,3,1⟩,[-6,48,-174,368,-474,336,-98]),(⟨0,3,2⟩,[-2,22,-104,224,-238,98]),(⟨0,3,3⟩,[12,-56,120,-120,44]),(⟨0,3,4⟩,[12,-44,76,-44]),(⟨0,3,6⟩,[8,-8]),(⟨0,4,0⟩,[-11,104,-407,800,-737,104,243]),(⟨0,4,1⟩,[-6,42,-132,236,-238,98]),(⟨0,4,2⟩,[-2,20,-84,140,-98]),(⟨0,4,3⟩,[12,-44,76,-44]),(⟨0,4,6⟩,[8]),(⟨0,5,0⟩,[-14,110,-404,788,-830,350]),(⟨0,6,0⟩,[10,-36,36,20,-54]),(⟨0,6,4⟩,[8]),(⟨0,7,0⟩,[8,-24,40,-24]),(⟨0,8,0⟩,[-4,16,-28]),(⟨0,9,0⟩,[8,-8]),(⟨0,10,0⟩,[8]),(⟨1,0,0⟩,[0,-9,105,-531,1497,-2493,2319,-837,-321,270]),(⟨1,0,1⟩,[3,-36,198,-652,1408,-2036,1906,-1036,245]),(⟨1,0,2⟩,[1,-15,101,-375,827,-1085,791,-245]),(⟨1,0,3⟩,[-6,52,-202,440,-562,388,-110]),(⟨1,0,4⟩,[-6,42,-132,236,-238,98]),(⟨1,0,6⟩,[-4,20,-36,20]),(⟨1,1,0⟩,[6,-72,396,-1304,2816,-4072,3812,-2072,490]),(⟨1,2,0⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨1,3,0⟩,[-12,100,-376,808,-1036,724,-208]),(⟨1,4,0⟩,[-6,42,-132,236,-238,98]),(⟨1,6,0⟩,[-4,20,-36,20]),(⟨2,0,0⟩,[3,-45,294,-1105,2590,-3767,3118,-1051,-133]),(⟨2,0,1⟩,[3,-33,171,-529,1053,-1351,1029,-343]),(⟨2,0,2⟩,[1,-14,89,-308,623,-686,343]),(⟨2,0,3⟩,[-6,46,-168,328,-354,154]),(⟨2,0,4⟩,[-2,20,-84,140,-98]),(⟨2,0,6⟩,[-4,16,-28]),(⟨2,1,0⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨2,2,0⟩,[2,-28,178,-616,1246,-1372,686]),(⟨2,3,0⟩,[-8,68,-272,552,-592,252]),(⟨2,4,0⟩,[-2,20,-84,140,-98]),(⟨2,6,0⟩,[-4,16,-28]),(⟨3,0,0⟩,[4,-30,134,-484,1256,-2046,1862,-696]),(⟨3,0,1⟩,[-6,48,-174,368,-474,336,-98]),(⟨3,0,2⟩,[-2,22,-104,224,-238,98]),(⟨3,0,3⟩,[12,-56,120,-120,44]),(⟨3,0,4⟩,[12,-44,76,-44]),(⟨3,0,6⟩,[8,-8]),(⟨3,1,0⟩,[-12,100,-376,808,-1036,724,-208]),(⟨3,2,0⟩,[-8,68,-272,552,-592,252]),(⟨3,3,0⟩,[24,-112,240,-240,88]),(⟨3,4,0⟩,[12,-44,76,-44]),(⟨3,6,0⟩,[8,-8]),(⟨4,0,0⟩,[-11,104,-407,800,-737,104,243]),(⟨4,0,1⟩,[-6,42,-132,236,-238,98]),(⟨4,0,2⟩,[-2,20,-84,140,-98]),(⟨4,0,3⟩,[12,-44,76,-44]),(⟨4,0,6⟩,[8]),(⟨4,1,0⟩,[-6,42,-132,236,-238,98]),(⟨4,2,0⟩,[-2,20,-84,140,-98]),(⟨4,3,0⟩,[12,-44,76,-44]),(⟨4,6,0⟩,[8]),(⟨5,0,0⟩,[-14,110,-404,788,-830,350]),(⟨6,0,0⟩,[10,-36,36,20,-54]),(⟨6,0,4⟩,[8]),(⟨6,1,0⟩,[-4,20,-36,20]),(⟨6,2,0⟩,[-4,16,-28]),(⟨6,3,0⟩,[8,-8]),(⟨6,4,0⟩,[8]),(⟨7,0,0⟩,[8,-24,40,-24]),(⟨8,0,0⟩,[-4,16,-28]),(⟨9,0,0⟩,[8,-8]),(⟨10,0,0⟩,[8])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,27,-288,1251,-2772,3033,-792,-1323,684,324]),(⟨0,0,1⟩,[0,-18,204,-1008,2814,-4734,4560,-1788,-594,564]),(⟨0,0,2⟩,[3,-48,336,-1360,3388,-5072,4084,-1072,-427]),(⟨0,0,3⟩,[4,-12,-4,-52,572,-1572,1892,-828]),(⟨0,0,4⟩,[-11,104,-407,800,-737,104,243]),(⟨0,0,5⟩,[-14,110,-404,788,-830,350]),(⟨0,0,6⟩,[10,-24,-12,56,-30]),(⟨0,0,7⟩,[8,-24,40,-24]),(⟨0,0,8⟩,[-4,16,-28]),(⟨0,0,9⟩,[8,-8]),(⟨0,0,10⟩,[8]),(⟨0,1,0⟩,[0,-18,204,-1008,2814,-4734,4560,-1788,-594,564]),(⟨0,1,1⟩,[6,-72,396,-1304,2816,-4072,3812,-2072,490]),(⟨0,1,2⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨0,1,3⟩,[-12,100,-376,808,-1036,724,-208]),(⟨0,1,4⟩,[-6,42,-132,236,-238,98]),(⟨0,1,6⟩,[-4,20,-36,20]),(⟨0,2,0⟩,[3,-48,336,-1360,3388,-5072,4084,-1072,-427]),(⟨0,2,1⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨0,2,2⟩,[2,-28,178,-616,1246,-1372,686]),(⟨0,2,3⟩,[-8,68,-272,552,-592,252]),(⟨0,2,4⟩,[-2,20,-84,140,-98]),(⟨0,2,6⟩,[-4,16,-28]),(⟨0,3,0⟩,[4,-12,-4,-52,572,-1572,1892,-828]),(⟨0,3,1⟩,[-12,100,-376,808,-1036,724,-208]),(⟨0,3,2⟩,[-8,68,-272,552,-592,252]),(⟨0,3,3⟩,[24,-112,240,-240,88]),(⟨0,3,4⟩,[12,-44,76,-44]),(⟨0,3,6⟩,[8,-8]),(⟨0,4,0⟩,[-11,104,-407,800,-737,104,243]),(⟨0,4,1⟩,[-6,42,-132,236,-238,98]),(⟨0,4,2⟩,[-2,20,-84,140,-98]),(⟨0,4,3⟩,[12,-44,76,-44]),(⟨0,4,6⟩,[8]),(⟨0,5,0⟩,[-14,110,-404,788,-830,350]),(⟨0,6,0⟩,[10,-24,-12,56,-30]),(⟨0,6,1⟩,[-4,20,-36,20]),(⟨0,6,2⟩,[-4,16,-28]),(⟨0,6,3⟩,[8,-8]),(⟨0,6,4⟩,[8]),(⟨0,7,0⟩,[8,-24,40,-24]),(⟨0,8,0⟩,[-4,16,-28]),(⟨0,9,0⟩,[8,-8]),(⟨0,10,0⟩,[8]),(⟨1,0,0⟩,[0,-18,204,-1008,2814,-4734,4560,-1788,-594,564]),(⟨1,0,1⟩,[6,-72,396,-1304,2816,-4072,3812,-2072,490]),(⟨1,0,2⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨1,0,3⟩,[-12,100,-376,808,-1036,724,-208]),(⟨1,0,4⟩,[-6,42,-132,236,-238,98]),(⟨1,0,6⟩,[-4,20,-36,20]),(⟨1,1,0⟩,[6,-72,396,-1304,2816,-4072,3812,-2072,490]),(⟨1,2,0⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨1,3,0⟩,[-12,100,-376,808,-1036,724,-208]),(⟨1,4,0⟩,[-6,42,-132,236,-238,98]),(⟨1,6,0⟩,[-4,20,-36,20]),(⟨2,0,0⟩,[3,-48,336,-1360,3388,-5072,4084,-1072,-427]),(⟨2,0,1⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨2,0,2⟩,[2,-28,178,-616,1246,-1372,686]),(⟨2,0,3⟩,[-8,68,-272,552,-592,252]),(⟨2,0,4⟩,[-2,20,-84,140,-98]),(⟨2,0,6⟩,[-4,16,-28]),(⟨2,1,0⟩,[4,-48,272,-904,1880,-2436,1820,-588]),(⟨2,2,0⟩,[2,-28,178,-616,1246,-1372,686]),(⟨2,3,0⟩,[-8,68,-272,552,-592,252]),(⟨2,4,0⟩,[-2,20,-84,140,-98]),(⟨2,6,0⟩,[-4,16,-28]),(⟨3,0,0⟩,[4,-12,-4,-52,572,-1572,1892,-828]),(⟨3,0,1⟩,[-12,100,-376,808,-1036,724,-208]),(⟨3,0,2⟩,[-8,68,-272,552,-592,252]),(⟨3,0,3⟩,[24,-112,240,-240,88]),(⟨3,0,4⟩,[12,-44,76,-44]),(⟨3,0,6⟩,[8,-8]),(⟨3,1,0⟩,[-12,100,-376,808,-1036,724,-208]),(⟨3,2,0⟩,[-8,68,-272,552,-592,252]),(⟨3,3,0⟩,[24,-112,240,-240,88]),(⟨3,4,0⟩,[12,-44,76,-44]),(⟨3,6,0⟩,[8,-8]),(⟨4,0,0⟩,[-11,104,-407,800,-737,104,243]),(⟨4,0,1⟩,[-6,42,-132,236,-238,98]),(⟨4,0,2⟩,[-2,20,-84,140,-98]),(⟨4,0,3⟩,[12,-44,76,-44]),(⟨4,0,6⟩,[8]),(⟨4,1,0⟩,[-6,42,-132,236,-238,98]),(⟨4,2,0⟩,[-2,20,-84,140,-98]),(⟨4,3,0⟩,[12,-44,76,-44]),(⟨4,6,0⟩,[8]),(⟨5,0,0⟩,[-14,110,-404,788,-830,350]),(⟨6,0,0⟩,[10,-24,-12,56,-30]),(⟨6,0,1⟩,[-4,20,-36,20]),(⟨6,0,2⟩,[-4,16,-28]),(⟨6,0,3⟩,[8,-8]),(⟨6,0,4⟩,[8]),(⟨6,1,0⟩,[-4,20,-36,20]),(⟨6,2,0⟩,[-4,16,-28]),(⟨6,3,0⟩,[8,-8]),(⟨6,4,0⟩,[8]),(⟨7,0,0⟩,[8,-24,40,-24]),(⟨8,0,0⟩,[-4,16,-28]),(⟨9,0,0⟩,[8,-8]),(⟨10,0,0⟩,[8])]


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
    (Poly.add (Poly.scale (K.ofRat r178) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 2).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r19*r72 : ℚ)=r178 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 2 r19 r72 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=2 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 2).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C047

#print axioms Coulomb8.Columns.C047.sound
