import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C072

def r0 : ℚ := { num := 81, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -135, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 1575, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -5229, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 21267, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -12897, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 927, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 1377, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -16407, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 891, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 729, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -27, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 369, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 4329, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1347, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 4563, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -20475, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 13479, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -5493, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -4809, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 1323, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 9, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 1137, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -717, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 9825, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -5757, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 36365, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -9203, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 41685, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -917, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -2891, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 3, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -39, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 173, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -531, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1781, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -3135, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 10587, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -3589, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -35, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 91, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -55, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 1267, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -4649, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 2709, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -461, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 525, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 245, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 41, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -255, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 873, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -1825, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 2331, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -1701, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 539, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 115, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -23, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 279, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 229, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 21, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -33, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 59, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -119, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 35, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 19, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 9, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -63, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 837, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -435, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 5013, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -5217, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 15845, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -4319, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 25725, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -5831, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 2401, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -51, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 201, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -935, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 711, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -2961, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 8491, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -8085, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 9261, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -2401, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -243, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 189, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -785, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 553, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -2049, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -539, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 1, den := 32, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 23, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -245, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1631, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -1715, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1127, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 235, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -121, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 603, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -209, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 121, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 1, den := 64, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10],[0,r11,r12,-72,r13,r14,r15,r16,r17,r18,r19,r20],[r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31],[r32,r32,r33,r34,r35,r35,r36,r37,r38,r39],[r40,r41,r42,r43,r44,r45,r46,r47,r48],[r49,r50,r51,r52,r53,r54,r55,r56],[r57,-3,r58,r59,r60,-22,r61],[r62,r63,r64,r65,r66,r67],[r68,r69,r70,r71,r72],[r73,r74,r75,r74],[],[],[r76],[r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87],[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96],[r97,6,r98,r99,r100,r101,r102,140,r103],[],[],[r62,r63,r64,r65,r66,r67],[],[],[],[],[],[r104,r105,r106,r107,r108,r109,r110,r109,r87],[r49,r50,r51,r52,r53,r54,r55,r56],[],[],[r68,r69,r70,r71,r72],[],[],[],[],[r111,r64,r112,r113,r114,r115,r116],[],[],[r73,r74,r75,r74],[],[],[],[],[],[],[],[],[],[],[],[r117],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10]),(⟨0,0,1⟩,[0,r11,r12,-72,r13,r14,r15,r16,r17,r18,r19,r20]),(⟨0,0,2⟩,[r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31]),(⟨0,0,3⟩,[r32,r32,r33,r34,r35,r35,r36,r37,r38,r39]),(⟨0,0,4⟩,[r40,r41,r42,r43,r44,r45,r46,r47,r48]),(⟨0,0,5⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨0,0,6⟩,[r57,-3,r58,r59,r60,-22,r61]),(⟨0,0,7⟩,[r62,r63,r64,r65,r66,r67]),(⟨0,0,8⟩,[r68,r69,r70,r71,r72]),(⟨0,0,9⟩,[r73,r74,r75,r74]),(⟨0,0,12⟩,[r76]),(⟨0,1,0⟩,[0,r11,r12,-72,r13,r14,r15,r16,r17,r18,r19,r20]),(⟨0,1,1⟩,[r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87]),(⟨0,1,2⟩,[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96]),(⟨0,1,3⟩,[r97,6,r98,r99,r100,r101,r102,140,r103]),(⟨0,1,6⟩,[r62,r63,r64,r65,r66,r67]),(⟨0,2,0⟩,[r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31]),(⟨0,2,1⟩,[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96]),(⟨0,2,2⟩,[r104,r105,r106,r107,r108,r109,r110,r109,r87]),(⟨0,2,3⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨0,2,6⟩,[r68,r69,r70,r71,r72]),(⟨0,3,0⟩,[r32,r32,r33,r34,r35,r35,r36,r37,r38,r39]),(⟨0,3,1⟩,[r97,6,r98,r99,r100,r101,r102,140,r103]),(⟨0,3,2⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨0,3,3⟩,[r111,r64,r112,r113,r114,r115,r116]),(⟨0,3,6⟩,[r73,r74,r75,r74]),(⟨0,4,0⟩,[r40,r41,r42,r43,r44,r45,r46,r47,r48]),(⟨0,5,0⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨0,6,0⟩,[r57,-3,r58,r59,r60,-22,r61]),(⟨0,6,1⟩,[r62,r63,r64,r65,r66,r67]),(⟨0,6,2⟩,[r68,r69,r70,r71,r72]),(⟨0,6,3⟩,[r73,r74,r75,r74]),(⟨0,6,6⟩,[r117]),(⟨0,7,0⟩,[r62,r63,r64,r65,r66,r67]),(⟨0,8,0⟩,[r68,r69,r70,r71,r72]),(⟨0,9,0⟩,[r73,r74,r75,r74]),(⟨0,12,0⟩,[r76]),(⟨1,0,0⟩,[0,r11,r12,-72,r13,r14,r15,r16,r17,r18,r19,r20]),(⟨1,0,1⟩,[r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87]),(⟨1,0,2⟩,[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96]),(⟨1,0,3⟩,[r97,6,r98,r99,r100,r101,r102,140,r103]),(⟨1,0,6⟩,[r62,r63,r64,r65,r66,r67]),(⟨1,1,0⟩,[r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87]),(⟨1,2,0⟩,[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96]),(⟨1,3,0⟩,[r97,6,r98,r99,r100,r101,r102,140,r103]),(⟨1,6,0⟩,[r62,r63,r64,r65,r66,r67]),(⟨2,0,0⟩,[r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31]),(⟨2,0,1⟩,[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96]),(⟨2,0,2⟩,[r104,r105,r106,r107,r108,r109,r110,r109,r87]),(⟨2,0,3⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨2,0,6⟩,[r68,r69,r70,r71,r72]),(⟨2,1,0⟩,[r32,r88,r89,r90,r91,r92,r93,r94,r95,r96]),(⟨2,2,0⟩,[r104,r105,r106,r107,r108,r109,r110,r109,r87]),(⟨2,3,0⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨2,6,0⟩,[r68,r69,r70,r71,r72]),(⟨3,0,0⟩,[r32,r32,r33,r34,r35,r35,r36,r37,r38,r39]),(⟨3,0,1⟩,[r97,6,r98,r99,r100,r101,r102,140,r103]),(⟨3,0,2⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨3,0,3⟩,[r111,r64,r112,r113,r114,r115,r116]),(⟨3,0,6⟩,[r73,r74,r75,r74]),(⟨3,1,0⟩,[r97,6,r98,r99,r100,r101,r102,140,r103]),(⟨3,2,0⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨3,3,0⟩,[r111,r64,r112,r113,r114,r115,r116]),(⟨3,6,0⟩,[r73,r74,r75,r74]),(⟨4,0,0⟩,[r40,r41,r42,r43,r44,r45,r46,r47,r48]),(⟨5,0,0⟩,[r49,r50,r51,r52,r53,r54,r55,r56]),(⟨6,0,0⟩,[r57,-3,r58,r59,r60,-22,r61]),(⟨6,0,1⟩,[r62,r63,r64,r65,r66,r67]),(⟨6,0,2⟩,[r68,r69,r70,r71,r72]),(⟨6,0,3⟩,[r73,r74,r75,r74]),(⟨6,0,6⟩,[r117]),(⟨6,1,0⟩,[r62,r63,r64,r65,r66,r67]),(⟨6,2,0⟩,[r68,r69,r70,r71,r72]),(⟨6,3,0⟩,[r73,r74,r75,r74]),(⟨6,6,0⟩,[r117]),(⟨7,0,0⟩,[r62,r63,r64,r65,r66,r67]),(⟨8,0,0⟩,[r68,r69,r70,r71,r72]),(⟨9,0,0⟩,[r73,r74,r75,r74]),(⟨12,0,0⟩,[r76])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r118) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r118) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[0,36,-240,600,-648,132,216]),(⟨6,0,1⟩,[-12,84,-264,472,-476,196]),(⟨6,0,2⟩,[-4,40,-168,280,-196]),(⟨6,0,3⟩,[24,-88,152,-88]),(⟨6,0,6⟩,[16]),(⟨6,1,0⟩,[-12,84,-264,472,-476,196]),(⟨6,2,0⟩,[-4,40,-168,280,-196]),(⟨6,3,0⟩,[24,-88,152,-88]),(⟨6,6,0⟩,[16]),(⟨7,0,0⟩,[-12,84,-264,472,-476,196]),(⟨8,0,0⟩,[-4,40,-168,280,-196]),(⟨9,0,0⟩,[24,-88,152,-88]),(⟨12,0,0⟩,[16])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[0,36,-240,600,-648,132,216]),(⟨0,6,1⟩,[-12,84,-264,472,-476,196]),(⟨0,6,2⟩,[-4,40,-168,280,-196]),(⟨0,6,3⟩,[24,-88,152,-88]),(⟨0,6,6⟩,[16]),(⟨0,7,0⟩,[-12,84,-264,472,-476,196]),(⟨0,8,0⟩,[-4,40,-168,280,-196]),(⟨0,9,0⟩,[24,-88,152,-88]),(⟨0,12,0⟩,[16]),(⟨1,0,0⟩,[0,-27,369,-2304,8658,-21552,36504,-40950,26958,-5493,-4809,2646]),(⟨1,0,1⟩,[9,-126,837,-3480,10026,-20868,31690,-34552,25725,-11662,2401]),(⟨1,0,2⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨1,0,3⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨1,0,6⟩,[-12,84,-264,472,-476,196]),(⟨1,1,0⟩,[9,-126,837,-3480,10026,-20868,31690,-34552,25725,-11662,2401]),(⟨1,2,0⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨1,3,0⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨1,6,0⟩,[-24,168,-528,944,-952,392]),(⟨2,0,0⟩,[9,-135,987,-4608,14838,-33462,52210,-54088,33705,-9499,-245]),(⟨2,0,1⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨2,0,2⟩,[1,-20,184,-980,3262,-6860,9016,-6860,2401]),(⟨2,0,3⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨2,0,6⟩,[-4,40,-168,280,-196]),(⟨2,1,0⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨2,2,0⟩,[1,-20,184,-980,3262,-6860,9016,-6860,2401]),(⟨2,3,0⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨2,6,0⟩,[-8,80,-336,560,-392]),(⟨3,0,0⟩,[6,-48,246,-1178,4626,-12906,24106,-28710,19848,-5990]),(⟨3,0,1⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨3,0,2⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨3,0,3⟩,[36,-264,940,-1936,2412,-1672,484]),(⟨3,0,6⟩,[24,-88,152,-88]),(⟨3,1,0⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨3,2,0⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨3,3,0⟩,[36,-264,940,-1936,2412,-1672,484]),(⟨3,6,0⟩,[48,-176,304,-176]),(⟨4,0,0⟩,[-35,364,-1760,5068,-9298,10836,-7376,2100,245]),(⟨5,0,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨6,0,0⟩,[36,-228,700,-1336,1764,-1540,700]),(⟨6,0,1⟩,[-12,84,-264,472,-476,196]),(⟨6,0,2⟩,[-4,40,-168,280,-196]),(⟨6,0,3⟩,[24,-88,152,-88]),(⟨6,0,6⟩,[16]),(⟨6,1,0⟩,[-12,84,-264,472,-476,196]),(⟨6,2,0⟩,[-4,40,-168,280,-196]),(⟨6,3,0⟩,[24,-88,152,-88]),(⟨6,6,0⟩,[32]),(⟨7,0,0⟩,[-24,168,-528,944,-952,392]),(⟨8,0,0⟩,[-8,80,-336,560,-392]),(⟨9,0,0⟩,[48,-176,304,-176]),(⟨12,0,0⟩,[16])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[0,36,-240,600,-648,132,216]),(⟨0,0,7⟩,[-12,84,-264,472,-476,196]),(⟨0,0,8⟩,[-4,40,-168,280,-196]),(⟨0,0,9⟩,[24,-88,152,-88]),(⟨0,0,12⟩,[16]),(⟨0,1,0⟩,[0,-27,369,-2304,8658,-21552,36504,-40950,26958,-5493,-4809,2646]),(⟨0,1,1⟩,[9,-126,837,-3480,10026,-20868,31690,-34552,25725,-11662,2401]),(⟨0,1,2⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨0,1,3⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨0,1,6⟩,[-24,168,-528,944,-952,392]),(⟨0,2,0⟩,[9,-135,987,-4608,14838,-33462,52210,-54088,33705,-9499,-245]),(⟨0,2,1⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨0,2,2⟩,[1,-20,184,-980,3262,-6860,9016,-6860,2401]),(⟨0,2,3⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨0,2,6⟩,[-8,80,-336,560,-392]),(⟨0,3,0⟩,[6,-48,246,-1178,4626,-12906,24106,-28710,19848,-5990]),(⟨0,3,1⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨0,3,2⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨0,3,3⟩,[36,-264,940,-1936,2412,-1672,484]),(⟨0,3,6⟩,[48,-176,304,-176]),(⟨0,4,0⟩,[-35,364,-1760,5068,-9298,10836,-7376,2100,245]),(⟨0,5,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨0,6,0⟩,[36,-228,700,-1336,1764,-1540,700]),(⟨0,6,1⟩,[-12,84,-264,472,-476,196]),(⟨0,6,2⟩,[-4,40,-168,280,-196]),(⟨0,6,3⟩,[24,-88,152,-88]),(⟨0,6,6⟩,[32]),(⟨0,7,0⟩,[-24,168,-528,944,-952,392]),(⟨0,8,0⟩,[-8,80,-336,560,-392]),(⟨0,9,0⟩,[48,-176,304,-176]),(⟨0,12,0⟩,[16]),(⟨1,0,0⟩,[0,-27,369,-2304,8658,-21552,36504,-40950,26958,-5493,-4809,2646]),(⟨1,0,1⟩,[9,-126,837,-3480,10026,-20868,31690,-34552,25725,-11662,2401]),(⟨1,0,2⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨1,0,3⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨1,0,6⟩,[-24,168,-528,944,-952,392]),(⟨1,1,0⟩,[18,-252,1674,-6960,20052,-41736,63380,-69104,51450,-23324,4802]),(⟨1,2,0⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨1,3,0⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨1,6,0⟩,[-24,168,-528,944,-952,392]),(⟨2,0,0⟩,[9,-135,987,-4608,14838,-33462,52210,-54088,33705,-9499,-245]),(⟨2,0,1⟩,[3,-51,402,-1870,5688,-11844,16982,-16170,9261,-2401]),(⟨2,0,2⟩,[1,-20,184,-980,3262,-6860,9016,-6860,2401]),(⟨2,0,3⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨2,0,6⟩,[-8,80,-336,560,-392]),(⟨2,1,0⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨2,2,0⟩,[2,-40,368,-1960,6524,-13720,18032,-13720,4802]),(⟨2,3,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨2,6,0⟩,[-8,80,-336,560,-392]),(⟨3,0,0⟩,[6,-48,246,-1178,4626,-12906,24106,-28710,19848,-5990]),(⟨3,0,1⟩,[-18,192,-972,3024,-6280,8848,-8196,4480,-1078]),(⟨3,0,2⟩,[-6,82,-510,1746,-3650,4662,-3402,1078]),(⟨3,0,3⟩,[36,-264,940,-1936,2412,-1672,484]),(⟨3,0,6⟩,[48,-176,304,-176]),(⟨3,1,0⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨3,2,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨3,3,0⟩,[72,-528,1880,-3872,4824,-3344,968]),(⟨3,6,0⟩,[48,-176,304,-176]),(⟨4,0,0⟩,[-35,364,-1760,5068,-9298,10836,-7376,2100,245]),(⟨5,0,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨6,0,0⟩,[36,-228,700,-1336,1764,-1540,700]),(⟨6,0,1⟩,[-12,84,-264,472,-476,196]),(⟨6,0,2⟩,[-4,40,-168,280,-196]),(⟨6,0,3⟩,[24,-88,152,-88]),(⟨6,0,6⟩,[32]),(⟨6,1,0⟩,[-24,168,-528,944,-952,392]),(⟨6,2,0⟩,[-8,80,-336,560,-392]),(⟨6,3,0⟩,[48,-176,304,-176]),(⟨6,6,0⟩,[32]),(⟨7,0,0⟩,[-24,168,-528,944,-952,392]),(⟨8,0,0⟩,[-8,80,-336,560,-392]),(⟨9,0,0⟩,[48,-176,304,-176]),(⟨12,0,0⟩,[16])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,81,-1080,6300,-20916,42534,-51588,29664,5508,-16407,3564,2916]),(⟨0,0,1⟩,[0,-54,738,-4608,17316,-43104,73008,-81900,53916,-10986,-9618,5292]),(⟨0,0,2⟩,[9,-144,1137,-5736,19650,-46056,72730,-73624,41685,-7336,-2891]),(⟨0,0,3⟩,[6,6,-312,1384,-2124,-2124,14248,-25080,21174,-7178]),(⟨0,0,4⟩,[-35,364,-1760,5068,-9298,10836,-7376,2100,245]),(⟨0,0,5⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨0,0,6⟩,[36,-192,460,-736,1116,-1408,916]),(⟨0,0,7⟩,[-24,168,-528,944,-952,392]),(⟨0,0,8⟩,[-8,80,-336,560,-392]),(⟨0,0,9⟩,[48,-176,304,-176]),(⟨0,0,12⟩,[16]),(⟨0,1,0⟩,[0,-54,738,-4608,17316,-43104,73008,-81900,53916,-10986,-9618,5292]),(⟨0,1,1⟩,[18,-252,1674,-6960,20052,-41736,63380,-69104,51450,-23324,4802]),(⟨0,1,2⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨0,1,3⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨0,1,6⟩,[-24,168,-528,944,-952,392]),(⟨0,2,0⟩,[9,-144,1137,-5736,19650,-46056,72730,-73624,41685,-7336,-2891]),(⟨0,2,1⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨0,2,2⟩,[2,-40,368,-1960,6524,-13720,18032,-13720,4802]),(⟨0,2,3⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨0,2,6⟩,[-8,80,-336,560,-392]),(⟨0,3,0⟩,[6,6,-312,1384,-2124,-2124,14248,-25080,21174,-7178]),(⟨0,3,1⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨0,3,2⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨0,3,3⟩,[72,-528,1880,-3872,4824,-3344,968]),(⟨0,3,6⟩,[48,-176,304,-176]),(⟨0,4,0⟩,[-35,364,-1760,5068,-9298,10836,-7376,2100,245]),(⟨0,5,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨0,6,0⟩,[36,-192,460,-736,1116,-1408,916]),(⟨0,6,1⟩,[-24,168,-528,944,-952,392]),(⟨0,6,2⟩,[-8,80,-336,560,-392]),(⟨0,6,3⟩,[48,-176,304,-176]),(⟨0,6,6⟩,[32]),(⟨0,7,0⟩,[-24,168,-528,944,-952,392]),(⟨0,8,0⟩,[-8,80,-336,560,-392]),(⟨0,9,0⟩,[48,-176,304,-176]),(⟨0,12,0⟩,[16]),(⟨1,0,0⟩,[0,-54,738,-4608,17316,-43104,73008,-81900,53916,-10986,-9618,5292]),(⟨1,0,1⟩,[18,-252,1674,-6960,20052,-41736,63380,-69104,51450,-23324,4802]),(⟨1,0,2⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨1,0,3⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨1,0,6⟩,[-24,168,-528,944,-952,392]),(⟨1,1,0⟩,[18,-252,1674,-6960,20052,-41736,63380,-69104,51450,-23324,4802]),(⟨1,2,0⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨1,3,0⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨1,6,0⟩,[-24,168,-528,944,-952,392]),(⟨2,0,0⟩,[9,-144,1137,-5736,19650,-46056,72730,-73624,41685,-7336,-2891]),(⟨2,0,1⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨2,0,2⟩,[2,-40,368,-1960,6524,-13720,18032,-13720,4802]),(⟨2,0,3⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨2,0,6⟩,[-8,80,-336,560,-392]),(⟨2,1,0⟩,[6,-102,804,-3740,11376,-23688,33964,-32340,18522,-4802]),(⟨2,2,0⟩,[2,-40,368,-1960,6524,-13720,18032,-13720,4802]),(⟨2,3,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨2,6,0⟩,[-8,80,-336,560,-392]),(⟨3,0,0⟩,[6,6,-312,1384,-2124,-2124,14248,-25080,21174,-7178]),(⟨3,0,1⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨3,0,2⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨3,0,3⟩,[72,-528,1880,-3872,4824,-3344,968]),(⟨3,0,6⟩,[48,-176,304,-176]),(⟨3,1,0⟩,[-36,384,-1944,6048,-12560,17696,-16392,8960,-2156]),(⟨3,2,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨3,3,0⟩,[72,-528,1880,-3872,4824,-3344,968]),(⟨3,6,0⟩,[48,-176,304,-176]),(⟨4,0,0⟩,[-35,364,-1760,5068,-9298,10836,-7376,2100,245]),(⟨5,0,0⟩,[-12,164,-1020,3492,-7300,9324,-6804,2156]),(⟨6,0,0⟩,[36,-192,460,-736,1116,-1408,916]),(⟨6,0,1⟩,[-24,168,-528,944,-952,392]),(⟨6,0,2⟩,[-8,80,-336,560,-392]),(⟨6,0,3⟩,[48,-176,304,-176]),(⟨6,0,6⟩,[32]),(⟨6,1,0⟩,[-24,168,-528,944,-952,392]),(⟨6,2,0⟩,[-8,80,-336,560,-392]),(⟨6,3,0⟩,[48,-176,304,-176]),(⟨6,6,0⟩,[32]),(⟨7,0,0⟩,[-24,168,-528,944,-952,392]),(⟨8,0,0⟩,[-8,80,-336,560,-392]),(⟨9,0,0⟩,[48,-176,304,-176]),(⟨12,0,0⟩,[16])]


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
    (Poly.add (Poly.scale (K.ofRat r119) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 2).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r118*r118 : ℚ)=r119 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 2 r118 r118 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=2 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 2).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C072

#print axioms Coulomb8.Columns.C072.sound
