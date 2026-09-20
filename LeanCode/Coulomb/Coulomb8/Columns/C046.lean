import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C046

def r0 : ℚ := { num := -9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 81, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -135, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 189, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -117, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -171, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 9, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -57, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 111, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -225, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 243, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -225, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 13, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -71, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 219, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -399, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 379, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -121, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -19, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 57, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -31, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 61, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 53, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -125, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -41, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 67, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -103, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 141, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -33, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 31, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 93, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -177, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -59, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 35, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -39, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 49, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -149, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 133, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -59, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -35, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -87, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 157, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -11, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 7, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 33, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -25, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 67, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 11, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -17, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 81, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -135, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 189, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -117, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -171, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -57, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 111, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 243, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -225, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -21, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 13, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -71, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 219, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -399, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 379, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -121, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -19, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 57, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -31, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 61, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 53, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -125, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 5, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -41, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -103, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 141, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -33, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 31, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -13, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 93, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -177, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -59, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 35, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -39, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -149, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 133, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -59, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -35, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -87, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 157, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -11, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 7, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 33, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -25, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 67, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -7, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -17, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,9,r6],[0,r7,r8,r9,r10,r11,r12,r13,9],[r14,r15,r16,r17,r18,r19,r20,r21],[r14,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33],[r28,-3,r34,-13,r35],[-1,4,-6,3],[-1,3,-4],[r36,r37],[r36],[],[],[],[r38,r39,-11,r9,r40,46,r41,r42],[r14,r43,r44,r45,r46,r47,r48],[r28,r49,r26,r50,r51,r48],[r52,r53,r39,r54,r55],[r38,r56,r57,r56],[],[],[],[],[],[],[0,0,r37,r39,r58,r59],[r60,r61,r62,r63,r64],[0,0,r36,r37],[r38,1,r65],[],[],[],[],[],[r66,r67,r68,r6],[r22,2,r57],[r36,r37],[],[],[],[],[],[r36],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r69,r70,r71,r72,r73,r74,r6,r75]),(⟨0,0,1⟩,[0,r60,r76,r77,r12,r78,r79,r80,r6]),(⟨0,0,2⟩,[r81,r82,r83,r84,r85,r86,r87,r88]),(⟨0,0,3⟩,[r81,r89,r90,r91,r92,r93,r94]),(⟨0,0,4⟩,[r95,r96,r64,r97,r98,r99]),(⟨0,0,5⟩,[r95,r66,r100,r101,r102]),(⟨0,0,6⟩,[r37,2,-3,r103]),(⟨0,0,7⟩,[r37,r103,-2]),(⟨0,0,8⟩,[r52,r38]),(⟨0,0,9⟩,[r52]),(⟨0,1,0⟩,[0,r60,r76,r77,r12,r78,r79,r80,r6]),(⟨0,1,1⟩,[r14,r56,r58,r77,r104,23,r105,r106]),(⟨0,1,2⟩,[r81,r107,r108,r109,r110,r111,r112]),(⟨0,1,3⟩,[r95,r113,r93,r114,r115,r112]),(⟨0,1,4⟩,[r116,r117,r56,r118,r119]),(⟨0,1,5⟩,[r14,r28,r0,r28]),(⟨0,2,0⟩,[r81,r82,r83,r84,r85,r86,r87,r88]),(⟨0,2,1⟩,[r81,r107,r108,r109,r110,r111,r112]),(⟨0,2,2⟩,[0,0,r38,r56,r54,r55]),(⟨0,2,3⟩,[r120,r53,r121,r122,r123]),(⟨0,2,4⟩,[0,0,r52,r38]),(⟨0,2,5⟩,[r14,r36,r124]),(⟨0,3,0⟩,[r81,r89,r90,r91,r92,r93,r94]),(⟨0,3,1⟩,[r95,r113,r93,r114,r115,r112]),(⟨0,3,2⟩,[r120,r53,r121,r122,r123]),(⟨0,3,3⟩,[r22,r125,r126,r75]),(⟨0,3,4⟩,[r89,1,r0]),(⟨0,3,5⟩,[r52,r38]),(⟨0,4,0⟩,[r95,r96,r64,r97,r98,r99]),(⟨0,4,1⟩,[r116,r117,r56,r118,r119]),(⟨0,4,2⟩,[0,0,r52,r38]),(⟨0,4,3⟩,[r89,1,r0]),(⟨0,4,5⟩,[r52]),(⟨0,5,0⟩,[r95,r66,r100,r101,r102]),(⟨0,5,1⟩,[r14,r28,r0,r28]),(⟨0,5,2⟩,[r14,r36,r124]),(⟨0,5,3⟩,[r52,r38]),(⟨0,5,4⟩,[r52]),(⟨0,6,0⟩,[r37,2,-3,r103]),(⟨0,7,0⟩,[r37,r103,-2]),(⟨0,8,0⟩,[r52,r38]),(⟨0,9,0⟩,[r52]),(⟨1,0,0⟩,[0,r60,r76,r77,r12,r78,r79,r80,r6]),(⟨1,0,1⟩,[r14,r56,r58,r77,r104,23,r105,r106]),(⟨1,0,2⟩,[r81,r107,r108,r109,r110,r111,r112]),(⟨1,0,3⟩,[r95,r113,r93,r114,r115,r112]),(⟨1,0,4⟩,[r116,r117,r56,r118,r119]),(⟨1,0,5⟩,[r14,r28,r0,r28]),(⟨1,1,0⟩,[r14,r56,r58,r77,r104,23,r105,r106]),(⟨1,2,0⟩,[r81,r107,r108,r109,r110,r111,r112]),(⟨1,3,0⟩,[r95,r113,r93,r114,r115,r112]),(⟨1,4,0⟩,[r116,r117,r56,r118,r119]),(⟨1,5,0⟩,[r14,r28,r0,r28]),(⟨2,0,0⟩,[r81,r82,r83,r84,r85,r86,r87,r88]),(⟨2,0,1⟩,[r81,r107,r108,r109,r110,r111,r112]),(⟨2,0,2⟩,[0,0,r38,r56,r54,r55]),(⟨2,0,3⟩,[r120,r53,r121,r122,r123]),(⟨2,0,4⟩,[0,0,r52,r38]),(⟨2,0,5⟩,[r14,r36,r124]),(⟨2,1,0⟩,[r81,r107,r108,r109,r110,r111,r112]),(⟨2,2,0⟩,[0,0,r38,r56,r54,r55]),(⟨2,3,0⟩,[r120,r53,r121,r122,r123]),(⟨2,4,0⟩,[0,0,r52,r38]),(⟨2,5,0⟩,[r14,r36,r124]),(⟨3,0,0⟩,[r81,r89,r90,r91,r92,r93,r94]),(⟨3,0,1⟩,[r95,r113,r93,r114,r115,r112]),(⟨3,0,2⟩,[r120,r53,r121,r122,r123]),(⟨3,0,3⟩,[r22,r125,r126,r75]),(⟨3,0,4⟩,[r89,1,r0]),(⟨3,0,5⟩,[r52,r38]),(⟨3,1,0⟩,[r95,r113,r93,r114,r115,r112]),(⟨3,2,0⟩,[r120,r53,r121,r122,r123]),(⟨3,3,0⟩,[r22,r125,r126,r75]),(⟨3,4,0⟩,[r89,1,r0]),(⟨3,5,0⟩,[r52,r38]),(⟨4,0,0⟩,[r95,r96,r64,r97,r98,r99]),(⟨4,0,1⟩,[r116,r117,r56,r118,r119]),(⟨4,0,2⟩,[0,0,r52,r38]),(⟨4,0,3⟩,[r89,1,r0]),(⟨4,0,5⟩,[r52]),(⟨4,1,0⟩,[r116,r117,r56,r118,r119]),(⟨4,2,0⟩,[0,0,r52,r38]),(⟨4,3,0⟩,[r89,1,r0]),(⟨4,5,0⟩,[r52]),(⟨5,0,0⟩,[r95,r66,r100,r101,r102]),(⟨5,0,1⟩,[r14,r28,r0,r28]),(⟨5,0,2⟩,[r14,r36,r124]),(⟨5,0,3⟩,[r52,r38]),(⟨5,0,4⟩,[r52]),(⟨5,1,0⟩,[r14,r28,r0,r28]),(⟨5,2,0⟩,[r14,r36,r124]),(⟨5,3,0⟩,[r52,r38]),(⟨5,4,0⟩,[r52]),(⟨6,0,0⟩,[r37,2,-3,r103]),(⟨7,0,0⟩,[r37,r103,-2]),(⟨8,0,0⟩,[r52,r38]),(⟨9,0,0⟩,[r52])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r52) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r52) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[0,-6,30,-42,6,12]),(⟨4,0,1⟩,[2,-10,20,-22,14]),(⟨4,0,2⟩,[0,0,4,-4]),(⟨4,0,3⟩,[-6,16,-18]),(⟨4,0,5⟩,[4]),(⟨4,1,0⟩,[2,-10,20,-22,14]),(⟨4,2,0⟩,[0,0,4,-4]),(⟨4,3,0⟩,[-6,16,-18]),(⟨4,5,0⟩,[4]),(⟨5,0,0⟩,[2,-10,20,-22,14]),(⟨6,0,0⟩,[0,0,4,-4]),(⟨7,0,0⟩,[-6,16,-18]),(⟨9,0,0⟩,[4])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[0,-6,30,-42,6,12]),(⟨0,4,1⟩,[2,-10,20,-22,14]),(⟨0,4,2⟩,[0,0,4,-4]),(⟨0,4,3⟩,[-6,16,-18]),(⟨0,4,5⟩,[4]),(⟨0,5,0⟩,[2,-10,20,-22,14]),(⟨0,6,0⟩,[0,0,4,-4]),(⟨0,7,0⟩,[-6,16,-18]),(⟨0,9,0⟩,[4]),(⟨1,0,0⟩,[0,3,-30,123,-258,273,-102,-39,30]),(⟨1,0,1⟩,[-1,10,-44,111,-177,184,-118,35]),(⟨1,0,2⟩,[0,0,-2,12,-28,28,-10]),(⟨1,0,3⟩,[3,-23,76,-132,121,-45]),(⟨1,0,5⟩,[-2,10,-18,10]),(⟨1,1,0⟩,[-1,10,-44,111,-177,184,-118,35]),(⟨1,2,0⟩,[0,0,-2,12,-28,28,-10]),(⟨1,3,0⟩,[3,-23,76,-132,121,-45]),(⟨1,4,0⟩,[2,-10,20,-22,14]),(⟨1,5,0⟩,[-2,10,-18,10]),(⟨2,0,0⟩,[-1,13,-71,213,-369,337,-115,-7]),(⟨2,0,1⟩,[-1,9,-37,86,-121,105,-49]),(⟨2,0,2⟩,[0,0,-2,10,-22,14]),(⟨2,0,3⟩,[3,-20,62,-92,63]),(⟨2,0,5⟩,[-2,8,-14]),(⟨2,1,0⟩,[-1,9,-37,86,-121,105,-49]),(⟨2,2,0⟩,[0,0,-2,10,-22,14]),(⟨2,3,0⟩,[3,-20,62,-92,63]),(⟨2,4,0⟩,[0,0,4,-4]),(⟨2,5,0⟩,[-2,8,-14]),(⟨3,0,0⟩,[-1,3,-3,26,-101,139,-71]),(⟨3,0,1⟩,[2,-12,30,-42,36,-14]),(⟨3,0,2⟩,[0,0,4,-8,4]),(⟨3,0,3⟩,[-6,22,-34,18]),(⟨3,0,5⟩,[4,-4]),(⟨3,1,0⟩,[2,-12,30,-42,36,-14]),(⟨3,2,0⟩,[0,0,4,-8,4]),(⟨3,3,0⟩,[-6,22,-34,18]),(⟨3,4,0⟩,[-6,16,-18]),(⟨3,5,0⟩,[4,-4]),(⟨4,0,0⟩,[5,-41,134,-206,141,-33]),(⟨4,0,1⟩,[2,-10,20,-22,14]),(⟨4,0,2⟩,[0,0,4,-4]),(⟨4,0,3⟩,[-6,16,-18]),(⟨4,0,5⟩,[4]),(⟨4,1,0⟩,[2,-10,20,-22,14]),(⟨4,2,0⟩,[0,0,4,-4]),(⟨4,3,0⟩,[-6,16,-18]),(⟨4,5,0⟩,[4]),(⟨5,0,0⟩,[5,-30,86,-122,81]),(⟨5,4,0⟩,[4]),(⟨6,0,0⟩,[-8,32,-48,24]),(⟨7,0,0⟩,[-8,24,-32]),(⟨8,0,0⟩,[4,-4]),(⟨9,0,0⟩,[4])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[0,-6,30,-42,6,12]),(⟨0,0,5⟩,[2,-10,20,-22,14]),(⟨0,0,6⟩,[0,0,4,-4]),(⟨0,0,7⟩,[-6,16,-18]),(⟨0,0,9⟩,[4]),(⟨0,1,0⟩,[0,3,-30,123,-258,273,-102,-39,30]),(⟨0,1,1⟩,[-1,10,-44,111,-177,184,-118,35]),(⟨0,1,2⟩,[0,0,-2,12,-28,28,-10]),(⟨0,1,3⟩,[3,-23,76,-132,121,-45]),(⟨0,1,4⟩,[2,-10,20,-22,14]),(⟨0,1,5⟩,[-2,10,-18,10]),(⟨0,2,0⟩,[-1,13,-71,213,-369,337,-115,-7]),(⟨0,2,1⟩,[-1,9,-37,86,-121,105,-49]),(⟨0,2,2⟩,[0,0,-2,10,-22,14]),(⟨0,2,3⟩,[3,-20,62,-92,63]),(⟨0,2,4⟩,[0,0,4,-4]),(⟨0,2,5⟩,[-2,8,-14]),(⟨0,3,0⟩,[-1,3,-3,26,-101,139,-71]),(⟨0,3,1⟩,[2,-12,30,-42,36,-14]),(⟨0,3,2⟩,[0,0,4,-8,4]),(⟨0,3,3⟩,[-6,22,-34,18]),(⟨0,3,4⟩,[-6,16,-18]),(⟨0,3,5⟩,[4,-4]),(⟨0,4,0⟩,[5,-41,134,-206,141,-33]),(⟨0,4,1⟩,[2,-10,20,-22,14]),(⟨0,4,2⟩,[0,0,4,-4]),(⟨0,4,3⟩,[-6,16,-18]),(⟨0,4,5⟩,[4]),(⟨0,5,0⟩,[5,-30,86,-122,81]),(⟨0,5,4⟩,[4]),(⟨0,6,0⟩,[-8,32,-48,24]),(⟨0,7,0⟩,[-8,24,-32]),(⟨0,8,0⟩,[4,-4]),(⟨0,9,0⟩,[4]),(⟨1,0,0⟩,[0,3,-30,123,-258,273,-102,-39,30]),(⟨1,0,1⟩,[-1,10,-44,111,-177,184,-118,35]),(⟨1,0,2⟩,[0,0,-2,12,-28,28,-10]),(⟨1,0,3⟩,[3,-23,76,-132,121,-45]),(⟨1,0,4⟩,[2,-10,20,-22,14]),(⟨1,0,5⟩,[-2,10,-18,10]),(⟨1,1,0⟩,[-2,20,-88,222,-354,368,-236,70]),(⟨1,2,0⟩,[-1,9,-39,98,-149,133,-59]),(⟨1,3,0⟩,[5,-35,106,-174,157,-59]),(⟨1,4,0⟩,[2,-10,20,-22,14]),(⟨1,5,0⟩,[-2,10,-18,10]),(⟨2,0,0⟩,[-1,13,-71,213,-369,337,-115,-7]),(⟨2,0,1⟩,[-1,9,-37,86,-121,105,-49]),(⟨2,0,2⟩,[0,0,-2,10,-22,14]),(⟨2,0,3⟩,[3,-20,62,-92,63]),(⟨2,0,4⟩,[0,0,4,-4]),(⟨2,0,5⟩,[-2,8,-14]),(⟨2,1,0⟩,[-1,9,-39,98,-149,133,-59]),(⟨2,2,0⟩,[0,0,-4,20,-44,28]),(⟨2,3,0⟩,[3,-20,66,-100,67]),(⟨2,4,0⟩,[0,0,4,-4]),(⟨2,5,0⟩,[-2,8,-14]),(⟨3,0,0⟩,[-1,3,-3,26,-101,139,-71]),(⟨3,0,1⟩,[2,-12,30,-42,36,-14]),(⟨3,0,2⟩,[0,0,4,-8,4]),(⟨3,0,3⟩,[-6,22,-34,18]),(⟨3,0,4⟩,[-6,16,-18]),(⟨3,0,5⟩,[4,-4]),(⟨3,1,0⟩,[5,-35,106,-174,157,-59]),(⟨3,2,0⟩,[3,-20,66,-100,67]),(⟨3,3,0⟩,[-12,44,-68,36]),(⟨3,4,0⟩,[-6,16,-18]),(⟨3,5,0⟩,[4,-4]),(⟨4,0,0⟩,[5,-41,134,-206,141,-33]),(⟨4,0,1⟩,[2,-10,20,-22,14]),(⟨4,0,2⟩,[0,0,4,-4]),(⟨4,0,3⟩,[-6,16,-18]),(⟨4,0,5⟩,[4]),(⟨4,1,0⟩,[2,-10,20,-22,14]),(⟨4,2,0⟩,[0,0,4,-4]),(⟨4,3,0⟩,[-6,16,-18]),(⟨4,5,0⟩,[4]),(⟨5,0,0⟩,[5,-30,86,-122,81]),(⟨5,0,4⟩,[4]),(⟨5,1,0⟩,[-2,10,-18,10]),(⟨5,2,0⟩,[-2,8,-14]),(⟨5,3,0⟩,[4,-4]),(⟨5,4,0⟩,[4]),(⟨6,0,0⟩,[-8,32,-48,24]),(⟨7,0,0⟩,[-8,24,-32]),(⟨8,0,0⟩,[4,-4]),(⟨9,0,0⟩,[4])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,-9,81,-270,378,-117,-171,72,36]),(⟨0,0,1⟩,[0,6,-57,222,-450,486,-225,-42,72]),(⟨0,0,2⟩,[-1,13,-71,219,-399,379,-121,-19]),(⟨0,0,3⟩,[-1,-6,57,-124,61,106,-125]),(⟨0,0,4⟩,[5,-41,134,-206,141,-33]),(⟨0,0,5⟩,[5,-24,62,-104,93]),(⟨0,0,6⟩,[-8,32,-48,24]),(⟨0,0,7⟩,[-8,24,-32]),(⟨0,0,8⟩,[4,-4]),(⟨0,0,9⟩,[4]),(⟨0,1,0⟩,[0,6,-57,222,-450,486,-225,-42,72]),(⟨0,1,1⟩,[-2,20,-88,222,-354,368,-236,70]),(⟨0,1,2⟩,[-1,9,-39,98,-149,133,-59]),(⟨0,1,3⟩,[5,-35,106,-174,157,-59]),(⟨0,1,4⟩,[2,-10,20,-22,14]),(⟨0,1,5⟩,[-2,10,-18,10]),(⟨0,2,0⟩,[-1,13,-71,219,-399,379,-121,-19]),(⟨0,2,1⟩,[-1,9,-39,98,-149,133,-59]),(⟨0,2,2⟩,[0,0,-4,20,-44,28]),(⟨0,2,3⟩,[3,-20,66,-100,67]),(⟨0,2,4⟩,[0,0,4,-4]),(⟨0,2,5⟩,[-2,8,-14]),(⟨0,3,0⟩,[-1,-6,57,-124,61,106,-125]),(⟨0,3,1⟩,[5,-35,106,-174,157,-59]),(⟨0,3,2⟩,[3,-20,66,-100,67]),(⟨0,3,3⟩,[-12,44,-68,36]),(⟨0,3,4⟩,[-6,16,-18]),(⟨0,3,5⟩,[4,-4]),(⟨0,4,0⟩,[5,-41,134,-206,141,-33]),(⟨0,4,1⟩,[2,-10,20,-22,14]),(⟨0,4,2⟩,[0,0,4,-4]),(⟨0,4,3⟩,[-6,16,-18]),(⟨0,4,5⟩,[4]),(⟨0,5,0⟩,[5,-24,62,-104,93]),(⟨0,5,1⟩,[-2,10,-18,10]),(⟨0,5,2⟩,[-2,8,-14]),(⟨0,5,3⟩,[4,-4]),(⟨0,5,4⟩,[4]),(⟨0,6,0⟩,[-8,32,-48,24]),(⟨0,7,0⟩,[-8,24,-32]),(⟨0,8,0⟩,[4,-4]),(⟨0,9,0⟩,[4]),(⟨1,0,0⟩,[0,6,-57,222,-450,486,-225,-42,72]),(⟨1,0,1⟩,[-2,20,-88,222,-354,368,-236,70]),(⟨1,0,2⟩,[-1,9,-39,98,-149,133,-59]),(⟨1,0,3⟩,[5,-35,106,-174,157,-59]),(⟨1,0,4⟩,[2,-10,20,-22,14]),(⟨1,0,5⟩,[-2,10,-18,10]),(⟨1,1,0⟩,[-2,20,-88,222,-354,368,-236,70]),(⟨1,2,0⟩,[-1,9,-39,98,-149,133,-59]),(⟨1,3,0⟩,[5,-35,106,-174,157,-59]),(⟨1,4,0⟩,[2,-10,20,-22,14]),(⟨1,5,0⟩,[-2,10,-18,10]),(⟨2,0,0⟩,[-1,13,-71,219,-399,379,-121,-19]),(⟨2,0,1⟩,[-1,9,-39,98,-149,133,-59]),(⟨2,0,2⟩,[0,0,-4,20,-44,28]),(⟨2,0,3⟩,[3,-20,66,-100,67]),(⟨2,0,4⟩,[0,0,4,-4]),(⟨2,0,5⟩,[-2,8,-14]),(⟨2,1,0⟩,[-1,9,-39,98,-149,133,-59]),(⟨2,2,0⟩,[0,0,-4,20,-44,28]),(⟨2,3,0⟩,[3,-20,66,-100,67]),(⟨2,4,0⟩,[0,0,4,-4]),(⟨2,5,0⟩,[-2,8,-14]),(⟨3,0,0⟩,[-1,-6,57,-124,61,106,-125]),(⟨3,0,1⟩,[5,-35,106,-174,157,-59]),(⟨3,0,2⟩,[3,-20,66,-100,67]),(⟨3,0,3⟩,[-12,44,-68,36]),(⟨3,0,4⟩,[-6,16,-18]),(⟨3,0,5⟩,[4,-4]),(⟨3,1,0⟩,[5,-35,106,-174,157,-59]),(⟨3,2,0⟩,[3,-20,66,-100,67]),(⟨3,3,0⟩,[-12,44,-68,36]),(⟨3,4,0⟩,[-6,16,-18]),(⟨3,5,0⟩,[4,-4]),(⟨4,0,0⟩,[5,-41,134,-206,141,-33]),(⟨4,0,1⟩,[2,-10,20,-22,14]),(⟨4,0,2⟩,[0,0,4,-4]),(⟨4,0,3⟩,[-6,16,-18]),(⟨4,0,5⟩,[4]),(⟨4,1,0⟩,[2,-10,20,-22,14]),(⟨4,2,0⟩,[0,0,4,-4]),(⟨4,3,0⟩,[-6,16,-18]),(⟨4,5,0⟩,[4]),(⟨5,0,0⟩,[5,-24,62,-104,93]),(⟨5,0,1⟩,[-2,10,-18,10]),(⟨5,0,2⟩,[-2,8,-14]),(⟨5,0,3⟩,[4,-4]),(⟨5,0,4⟩,[4]),(⟨5,1,0⟩,[-2,10,-18,10]),(⟨5,2,0⟩,[-2,8,-14]),(⟨5,3,0⟩,[4,-4]),(⟨5,4,0⟩,[4]),(⟨6,0,0⟩,[-8,32,-48,24]),(⟨7,0,0⟩,[-8,24,-32]),(⟨8,0,0⟩,[4,-4]),(⟨9,0,0⟩,[4])]


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
    (Poly.add (Poly.scale (K.ofRat r127) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 1).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r52*r52 : ℚ)=r127 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 1 r52 r52 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=1 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C046

#print axioms Coulomb8.Columns.C046.sound
