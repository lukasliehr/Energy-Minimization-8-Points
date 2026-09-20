import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C140

def r0 : ℚ := { num := 256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -6656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 75520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -498688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 2133760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -6134272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 11782400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -14364672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 9764864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -2752512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 262144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -3072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 62464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -542720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 157696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -8248320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 15967232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -18436096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 10747904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -1703936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -105984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 421888, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -691712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -552960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 4181504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -6148096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 2883584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 7168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 780288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -2488320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 240640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -2812928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 20480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -5632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 16128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 150528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -938240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 1845760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -1265408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 57344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -212992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 204800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 86016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -98304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 147456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -1024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 41984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -485376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 2697216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -8451072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 15332352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -14966784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 6094848, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 3072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -50176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 256000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -411648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -500736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 2362368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -2183168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 1024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -46080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 403456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1370112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 119808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -1156096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -8192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 106496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -385024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 24576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -11264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 82432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -227328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 243200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -211968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 321024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -196608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 294912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -23552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 233472, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -1349632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 4858880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -10447872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 12191744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -352256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -5120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -559104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 1894400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -3417088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 148480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 21504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -157696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 485376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -37888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 8192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -106496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 385024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -24576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -2048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 40960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -274432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 40960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -20480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 137216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -20480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 1, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10],[0,r11,r12,r13,r14,r15,r16,r17,r18,r19],[r20,r21,r22,r23,r24,r25,r26,r27,r28],[0,r29,r30,r31,r32,r33,r34,r35],[r0,r36,r37,r38,r39,r40,r41],[0,r42,r43,r44,r45,r46],[0,0,r47,r48,r49],[],[],[],[],[],[],[0,r50,r51,r52,r53,r54,r55,r56,r57],[0,r58,r59,r60,r61,r62,r63,r64],[0,r65,r66,r67,r68,r69,r70],[0,0,r71,r72,r73,r74],[],[],[],[],[],[],[],[r75,r76,r77,r78,r79,r80,r81],[0,r42,r43,r44,r45,r46],[],[],[],[],[],[],[],[0,0,r82,r83,r84],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r65,r85,r86,r87,r88,r89,r90,r91],[0,r92,r93,r94,r95,r96,r97],[r50,r98,r99,r100,r101,1024],[0,r102,r103,r104,r105],[],[],[],[],[],[],[0,r106,r107,r108,r109,-2048],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r65,r110,r111,r112,1024],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10]),(⟨0,0,1⟩,[0,r11,r12,r13,r14,r15,r16,r17,r18,r19]),(⟨0,0,2⟩,[r20,r21,r22,r23,r24,r25,r26,r27,r28]),(⟨0,0,3⟩,[0,r29,r30,r31,r32,r33,r34,r35]),(⟨0,0,4⟩,[r0,r36,r37,r38,r39,r40,r41]),(⟨0,0,5⟩,[0,r42,r43,r44,r45,r46]),(⟨0,0,6⟩,[0,0,r47,r48,r49]),(⟨0,1,0⟩,[0,r11,r12,r13,r14,r15,r16,r17,r18,r19]),(⟨0,1,1⟩,[0,r50,r51,r52,r53,r54,r55,r56,r57]),(⟨0,1,2⟩,[0,r58,r59,r60,r61,r62,r63,r64]),(⟨0,1,3⟩,[0,r65,r66,r67,r68,r69,r70]),(⟨0,1,4⟩,[0,0,r71,r72,r73,r74]),(⟨0,2,0⟩,[r20,r21,r22,r23,r24,r25,r26,r27,r28]),(⟨0,2,1⟩,[0,r58,r59,r60,r61,r62,r63,r64]),(⟨0,2,2⟩,[r75,r76,r77,r78,r79,r80,r81]),(⟨0,2,3⟩,[0,r42,r43,r44,r45,r46]),(⟨0,3,0⟩,[0,r29,r30,r31,r32,r33,r34,r35]),(⟨0,3,1⟩,[0,r65,r66,r67,r68,r69,r70]),(⟨0,3,2⟩,[0,r42,r43,r44,r45,r46]),(⟨0,3,3⟩,[0,0,r82,r83,r84]),(⟨0,4,0⟩,[r0,r36,r37,r38,r39,r40,r41]),(⟨0,4,1⟩,[0,0,r71,r72,r73,r74]),(⟨0,5,0⟩,[0,r42,r43,r44,r45,r46]),(⟨0,6,0⟩,[0,0,r47,r48,r49]),(⟨1,0,0⟩,[0,r11,r12,r13,r14,r15,r16,r17,r18,r19]),(⟨1,0,1⟩,[0,r50,r51,r52,r53,r54,r55,r56,r57]),(⟨1,0,2⟩,[0,r58,r59,r60,r61,r62,r63,r64]),(⟨1,0,3⟩,[0,r65,r66,r67,r68,r69,r70]),(⟨1,0,4⟩,[0,0,r71,r72,r73,r74]),(⟨1,1,0⟩,[0,r50,r51,r52,r53,r54,r55,r56,r57]),(⟨1,1,1⟩,[r65,r85,r86,r87,r88,r89,r90,r91]),(⟨1,1,2⟩,[0,r92,r93,r94,r95,r96,r97]),(⟨1,1,3⟩,[r50,r98,r99,r100,r101,1024]),(⟨1,1,4⟩,[0,r102,r103,r104,r105]),(⟨1,2,0⟩,[0,r58,r59,r60,r61,r62,r63,r64]),(⟨1,2,1⟩,[0,r92,r93,r94,r95,r96,r97]),(⟨1,2,2⟩,[0,r106,r107,r108,r109,-2048]),(⟨1,3,0⟩,[0,r65,r66,r67,r68,r69,r70]),(⟨1,3,1⟩,[r50,r98,r99,r100,r101,1024]),(⟨1,4,0⟩,[0,0,r71,r72,r73,r74]),(⟨1,4,1⟩,[0,r102,r103,r104,r105]),(⟨2,0,0⟩,[r20,r21,r22,r23,r24,r25,r26,r27,r28]),(⟨2,0,1⟩,[0,r58,r59,r60,r61,r62,r63,r64]),(⟨2,0,2⟩,[r75,r76,r77,r78,r79,r80,r81]),(⟨2,0,3⟩,[0,r42,r43,r44,r45,r46]),(⟨2,1,0⟩,[0,r58,r59,r60,r61,r62,r63,r64]),(⟨2,1,1⟩,[0,r92,r93,r94,r95,r96,r97]),(⟨2,1,2⟩,[0,r106,r107,r108,r109,-2048]),(⟨2,2,0⟩,[r75,r76,r77,r78,r79,r80,r81]),(⟨2,2,1⟩,[0,r106,r107,r108,r109,-2048]),(⟨2,2,2⟩,[r65,r110,r111,r112,1024]),(⟨2,3,0⟩,[0,r42,r43,r44,r45,r46]),(⟨3,0,0⟩,[0,r29,r30,r31,r32,r33,r34,r35]),(⟨3,0,1⟩,[0,r65,r66,r67,r68,r69,r70]),(⟨3,0,2⟩,[0,r42,r43,r44,r45,r46]),(⟨3,0,3⟩,[0,0,r82,r83,r84]),(⟨3,1,0⟩,[0,r65,r66,r67,r68,r69,r70]),(⟨3,1,1⟩,[r50,r98,r99,r100,r101,1024]),(⟨3,2,0⟩,[0,r42,r43,r44,r45,r46]),(⟨3,3,0⟩,[0,0,r82,r83,r84]),(⟨4,0,0⟩,[r0,r36,r37,r38,r39,r40,r41]),(⟨4,0,1⟩,[0,0,r71,r72,r73,r74]),(⟨4,1,0⟩,[0,0,r71,r72,r73,r74]),(⟨4,1,1⟩,[0,r102,r103,r104,r105]),(⟨5,0,0⟩,[0,r42,r43,r44,r45,r46]),(⟨6,0,0⟩,[0,0,r47,r48,r49])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r113) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r113) sourceRight))).isZero := by decide +kernel

noncomputable def partial14 : Poly := []

theorem partial_sound14 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 14)
      sourceRight).eval u v t=partial14.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[-256,6144,-57600,278528,-762624,1122304,-629504,-145408,57344]),(⟨2,0,1⟩,[0,1536,-28160,181248,-539648,749056,-308736,-186368]),(⟨2,0,2⟩,[256,-5632,40704,-103424,52992,68096,12544]),(⟨2,0,3⟩,[0,-2048,28672,-106496,102400,43008]),(⟨2,1,0⟩,[0,1536,-28160,181248,-539648,749056,-308736,-186368]),(⟨2,1,1⟩,[0,512,-10752,74752,-189440,129536,60928]),(⟨2,2,0⟩,[256,-5632,40704,-103424,52992,68096,12544]),(⟨2,3,0⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,0,0⟩,[0,3584,-60928,390144,-1244160,2045440,-1406464,10240]),(⟨3,0,1⟩,[0,512,-23040,201728,-685056,1018368,-578048]),(⟨3,0,2⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,0,3⟩,[0,0,16384,-98304,147456]),(⟨3,1,0⟩,[0,512,-23040,201728,-685056,1018368,-578048]),(⟨3,1,1⟩,[-512,10752,-78848,242688,-322048,147968]),(⟨3,2,0⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,3,0⟩,[0,0,16384,-98304,147456]),(⟨4,0,0⟩,[256,-5632,28416,23552,-442624,956928,-626432]),(⟨4,0,1⟩,[0,0,-4096,53248,-192512,208896]),(⟨4,1,0⟩,[0,0,-4096,53248,-192512,208896]),(⟨4,1,1⟩,[0,4096,-53248,192512,-208896]),(⟨5,0,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨6,0,0⟩,[0,0,16384,-98304,147456])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial14)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 14))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound14 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544])]

noncomputable def partial8 : Poly := [(⟨1,0,0⟩,[0,-1536,31232,-271360,1340416,-4124160,7983616,-9218048,5373952,-851968]),(⟨1,0,1⟩,[0,-512,20992,-242688,1348608,-4225536,7666176,-7483392,3047424]),(⟨1,0,2⟩,[0,1536,-25088,128000,-205824,-250368,1181184,-1091584]),(⟨1,0,3⟩,[0,512,-23040,201728,-685056,1018368,-578048]),(⟨1,0,4⟩,[0,0,-4096,53248,-192512,208896]),(⟨1,1,0⟩,[0,-512,20992,-242688,1348608,-4225536,7666176,-7483392,3047424]),(⟨1,1,1⟩,[512,-11776,116736,-674816,2429440,-5223936,6095872,-2994176]),(⟨1,1,2⟩,[0,-2560,43520,-279552,947200,-1708544,1262080]),(⟨1,1,3⟩,[-512,10752,-78848,242688,-322048,147968]),(⟨1,1,4⟩,[0,4096,-53248,192512,-208896]),(⟨1,2,0⟩,[0,1536,-25088,128000,-205824,-250368,1181184,-1091584]),(⟨1,2,1⟩,[0,-2560,43520,-279552,947200,-1708544,1262080]),(⟨1,2,2⟩,[0,-1024,20480,-137216,348160,-295936]),(⟨1,3,0⟩,[0,512,-23040,201728,-685056,1018368,-578048]),(⟨1,3,1⟩,[-512,10752,-78848,242688,-322048,147968]),(⟨1,4,0⟩,[0,0,-4096,53248,-192512,208896]),(⟨1,4,1⟩,[0,4096,-53248,192512,-208896]),(⟨2,0,0⟩,[-256,6144,-48384,143360,70912,-1675264,4811008,-6002688,2826240]),(⟨2,0,1⟩,[0,1536,-22016,74752,128000,-1249792,2671104,-1996800]),(⟨2,0,2⟩,[256,-5632,41728,-123904,190208,-280064,308480]),(⟨2,0,3⟩,[0,-2048,28672,-106496,102400,43008]),(⟨2,1,0⟩,[0,1536,-22016,74752,128000,-1249792,2671104,-1996800]),(⟨2,1,1⟩,[0,-5632,97792,-633856,2083840,-3546624,2463232]),(⟨2,1,2⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨2,2,0⟩,[256,-5632,41728,-123904,190208,-280064,308480]),(⟨2,2,1⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨2,2,2⟩,[1024,-20480,137216,-348160,295936]),(⟨2,3,0⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,0,0⟩,[0,5120,-89088,571392,-1783808,2794496,-1715200,-176128]),(⟨3,0,1⟩,[0,1024,-33792,276480,-874496,1147904,-517120]),(⟨3,0,2⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,0,3⟩,[0,0,16384,-98304,147456]),(⟨3,1,0⟩,[0,1024,-33792,276480,-874496,1147904,-517120]),(⟨3,1,1⟩,[-1024,21504,-153600,432128,-451584,87040]),(⟨3,2,0⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,3,0⟩,[0,0,16384,-98304,147456]),(⟨4,0,0⟩,[256,-5632,16128,150528,-938240,1845760,-1265408]),(⟨4,0,1⟩,[0,0,-8192,106496,-385024,417792]),(⟨4,1,0⟩,[0,0,-8192,106496,-385024,417792]),(⟨4,1,1⟩,[0,8192,-106496,385024,-417792]),(⟨5,0,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨6,0,0⟩,[0,0,16384,-98304,147456])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-1536,31232,-271360,1340416,-4124160,7983616,-9218048,5373952,-851968]),(⟨0,1,1⟩,[0,-512,20992,-242688,1348608,-4225536,7666176,-7483392,3047424]),(⟨0,1,2⟩,[0,1536,-25088,128000,-205824,-250368,1181184,-1091584]),(⟨0,1,3⟩,[0,512,-23040,201728,-685056,1018368,-578048]),(⟨0,1,4⟩,[0,0,-4096,53248,-192512,208896]),(⟨0,2,0⟩,[-256,6144,-48384,143360,70912,-1675264,4811008,-6002688,2826240]),(⟨0,2,1⟩,[0,1536,-22016,74752,128000,-1249792,2671104,-1996800]),(⟨0,2,2⟩,[256,-5632,41728,-123904,190208,-280064,308480]),(⟨0,2,3⟩,[0,-2048,28672,-106496,102400,43008]),(⟨0,3,0⟩,[0,5120,-89088,571392,-1783808,2794496,-1715200,-176128]),(⟨0,3,1⟩,[0,1024,-33792,276480,-874496,1147904,-517120]),(⟨0,3,2⟩,[0,-2048,28672,-106496,102400,43008]),(⟨0,3,3⟩,[0,0,16384,-98304,147456]),(⟨0,4,0⟩,[256,-5632,16128,150528,-938240,1845760,-1265408]),(⟨0,4,1⟩,[0,0,-8192,106496,-385024,417792]),(⟨0,5,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨0,6,0⟩,[0,0,16384,-98304,147456]),(⟨1,0,0⟩,[0,-1536,31232,-271360,1340416,-4124160,7983616,-9218048,5373952,-851968]),(⟨1,0,1⟩,[0,-512,20992,-242688,1348608,-4225536,7666176,-7483392,3047424]),(⟨1,0,2⟩,[0,1536,-25088,128000,-205824,-250368,1181184,-1091584]),(⟨1,0,3⟩,[0,512,-23040,201728,-685056,1018368,-578048]),(⟨1,0,4⟩,[0,0,-4096,53248,-192512,208896]),(⟨1,1,0⟩,[0,-512,30208,-377856,2182144,-7023104,13106688,-13340672,5816320]),(⟨1,1,1⟩,[512,-11776,122880,-781312,3097088,-7222784,9075712,-4804608]),(⟨1,1,2⟩,[0,-2560,44544,-300032,1084416,-2056704,1558016]),(⟨1,1,3⟩,[-512,10752,-78848,242688,-322048,147968]),(⟨1,1,4⟩,[0,4096,-53248,192512,-208896]),(⟨1,2,0⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨1,2,1⟩,[0,-5120,87040,-559104,1894400,-3417088,2524160]),(⟨1,2,2⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨1,3,0⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨1,3,1⟩,[-1024,21504,-157696,485376,-644096,295936]),(⟨1,4,0⟩,[0,0,-8192,106496,-385024,417792]),(⟨1,4,1⟩,[0,8192,-106496,385024,-417792]),(⟨2,0,0⟩,[-256,6144,-48384,143360,70912,-1675264,4811008,-6002688,2826240]),(⟨2,0,1⟩,[0,1536,-22016,74752,128000,-1249792,2671104,-1996800]),(⟨2,0,2⟩,[256,-5632,41728,-123904,190208,-280064,308480]),(⟨2,0,3⟩,[0,-2048,28672,-106496,102400,43008]),(⟨2,1,0⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨2,1,1⟩,[0,-5120,87040,-559104,1894400,-3417088,2524160]),(⟨2,1,2⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨2,2,0⟩,[512,-11264,82432,-227328,243200,-211968,321024]),(⟨2,2,1⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨2,2,2⟩,[1024,-20480,137216,-348160,295936]),(⟨2,3,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨3,0,0⟩,[0,5120,-89088,571392,-1783808,2794496,-1715200,-176128]),(⟨3,0,1⟩,[0,1024,-33792,276480,-874496,1147904,-517120]),(⟨3,0,2⟩,[0,-2048,28672,-106496,102400,43008]),(⟨3,0,3⟩,[0,0,16384,-98304,147456]),(⟨3,1,0⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨3,1,1⟩,[-1024,21504,-157696,485376,-644096,295936]),(⟨3,2,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨3,3,0⟩,[0,0,32768,-196608,294912]),(⟨4,0,0⟩,[256,-5632,16128,150528,-938240,1845760,-1265408]),(⟨4,0,1⟩,[0,0,-8192,106496,-385024,417792]),(⟨4,1,0⟩,[0,0,-8192,106496,-385024,417792]),(⟨4,1,1⟩,[0,8192,-106496,385024,-417792]),(⟨5,0,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨6,0,0⟩,[0,0,16384,-98304,147456])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[256,-6656,75520,-498688,2133760,-6134272,11782400,-14364672,9764864,-2752512,262144]),(⟨0,0,1⟩,[0,-3072,62464,-542720,2680832,-8248320,15967232,-18436096,10747904,-1703936]),(⟨0,0,2⟩,[-512,12288,-105984,421888,-691712,-552960,4181504,-6148096,2883584]),(⟨0,0,3⟩,[0,7168,-121856,780288,-2488320,4090880,-2812928,20480]),(⟨0,0,4⟩,[256,-5632,16128,150528,-938240,1845760,-1265408]),(⟨0,0,5⟩,[0,-4096,57344,-212992,204800,86016]),(⟨0,0,6⟩,[0,0,16384,-98304,147456]),(⟨0,1,0⟩,[0,-3072,62464,-542720,2680832,-8248320,15967232,-18436096,10747904,-1703936]),(⟨0,1,1⟩,[0,-1024,41984,-485376,2697216,-8451072,15332352,-14966784,6094848]),(⟨0,1,2⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨0,1,3⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨0,1,4⟩,[0,0,-8192,106496,-385024,417792]),(⟨0,2,0⟩,[-512,12288,-105984,421888,-691712,-552960,4181504,-6148096,2883584]),(⟨0,2,1⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨0,2,2⟩,[512,-11264,82432,-227328,243200,-211968,321024]),(⟨0,2,3⟩,[0,-4096,57344,-212992,204800,86016]),(⟨0,3,0⟩,[0,7168,-121856,780288,-2488320,4090880,-2812928,20480]),(⟨0,3,1⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨0,3,2⟩,[0,-4096,57344,-212992,204800,86016]),(⟨0,3,3⟩,[0,0,32768,-196608,294912]),(⟨0,4,0⟩,[256,-5632,16128,150528,-938240,1845760,-1265408]),(⟨0,4,1⟩,[0,0,-8192,106496,-385024,417792]),(⟨0,5,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨0,6,0⟩,[0,0,16384,-98304,147456]),(⟨1,0,0⟩,[0,-3072,62464,-542720,2680832,-8248320,15967232,-18436096,10747904,-1703936]),(⟨1,0,1⟩,[0,-1024,41984,-485376,2697216,-8451072,15332352,-14966784,6094848]),(⟨1,0,2⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨1,0,3⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨1,0,4⟩,[0,0,-8192,106496,-385024,417792]),(⟨1,1,0⟩,[0,-1024,41984,-485376,2697216,-8451072,15332352,-14966784,6094848]),(⟨1,1,1⟩,[1024,-23552,233472,-1349632,4858880,-10447872,12191744,-5988352]),(⟨1,1,2⟩,[0,-5120,87040,-559104,1894400,-3417088,2524160]),(⟨1,1,3⟩,[-1024,21504,-157696,485376,-644096,295936]),(⟨1,1,4⟩,[0,8192,-106496,385024,-417792]),(⟨1,2,0⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨1,2,1⟩,[0,-5120,87040,-559104,1894400,-3417088,2524160]),(⟨1,2,2⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨1,3,0⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨1,3,1⟩,[-1024,21504,-157696,485376,-644096,295936]),(⟨1,4,0⟩,[0,0,-8192,106496,-385024,417792]),(⟨1,4,1⟩,[0,8192,-106496,385024,-417792]),(⟨2,0,0⟩,[-512,12288,-105984,421888,-691712,-552960,4181504,-6148096,2883584]),(⟨2,0,1⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨2,0,2⟩,[512,-11264,82432,-227328,243200,-211968,321024]),(⟨2,0,3⟩,[0,-4096,57344,-212992,204800,86016]),(⟨2,1,0⟩,[0,3072,-50176,256000,-411648,-500736,2362368,-2183168]),(⟨2,1,1⟩,[0,-5120,87040,-559104,1894400,-3417088,2524160]),(⟨2,1,2⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨2,2,0⟩,[512,-11264,82432,-227328,243200,-211968,321024]),(⟨2,2,1⟩,[0,-2048,40960,-274432,696320,-591872]),(⟨2,2,2⟩,[1024,-20480,137216,-348160,295936]),(⟨2,3,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨3,0,0⟩,[0,7168,-121856,780288,-2488320,4090880,-2812928,20480]),(⟨3,0,1⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨3,0,2⟩,[0,-4096,57344,-212992,204800,86016]),(⟨3,0,3⟩,[0,0,32768,-196608,294912]),(⟨3,1,0⟩,[0,1024,-46080,403456,-1370112,2036736,-1156096]),(⟨3,1,1⟩,[-1024,21504,-157696,485376,-644096,295936]),(⟨3,2,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨3,3,0⟩,[0,0,32768,-196608,294912]),(⟨4,0,0⟩,[256,-5632,16128,150528,-938240,1845760,-1265408]),(⟨4,0,1⟩,[0,0,-8192,106496,-385024,417792]),(⟨4,1,0⟩,[0,0,-8192,106496,-385024,417792]),(⟨4,1,1⟩,[0,8192,-106496,385024,-417792]),(⟨5,0,0⟩,[0,-4096,57344,-212992,204800,86016]),(⟨6,0,0⟩,[0,0,16384,-98304,147456])]


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
    (Poly.add (Poly.scale (K.ofRat r114) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 10 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r113*r113 : ℚ)=r114 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 10 10 r113 r113 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 10=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 10 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C140

#print axioms Coulomb8.Columns.C140.sound
