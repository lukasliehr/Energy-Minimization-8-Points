import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C028

def r0 : ℚ := { num := 4096, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -32768, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 32768, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -2555904, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 4513792, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -753664, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 16842752, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -8192, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 278528, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -548864, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 3244032, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -25616384, den := 525, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 55918592, den := 525, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -24305664, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 524288, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -180224, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -12288, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 32768, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -3309568, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 10682368, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -581632, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 1015808, den := 75, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -4784128, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 131072, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -45056, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 90112, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -16384, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 2613248, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -25591808, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 6447104, den := 525, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -6504448, den := 525, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 3055616, den := 525, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -32768, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 131072, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -2031616, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 131072, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -32768, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -8192, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 1179648, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -2392064, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 67371008, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -6733824, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 75104256, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -104300544, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 2359296, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -811008, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 12288, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1327104, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 9674752, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -35487744, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 9076736, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -4571136, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -1859584, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 393216, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -135168, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -24576, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 49152, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -794624, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 335872, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -32768, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 196608, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 1015808, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -12189696, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 5603328, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -7274496, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 3244032, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 393216, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -2031616, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 131072, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -98304, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 32768, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -786432, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 262144, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -61341696, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 36110336, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -18087936, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 134742016, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -3145728, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 1081344, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -65536, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -9895936, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 262144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -3473408, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -131072, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 2359296, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -4063232, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 85458944, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -26345472, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 29097984, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -12976128, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -1572864, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 8126464, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -524288, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 393216, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -3538944, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 6094848, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -128188416, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 39518208, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -43646976, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 19464192, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1572864, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -8126464, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 524288, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -393216, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[r0,r1,r2,r3,r4,r5,r6,-131072,45056],[],[r7,r8,r9,r10,r11,r12,r13,r14,r15],[],[r16,r17,r18,r19,r20,r21,r22,r23,r24],[],[r25,r26,r27,r28,r29,r30,r31],[],[r32,r33,r34,r35,r36],[],[],[],[],[],[],[],[],[],[],[],[],[],[r37,r38,r39,r40,r41,r42,r43,r44,r45],[],[r46,r47,r48,r49,r50,r51,r52,r53,r54],[],[r55,r56,r57,r36,r58,-16384,8192],[],[],[],[],[],[],[],[],[],[],[],[r59,r60,r61,r62,r63,r64,r65],[],[r59,r66,r67,r68,r69],[],[],[],[],[],[],[],[],[r70,r71,r72,r73,r74,r75,r76,r77,r78],[],[r79,r38,r80,r81,r82,131072,-65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[r83,r84,r85,r86,r87,r88,r89],[],[r33,r90,r91,r92,r93],[],[],[],[],[],[],[],[],[],[r60,r94,r95,r96,r97,r98,r99],[],[r83,r100,r101,r102,r103],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F2.upperColumn 0 3)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F2.upperColumn 0 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C028

#print axioms Coulomb8.Columns.C028.sound
