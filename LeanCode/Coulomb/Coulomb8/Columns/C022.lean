import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C022

def r0 : ℚ := { num := 16384, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -262144, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 65536, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -1048576, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1933312, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -10747904, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 7143424, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -524288, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 16384, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 32768, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -98304, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 2916352, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -26902528, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 47218688, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -3178496, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 5144576, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -32768, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 131072, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -360448, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 10010624, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -5832704, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 1359872, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -40861696, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 4308992, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 524288, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -16384, den := 147, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -32768, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 98304, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2916352, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 26902528, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -47218688, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 3178496, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -5144576, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 32768, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -49152, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 98304, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -3883008, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 65536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -3817472, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 98304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -16384, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 524288, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -131072, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 2097152, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -3866624, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 21495808, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -14286848, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 1048576, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -32768, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -98304, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 294912, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -8749056, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 26902528, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -47218688, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 9535488, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -5144576, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 32768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -294912, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 589824, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -23298048, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 393216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -22904832, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 589824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -524288, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 131072, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -2097152, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 3866624, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -21495808, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 14286848, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1048576, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 32768, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 98304, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -294912, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 8749056, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -26902528, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 47218688, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -9535488, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 5144576, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -32768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 294912, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -589824, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 23298048, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -393216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 22904832, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -589824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[],[],[],[],[r0,r1,r2,r3,r4,r5,r6,r7,r8],[r9,r10,r11,r12,r13,r14,r15,r16],[r17,r18,r19,r20,r21,r22,r23,r24,r25],[r26,r27,r28,r29,r30,r31,r32,r33],[r34,r35,r36,r37,r38,r39,r40],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r26,r41,r42,r43,r44,r45,r46,r47,r48],[r49,r50,r51,r52,r53,r54,r55,r56],[],[],[],[r57,r58,r59,r60,r61,r62,-32768],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r9,r63,r64,r65,r66,r67,r68,r69,r70],[r71,r72,r73,r74,r75,r76,r77,r78],[],[],[],[],[r79,r80,r81,r82,r83,r84,32768],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F1.upperColumn 3 3)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F1.upperColumn 3 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C022

#print axioms Coulomb8.Columns.C022.sound
