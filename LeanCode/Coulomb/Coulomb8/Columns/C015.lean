import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C015

def r0 : ℚ := { num := 49152, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -98304, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 3883008, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -65536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 3817472, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -98304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 16384, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -180224, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1998848, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -49152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 11337728, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -4734976, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 98304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -16384, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 131072, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -262144, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 786432, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -4456448, den := 735, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 131072, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -262144, den := 3675, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 524288, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -786432, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -294912, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 589824, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -23298048, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 393216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -22904832, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 589824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 393216, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -786432, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 14155776, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -4456448, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 393216, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -524288, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 3145728, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -4718592, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 884736, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -1769472, den := 175, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 69894144, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -1179648, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 68714496, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -1769472, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 1572864, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -28311552, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 8912896, den := 245, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -786432, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -3145728, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 4718592, den := 1225, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[r0,r1,r2,r3,r4,r5,r6],[],[r7,r8,r9,r10,r11,r12,r13],[],[r14,r15,r16,r17,r18],[],[r19,r20,r21],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r22,r23,r24,r25,r26,r27,-32768],[],[r28,r29,r30,r31,r32],[],[],[],[],[],[],[],[],[],[],[],[],[],[r33,r34,r35],[],[],[],[],[],[],[],[],[r36,r37,r38,r39,r40,r41,98304],[],[r21,r42,r43,r44,r45],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r20,r46,r47],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F1.upperColumn 1 1)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F1.upperColumn 1 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C015

#print axioms Coulomb8.Columns.C015.sound
