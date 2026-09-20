import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C036

def r0 : ℚ := { num := -32, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 96, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -32, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -32, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 32, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 32, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -288, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -96, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 288, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 32, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 32, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -32, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 576, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -1728, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 192, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -576, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 3744, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -3456, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -384, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -864, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 448, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -3744, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 3456, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 96, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -672, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 4576, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1728, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -192, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -12672, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 7488, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -288, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 2016, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -13728, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -288, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 864, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -1728, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[r0,r1,r2,r3],[r4,r5,r6],[r1,r7,r4,r8],[r9,r10,-32],[r9,r11,r0,r12],[r1,r13,32],[r4,r9,r14,r15],[r0,r16,r17],[],[],[],[],[r18,r19,r20,r10],[r21,r22,r23,r24],[r25,r26,r27,-32],[r18,r28,r29,r30],[r7,r31,-96],[],[],[],[],[],[],[],[r32,r33,r34,r30],[],[],[],[],[],[],[],[r21,r35,-192],[r1,r7,r4,r8],[r9,r10,-32],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r21,r36,r37,r13],[],[],[],[],[],[],[],[],[r31,r38,r39,r40],[r41,r42,r43,r44],[r45,r46,288],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F3.upperColumn 0 1)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F3.upperColumn 0 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C036

#print axioms Coulomb8.Columns.C036.sound
