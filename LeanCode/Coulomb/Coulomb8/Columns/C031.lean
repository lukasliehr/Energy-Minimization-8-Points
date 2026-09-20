import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C031

def r0 : ℚ := { num := 64, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 1408, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -2944, den := 15, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1344, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -704, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -256, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 1024, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -3712, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 2176, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -2688, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1408, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 64, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1088, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 3200, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1408, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -128, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 384, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -128, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 128, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -64, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -1408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 2944, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -4032, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 2112, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 192, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -2112, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 2304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -3584, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 4032, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -2112, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -128, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 1152, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 64, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1408, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -2944, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -2304, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 256, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 5632, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -11776, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 16128, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -8448, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -256, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -5632, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 11776, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -16128, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 8448, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 2304, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 512, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -4608, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[],[r0,r1,r2,r3,r4,r5],[],[r6,r7,r8,r9,r10,r11],[],[r12,r13,r14,r15,r4,r5],[],[r16,r17,r18,r19],[],[],[],[],[r20,r21,r22,r23,r24,r25],[],[r26,r27,r28,r29,r30,r31],[],[r32,r33,-128,128],[],[],[],[],[],[],[r34,r35,r36,r37,r30,r31],[],[],[],[],[],[],[],[],[r20,r26,r38,r39,r30,r31],[],[r32,r33,-128,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r40,r41,r42,r43,r44,r45],[r46,r47,r48,r49,r50,r51],[r46,r52,-256,256],[r53,r54,512,-512],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F2.upperColumn 1 3)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F2.upperColumn 1 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C031

#print axioms Coulomb8.Columns.C031.sound
