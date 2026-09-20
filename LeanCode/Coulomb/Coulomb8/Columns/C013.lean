import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C013

def r0 : ℚ := { num := -256, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 2048, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -1536, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 4096, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -256, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -256, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 256, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 256, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 256, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -2048, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1536, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -4096, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 256, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 256, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -256, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -256, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 2048, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -4608, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 4096, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -512, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 3328, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -6912, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 4864, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 768, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -768, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 2304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[],[r0,r1,r2,r3,r4],[r5,r6,r7,r8],[r9,r10,r11,r12,r13],[r14,r15,r16,r17],[],[],[],[],[],[],[],[],[r5,r18,r19,r20,r21],[r22,r23,r24,r25,r26],[r27,r28,r29,-256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F1.upperColumn 0 3)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F1.upperColumn 0 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C013

#print axioms Coulomb8.Columns.C013.sound
