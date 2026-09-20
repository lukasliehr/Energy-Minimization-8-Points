import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C016

def r0 : ℚ := { num := -256, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 256, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 256, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 256, den := 15, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -2816, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -256, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -1024, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 1024, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 768, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -768, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 2304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1024, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 3072, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1536, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 1536, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -4608, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -3072, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[],[r0,r1,r2,r3],[],[r4,r5,r6,r7],[],[r8,r9],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r10,r11,r12,-256],[],[],[],[],[],[],[],[],[r13,r14],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r15,r16,r17,512],[],[],[],[],[],[],[],[],[],[r9,r18],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F1.upperColumn 1 2)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F1.upperColumn 1 2).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C016

#print axioms Coulomb8.Columns.C016.sound
