import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C009

def r0 : ℚ := { num := 1, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -10, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 65, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -260, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 740, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -1410, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -200, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 25, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 2, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -10, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 40, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,250,-200,100,r6,r7],[],[],[],[],[r8,r9,r10,-20,r10,r9],[],[],[],[],[r11],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[2],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F0.upperColumn 3 3)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F0.upperColumn 3 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C009

#print axioms Coulomb8.Columns.C009.sound
