import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C006

def r0 : ℚ := { num := -6, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 46, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 620, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -1080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1070, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 2, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -10, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 40, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 16, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,-32,r2,r3,r4,-80,r5],[],[r6,r7,r8,-20,r8,r7],[],[],[-2,r9,-8],[],[r6],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[2],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F0.upperColumn 1 3)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F0.upperColumn 1 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C006

#print axioms Coulomb8.Columns.C006.sound
