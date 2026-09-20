import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C001

def r0 : ℚ := { num := -6, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -24, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 16, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 2, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2],[-2,r3,-8],[r4],[r4],[],[],[],[],[],[],[],[],[],[],[2],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F0.upperColumn 0 1)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F0.upperColumn 0 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C001

#print axioms Coulomb8.Columns.C001.sound
