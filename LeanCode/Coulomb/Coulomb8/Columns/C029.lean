import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C029

def r0 : ℚ := { num := 1, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -2, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[],[r0],[],[r1],[],[r0],[],[],[],[],[],[],[-2],[],[2],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[2],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[4],[],[],[],[],[],[],[],[],[-8],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F2.upperColumn 1 1)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F2.upperColumn 1 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C029

#print axioms Coulomb8.Columns.C029.sound
