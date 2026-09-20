import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C035

def r0 : ℚ := { num := -1, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[1],[-6],[-1],[8],[1],[],[r0],[],[],[],[],[],[],[6],[6],[-6],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-2],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[-24],[],[],[],[],[],[],[],[],[18],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F3.upperColumn 0 0)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F3.upperColumn 0 0).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C035

#print axioms Coulomb8.Columns.C035.sound
