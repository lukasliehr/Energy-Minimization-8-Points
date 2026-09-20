import Coulomb8.Data
import Coulomb8.CoefficientBasis

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C026

def r0 : ℚ := { num := 128, den := 21, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 640, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -640, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1024, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -512, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 512, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -384, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1408, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -128, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 128, den := 3, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 512, den := 105, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -512, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -128, den := 5, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 4992, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 512, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -1536, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 384, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -9216, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 2048, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -6144, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -2048, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 6144, den := 35, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[],[r0,r1,r2,r3],[],[0,r4,r5,r6],[],[r7,r8,r9,r10],[],[r11,r12],[],[],[],[],[],[],[r13,r14,-384,384],[],[r15,r16],[],[],[],[],[],[],[],[],[r17,r7,-128,128],[],[],[],[],[],[],[],[],[r15,r16],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r4,r18,1024,-1024],[],[],[],[],[],[],[],[],[r19,r20],[r21,r22],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

theorem checked :
    (Poly.add (Data.F2.upperColumn 0 1)
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.F2.upperColumn 0 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Poly.eval_eq_of_check _ _ checked u v t

end Coulomb8.Columns.C026

#print axioms Coulomb8.Columns.C026.sound
