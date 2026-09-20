import Coulomb8.Data
import Coulomb8.Witness
import Coulomb8.Dyadic

namespace Coulomb8

noncomputable def coordinateValue (w : Fin 192 → ℝ) (c : ℕ) : ℝ :=
  if h : c<192 then w ⟨c,h⟩ else 0

noncomputable def Block.matrixFrom (b : Block) (w : Fin 192 → ℝ) : Matrix (Fin b.n) (Fin b.n) ℝ :=
  fun i j => coordinateValue w (b.coordinate i.val j.val)

theorem Block.matrixFrom_symm (b : Block) (w : Fin 192 → ℝ) (i j : Fin b.n) :
    b.matrixFrom w i j=b.matrixFrom w j i := by
  simp only [matrixFrom,coordinate,min_comm,max_comm]

def centerBox (c : Fin 192) : Dyadic :=
  ⟨Witness.centerNumerators c*2^32-2^90,Witness.centerNumerators c*2^32+2^90⟩

theorem integer_center_contains (n : ℤ) (x : ℝ)
    (h : |x-(n : ℝ)/(2^96 : ℝ)| ≤ (correctionRadius : ℝ)) :
    (⟨n*2^32-2^90,n*2^32+2^90⟩ : Dyadic).Contains x := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  norm_num [correctionRadius] at hl hu
  constructor <;> push_cast <;> norm_num [Dyadic.scale] <;> linarith

theorem centerBox_contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) (c : Fin 192) :
    (centerBox c).Contains (w c) :=
  integer_center_contains (Witness.centerNumerators c) (w c) (h c)

end Coulomb8

#print axioms Coulomb8.centerBox_contains
