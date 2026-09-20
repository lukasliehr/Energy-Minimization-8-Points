import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.F3

def preconditioner : Matrix (Fin 3) (Fin 3) ℤ := ![![12485390236122,0,0],![-4173587275120,8162135311640,0],![41631417394997,-116734963832990,69501906571543]]
def boxes : Fin 3 → Fin 3 → Dyadic := ![![⟨2638972447807487273159347063517872128,2638972450283367351730107613316120576⟩,⟨1349399562993795820089229444112187392,1349399565469675898659989993910435840⟩,⟨685707026923644597377644662343335936,685707029399524675948405212141584384⟩],![⟨1349399562993795820089229444112187392,1349399565469675898659989993910435840⟩,⟨6864918116569170096698056335576530944,6864918119045050175268816885374779392⟩,⟨10721987185407125401861133880734515200,10721987187883005480431894430532763648⟩],![⟨685707026923644597377644662343335936,685707029399524675948405212141584384⟩,⟨10721987185407125401861133880734515200,10721987187883005480431894430532763648⟩,⟨17683007708129357865456835486824792064,17683007710605237944027596036623040512⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 3) : (boxes i j).Contains (Data.F3.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 35
  · exact centerBox_contains w h 36
  · exact centerBox_contains w h 37
  · exact centerBox_contains w h 36
  · exact centerBox_contains w h 38
  · exact centerBox_contains w h 39
  · exact centerBox_contains w h 37
  · exact centerBox_contains w h 39
  · exact centerBox_contains w h 40

theorem checked0_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 3) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 3) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 3) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 3) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 3) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 3) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 3) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 3) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 3) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem positive (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) :
    (Data.F3.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.F3.matrixFrom_symm w)
  intro i j
  apply Dyadic.congruence_entry_bound _ _ boxes (contains w h)
  fin_cases i <;> fin_cases j
  · exact checked0_0
  · exact checked0_1
  · exact checked0_2
  · exact checked1_0
  · exact checked1_1
  · exact checked1_2
  · exact checked2_0
  · exact checked2_1
  · exact checked2_2

end Coulomb8.PSDBounds.F3

#print axioms Coulomb8.PSDBounds.F3.positive
