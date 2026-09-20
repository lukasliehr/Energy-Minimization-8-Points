import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.S7_odd

def preconditioner : Matrix (Fin 3) (Fin 3) ℤ := ![![1299517903677,0,0],![-87401510050169,93755573942906,0],![22055886766164,32795244034119,128748228646512]]
def boxes : Fin 3 → Fin 3 → Dyadic := ![![⟨243598474157615450382041620154366820352,243598474160091330460612380704165068800⟩,⟨227089159522933377383431985599306792960,227089159525409257462002746149105041408⟩,⟨-99575931269039577357350157940787511296,-99575931266563697278779397390989262848⟩],![⟨227089159522933377383431985599306792960,227089159525409257462002746149105041408⟩,⟨211745524822737253125004484035230040064,211745524825213133203575244585028288512⟩,⟨-92839327374362730601044430723041198080,-92839327371886850522473670173242949632⟩],![⟨-99575931269039577357350157940787511296,-99575931266563697278779397390989262848⟩,⟨-92839327374362730601044430723041198080,-92839327371886850522473670173242949632⟩,⟨40731582214788301141297216504427708416,40731582217264181219867977054225956864⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 3) : (boxes i j).Contains (Data.S7_odd.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 186
  · exact centerBox_contains w h 187
  · exact centerBox_contains w h 188
  · exact centerBox_contains w h 187
  · exact centerBox_contains w h 189
  · exact centerBox_contains w h 190
  · exact centerBox_contains w h 188
  · exact centerBox_contains w h 190
  · exact centerBox_contains w h 191

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
    (Data.S7_odd.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.S7_odd.matrixFrom_symm w)
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

end Coulomb8.PSDBounds.S7_odd

#print axioms Coulomb8.PSDBounds.S7_odd.positive
