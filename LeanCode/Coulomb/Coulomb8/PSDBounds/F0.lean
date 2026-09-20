import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.F0

def preconditioner : Matrix (Fin 4) (Fin 4) ℤ := ![![4603609864174,0,0,0],![416240355533,5144127102021,0,0],![74204511522705,-46537256987437,58503327661134,0],![3539594023811,45926772216245,31995492433174,93060087235435]]
def boxes : Fin 4 → Fin 4 → Dyadic := ![![⟨19410739184604912082275384321906835456,19410739187080792160846144871705083904⟩,⟨-1570632456391578226268071927509680128,-1570632453915698147697311377711431680⟩,⟨-25869594198421495552138138422786129920,-25869594195945615473567377872987881472⟩,⟨8931201039503443746349878988245041152,8931201041979323824920639538043289600⟩],![⟨-1570632456391578226268071927509680128,-1570632453915698147697311377711431680⟩,⟨15672983258302319073376928908439453696,15672983260778199151947689458237702144⟩,⟨14459445258444227135923915776931659776,14459445260920107214494676326729908224⟩,⟨-12646530186350328396875233618099699712,-12646530183874448318304473068301451264⟩],![⟨-25869594198421495552138138422786129920,-25869594195945615473567377872987881472⟩,⟨14459445258444227135923915776931659776,14459445260920107214494676326729908224⟩,⟨44434655177185539548128432065368555520,44434655179661419626699192615166803968⟩,⟨-21429342274286403466758892138868506624,-21429342271810523388188131589070258176⟩],![⟨8931201039503443746349878988245041152,8931201041979323824920639538043289600⟩,⟨-12646530186350328396875233618099699712,-12646530183874448318304473068301451264⟩,⟨-21429342274286403466758892138868506624,-21429342271810523388188131589070258176⟩,⟨13316819528019140302531309421486669824,13316819530495020381102069971284918272⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 4) : (boxes i j).Contains (Data.F0.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 0
  · exact centerBox_contains w h 1
  · exact centerBox_contains w h 2
  · exact centerBox_contains w h 3
  · exact centerBox_contains w h 1
  · exact centerBox_contains w h 4
  · exact centerBox_contains w h 5
  · exact centerBox_contains w h 6
  · exact centerBox_contains w h 2
  · exact centerBox_contains w h 5
  · exact centerBox_contains w h 7
  · exact centerBox_contains w h 8
  · exact centerBox_contains w h 3
  · exact centerBox_contains w h 6
  · exact centerBox_contains w h 8
  · exact centerBox_contains w h 9

theorem checked0_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 4) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 4) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 4) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked0_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 0 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (0 : Fin 4) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 4) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 4) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 4) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked1_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 1 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (1 : Fin 4) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 4) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 4) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 4) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked2_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 2 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (2 : Fin 4) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_0 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 0 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 4) 0) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_1 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 1 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 4) 1) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_2 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 2 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 4) 2) (2^80) ≤ 2^203 := by decide +kernel

theorem checked3_3 : Dyadic.errorNumerator
    (List.ofFn (fun k => List.ofFn (fun l => preconditioner 3 k*preconditioner 3 l))).flatten
    (List.ofFn (fun k => List.ofFn (boxes k))).flatten
    (Dyadic.identityBox (3 : Fin 4) 3) (2^80) ≤ 2^203 := by decide +kernel

theorem positive (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) :
    (Data.F0.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.F0.matrixFrom_symm w)
  intro i j
  apply Dyadic.congruence_entry_bound _ _ boxes (contains w h)
  fin_cases i <;> fin_cases j
  · exact checked0_0
  · exact checked0_1
  · exact checked0_2
  · exact checked0_3
  · exact checked1_0
  · exact checked1_1
  · exact checked1_2
  · exact checked1_3
  · exact checked2_0
  · exact checked2_1
  · exact checked2_2
  · exact checked2_3
  · exact checked3_0
  · exact checked3_1
  · exact checked3_2
  · exact checked3_3

end Coulomb8.PSDBounds.F0

#print axioms Coulomb8.PSDBounds.F0.positive
