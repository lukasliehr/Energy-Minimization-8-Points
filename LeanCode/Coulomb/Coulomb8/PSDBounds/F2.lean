import Coulomb8.BlockMatrix
import Coulomb8.FinitePositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.PSDBounds.F2

def preconditioner : Matrix (Fin 4) (Fin 4) ℤ := ![![7352534713242,0,0,0],![-10275459341398,53412787235932,0,0],![17965688153242,-89302578378484,5665105453179,0],![-13706958755032,-25527761831770,-21951762253112,24028214803421]]
def boxes : Fin 4 → Fin 4 → Dyadic := ![![⟨7609654356714669633229968758898950144,7609654359190549711800729308697198592⟩,⟨1463932101983765512957377691821015040,1463932104459645591528138241619263488⟩,⟨-1055543593430577777819771987854098432,-1055543590954697699249011438055849984⟩,⟨4931913895792493357252854480321380352,4931913898268373435823615030119628800⟩],![⟨1463932101983765512957377691821015040,1463932104459645591528138241619263488⟩,⟨425823190419148639529736361534816256,425823192895028718100496911333064704⟩,⟨2069963462152237588378310380493996032,2069963464628117666949070930292244480⟩,⟨3178584692793871163234801047950065664,3178584695269751241805561597748314112⟩],![⟨-1055543593430577777819771987854098432,-1055543590954697699249011438055849984⟩,⟨2069963462152237588378310380493996032,2069963464628117666949070930292244480⟩,⟨48795638362318618592621064193503657984,48795638364794498671191824743301906432⟩,⟨46175860470893819470326304822733570048,46175860473369699548897065372531818496⟩],![⟨4931913895792493357252854480321380352,4931913898268373435823615030119628800⟩,⟨3178584692793871163234801047950065664,3178584695269751241805561597748314112⟩,⟨46175860470893819470326304822733570048,46175860473369699548897065372531818496⟩,⟨49088363792720499565046264680358608896,49088363795196379643617025230156857344⟩]]

theorem contains (w : Fin 192 → ℝ)
    (h : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (i j : Fin 4) : (boxes i j).Contains (Data.F2.matrixFrom w i j) := by
  fin_cases i <;> fin_cases j
  · exact centerBox_contains w h 25
  · exact centerBox_contains w h 26
  · exact centerBox_contains w h 27
  · exact centerBox_contains w h 28
  · exact centerBox_contains w h 26
  · exact centerBox_contains w h 29
  · exact centerBox_contains w h 30
  · exact centerBox_contains w h 31
  · exact centerBox_contains w h 27
  · exact centerBox_contains w h 30
  · exact centerBox_contains w h 32
  · exact centerBox_contains w h 33
  · exact centerBox_contains w h 28
  · exact centerBox_contains w h 31
  · exact centerBox_contains w h 33
  · exact centerBox_contains w h 34

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
    (Data.F2.matrixFrom w).PosDef := by
  apply posDef_of_entry_bounds (Dyadic.scaledMatrix preconditioner) _ (by decide)
    (Data.F2.matrixFrom_symm w)
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

end Coulomb8.PSDBounds.F2

#print axioms Coulomb8.PSDBounds.F2.positive
