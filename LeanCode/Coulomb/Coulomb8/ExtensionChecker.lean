import Coulomb8.ExtensionData
import Coulomb8.GramIntervals

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8

def tripleCode (u v t : Fin 4) : ℕ := 16*u.val+4*v.val+t.val

def anchors (u v t : Fin 4) : Fin 8 × Fin 8 × Fin 8 :=
  ExtensionData.anchors.getD (tripleCode u v t) (0,1,2)

def extensionWitness (u v t a b c : Fin 4) : Fin 8 :=
  ((ExtensionData.witnesses.getD (tripleCode u v t) []).getD (tripleCode a b c) 0)

abbrev BaseCompatible (u v t : Fin 4) : Prop :=
  let z := anchors u v t
  z.1 ≠ z.2.1 ∧ z.1 ≠ z.2.2 ∧ z.2.1 ≠ z.2.2 ∧
    (candidateCode z.1 z.2.1).val=u.val+1 ∧
    (candidateCode z.1 z.2.2).val=v.val+1 ∧
    (candidateCode z.2.1 z.2.2).val=t.val+1

abbrev ExtensionCompatible (u v t a b c : Fin 4) : Prop :=
  let z := anchors u v t
  let w := extensionWitness u v t a b c
  w ≠ z.1 ∧ w ≠ z.2.1 ∧ w ≠ z.2.2 ∧
    (candidateCode z.1 w).val=a.val+1 ∧
    (candidateCode z.2.1 w).val=b.val+1 ∧
    (candidateCode z.2.2 w).val=c.val+1


abbrev extensionCheck (u v t r s w : Fin 4) : Prop :=
  (BaseCompatible u v t ∧ ExtensionCompatible u v t r s w) ∨
    (gramResidualBox (nodeDyadic u) (nodeDyadic v) (nodeDyadic t)
      (nodeDyadic r) (nodeDyadic s) (nodeDyadic w)).Separated

theorem extensionCheck_sound (u v t r s w : Fin 4) (hc : extensionCheck u v t r s w)
    (hr : Thomson8.gramResidual (nodes a u) (nodes a v) (nodes a t)
      (nodes a r) (nodes a s) (nodes a w)=0) :
    BaseCompatible u v t ∧ ExtensionCompatible u v t r s w := by
  rcases hc with h | h
  · exact h
  · exfalso
    exact Dyadic.nonzero_of_contains (gramResidualBox_contains (nodeDyadic_contains u)
      (nodeDyadic_contains v) (nodeDyadic_contains t) (nodeDyadic_contains r)
      (nodeDyadic_contains s) (nodeDyadic_contains w)) h hr

theorem contact_gramDet3_nonzero (u v t : Fin 4) :
    Thomson8.gramDet3 (nodes a u) (nodes a v) (nodes a t) ≠ 0 := by
  apply Dyadic.nonzero_of_contains (gramDetBox_contains (nodeDyadic_contains u)
    (nodeDyadic_contains v) (nodeDyadic_contains t))
  fin_cases u <;> fin_cases v <;> fin_cases t <;> decide +kernel

end Coulomb8
