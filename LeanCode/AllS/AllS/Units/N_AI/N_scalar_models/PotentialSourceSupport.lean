import AllS.Units.N_AI.N_scalar_models.N_entire_identity
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_F.N_contact_order

noncomputable section
namespace Blueprint.CAP
open Blueprint.Thomson.Finite

def sourceContactValues (a : ℝ) : Fin 5 → ℝ :=
  ![contacts a 0,contacts a 1,contacts a 2,contacts a 3,-1]

theorem sourceContactValues_lt_one (a : ℝ) (ha : physical a) (j : Fin 5) :
    sourceContactValues a j < 1 := by
  obtain ⟨hD,hDB,hB,hC,hCA,hA,hAB,hABn⟩ := contact_order_ordered_contacts a ha
  fin_cases j
  · exact hA
  · exact hB.trans (by norm_num)
  · exact hCA.trans hA
  · exact hDB.trans (hB.trans (by norm_num))
  · norm_num [sourceContactValues]

theorem potentialSourceValue (s t : ℝ) (hs : 0 ≤ s) (ht : t < 1) :
    (-(Real.log (2-2*t))/2)*entirePsi (s*(-(Real.log (2-2*t))/2)) =
      potentialJet s 0 t := scalar_models_entire_identity s t hs ht

theorem potentialSourceFirst (s t : ℝ) (ht : t < 1) :
    Real.exp ((-s/2-1)*Real.log (2-2*t)) = potentialJet s 1 t := by
  rw [potentialJet_one,Real.rpow_def_of_pos (by linarith : 0<2-2*t)]
  congr 1
  ring

theorem potentialSourceRecurrence (s t : ℝ) (m : ℕ) (ht : t < 1) :
    ((s+2*((m:ℝ)+1))*potentialJet s (m+1) t)/(2-2*t) =
      potentialJet s (m+2) t := by
  rw [potentialJet_recurrence s t m ht]
  ring

#print axioms sourceContactValues_lt_one
#print axioms potentialSourceValue
#print axioms potentialSourceFirst
#print axioms potentialSourceRecurrence
end Blueprint.CAP
