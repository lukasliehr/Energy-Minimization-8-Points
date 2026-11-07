import AllS.Units.N_FI.N_contact_order.N_ordered_contacts

noncomputable section
namespace Blueprint.Thomson.Finite

theorem contact_order_no_opposites_indices (a : ℝ) (ha : physical a) (i j : Fin 4) :
    contacts a i ≠ 0 ∧ contacts a i + contacts a j ≠ 0 := by
  obtain ⟨hD, hDB, hB, hC, hCA, hA, hsum, hsumneg⟩ :=
    contact_order_ordered_contacts a ha
  change -1 < -a-(1-a)/√2 at hD
  change -a-(1-a)/√2 < 2*a-1 at hDB
  change 2*a-1 < 0 at hB
  change 0 < -a+(1-a)/√2 at hC
  change -a+(1-a)/√2 < a at hCA
  change a+(2*a-1) < 0 at hsumneg
  fin_cases i <;> fin_cases j <;> constructor <;> intro he <;>
    norm_num [contacts] at he <;> linarith

theorem contact_order_no_opposites (a x y : ℝ) (ha : physical a)
    (hx : x ∈ Set.range (contacts a)) (hy : y ∈ Set.range (contacts a)) :
    x ≠ 0 ∧ x+y ≠ 0 := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact contact_order_no_opposites_indices a ha i j

#check contact_order_no_opposites
#print axioms contact_order_no_opposites
end Blueprint.Thomson.Finite
