import AllS.Units.N_FI.N_no_antipodes.N_exclude

namespace Blueprint.Thomson.Finite

theorem no_antipodal_equality_pair (a : ℝ) (Y : Fin 8 → Point) (ha : physical a)
    (hY : IsConfiguration Y) (hallowed : AllowedContacts a Y) :
    ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ≠ -1 ∧
      inner ℝ (Y i) (Y j) ∈ Set.range (contacts a) := by
  intro i j hij
  have hc := no_antipodes_exclude a Y ha hY hallowed i j hij
  refine ⟨?_,hc⟩
  obtain ⟨k,hk⟩ := hc
  rw [← hk]
  obtain ⟨hD,hDB,hB,hC,hCA,hA,_,_⟩ := contact_order_ordered_contacts a ha
  change -1 < -a-(1-a)/√2 at hD
  change -a-(1-a)/√2 < 2*a-1 at hDB
  change 0 < -a+(1-a)/√2 at hC
  change -a+(1-a)/√2 < a at hCA
  fin_cases k <;> norm_num [contacts] at * <;> linarith

#check no_antipodal_equality_pair
#print axioms no_antipodal_equality_pair
end Blueprint.Thomson.Finite
