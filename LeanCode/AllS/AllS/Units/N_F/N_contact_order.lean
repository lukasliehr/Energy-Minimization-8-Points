import AllS.Units.N_FI.N_contact_order.N_no_opposites
import AllS.Units.N_FI.N_contact_order.N_orbit_table
import AllS.Units.N_F.N_definitions

noncomputable section
namespace Blueprint.Thomson.Finite

theorem contact_order (a : ℝ) (ha : physical a) :
    (-1 < contacts a 3 ∧ contacts a 3 < contacts a 1 ∧ contacts a 1 < 0 ∧
      0 < contacts a 2 ∧ contacts a 2 < contacts a 0 ∧ contacts a 0 < 1 ∧
      contacts a 0 + contacts a 1 = 3*a-1 ∧ contacts a 0 + contacts a 1 < 0) ∧
    (∀ i j : Fin 4, contacts a i ≠ 0 ∧ contacts a i+contacts a j ≠ 0) ∧
    (∀ r, (contactRealOrbit a r).card = contactOrbitSize r) ∧
    (∀ r t, r ≠ t → Disjoint (contactRealOrbit a r) (contactRealOrbit a t)) ∧
    (Finset.univ.biUnion (contactRealOrbit a)).card = 21 :=
  ⟨contact_order_ordered_contacts a ha, contact_order_no_opposites_indices a ha,
    contact_order_orbit_table a ha⟩

#check contact_order
#print axioms contact_order
end Blueprint.Thomson.Finite
