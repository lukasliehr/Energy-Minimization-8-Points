import AllS.Units.N_FI.N_contact_order.N_ordered_contacts

namespace Blueprint.Thomson.Finite

/-- AAB, ACC, ADD, ACD, BCD in the fixed A,B,C,D label order. -/
def contactRepresentative : Fin 5 → Fin 3 → Fin 4 :=
  ![![0,0,1], ![0,2,2], ![0,3,3], ![0,2,3], ![1,2,3]]

def contactLabelOrbit (r : Fin 5) : Finset (Fin 3 → Fin 4) :=
  Finset.univ.image (fun (σ : Equiv.Perm (Fin 3)) i => contactRepresentative r (σ i))

def contactOrbitSize : Fin 5 → ℕ := ![3,3,3,6,6]

theorem contactLabelOrbit_card : ∀ r, (contactLabelOrbit r).card = contactOrbitSize r := by
  decide

theorem contactLabelOrbit_disjoint : ∀ r t, r ≠ t →
    Disjoint (contactLabelOrbit r) (contactLabelOrbit t) := by
  decide

theorem contactLabelOrbit_union_card : (Finset.univ.biUnion contactLabelOrbit).card = 21 := by
  decide

noncomputable section

def contactTripleEval (a : ℝ) (v : Fin 3 → Fin 4) : Fin 3 → ℝ := fun i => contacts a (v i)

def contactRealOrbit (a : ℝ) (r : Fin 5) : Finset (Fin 3 → ℝ) :=
  (contactLabelOrbit r).image (contactTripleEval a)

theorem contacts_injective (a : ℝ) (ha : physical a) : Function.Injective (contacts a) := by
  obtain ⟨hD,hDB,hB,hC,hCA,hA,hsum,hsumneg⟩ := contact_order_ordered_contacts a ha
  change -a-(1-a)/√2 < 2*a-1 at hDB
  change 2*a-1 < 0 at hB
  change 0 < -a+(1-a)/√2 at hC
  change -a+(1-a)/√2 < a at hCA
  intro i j hij
  by_contra hne
  fin_cases i <;> fin_cases j <;> norm_num [contacts] at hij hne <;> linarith

theorem contactTripleEval_injective (a : ℝ) (ha : physical a) :
    Function.Injective (contactTripleEval a) := by
  intro v w hvw
  funext i
  apply contacts_injective a ha
  exact congrFun hvw i

theorem contactRealOrbit_card (a : ℝ) (ha : physical a) (r : Fin 5) :
    (contactRealOrbit a r).card = contactOrbitSize r := by
  rw [contactRealOrbit, Finset.card_image_of_injective _ (contactTripleEval_injective a ha)]
  exact contactLabelOrbit_card r

theorem contactRealOrbit_disjoint (a : ℝ) (ha : physical a) (r t : Fin 5) (hrt : r ≠ t) :
    Disjoint (contactRealOrbit a r) (contactRealOrbit a t) := by
  exact (Finset.disjoint_image (contactTripleEval_injective a ha)).2
    (contactLabelOrbit_disjoint r t hrt)

theorem contactRealOrbit_union_image (a : ℝ) :
    Finset.univ.biUnion (contactRealOrbit a) =
    (Finset.univ.biUnion contactLabelOrbit).image (contactTripleEval a) := by
  classical
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, contactRealOrbit, Finset.mem_image]
  constructor
  · rintro ⟨r,w,hw,rfl⟩
    exact ⟨w,⟨r,hw⟩,rfl⟩
  · rintro ⟨w,⟨r,hw⟩,rfl⟩
    exact ⟨r,w,hw,rfl⟩

theorem contact_order_orbit_table (a : ℝ) (ha : physical a) :
    (∀ r, (contactRealOrbit a r).card = contactOrbitSize r) ∧
    (∀ r t, r ≠ t → Disjoint (contactRealOrbit a r) (contactRealOrbit a t)) ∧
    (Finset.univ.biUnion (contactRealOrbit a)).card = 21 := by
  refine ⟨contactRealOrbit_card a ha, contactRealOrbit_disjoint a ha, ?_⟩
  rw [contactRealOrbit_union_image, Finset.card_image_of_injective _ (contactTripleEval_injective a ha)]
  exact contactLabelOrbit_union_card

#check contact_order_orbit_table
#print axioms contact_order_orbit_table
end
end Blueprint.Thomson.Finite
