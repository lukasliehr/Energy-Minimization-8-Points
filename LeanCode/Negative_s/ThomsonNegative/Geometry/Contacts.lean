import ThomsonNegative.Geometry.Base

noncomputable section


open Real
namespace ThomsonNegative.Geometry

/-- Exact packing endpoint facts from the quadratic equation for sqrt 2. -/
theorem packing_endpoint_bounds : 13/50 < aInf ∧ aInf < 1/3 ∧
    7*aInf^2+2*aInf-1=0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hl : (141/100 : ℝ) < √2 := by nlinarith
  have hu : √(2 : ℝ) < 3/2 := by nlinarith
  dsimp [aInf,limitingHeight]
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith

theorem contact_order_packing_bounds (a : ℝ) (hl : aInf < a) (hu : a < 1/3) :
    (13/50 < aInf ∧ aInf < a ∧ a < 1/3) ∧ 0 < 7*a^2+2*a-1 := by
  obtain ⟨hb, _, he⟩ := packing_endpoint_bounds
  refine ⟨⟨hb, hl, hu⟩, ?_⟩
  have hprod : 0 < (a-aInf)*(7*a+7*aInf+2) :=
    mul_pos (sub_pos.mpr hl) (by linarith)
  nlinarith

end ThomsonNegative.Geometry


open Real
namespace ThomsonNegative.Geometry

theorem contact_order_ordered_contacts (a : ℝ) (ha : physical a) :
    -1 < contacts a 3 ∧ contacts a 3 < contacts a 1 ∧ contacts a 1 < 0 ∧
    0 < contacts a 2 ∧ contacts a 2 < contacts a 0 ∧ contacts a 0 < 1 ∧
    contacts a 0 + contacts a 1 = 3*a-1 ∧ contacts a 0 + contacts a 1 < 0 := by
  obtain ⟨hl, hu⟩ := ha
  have hb := packing_endpoint_bounds.1
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hrlo : (1 : ℝ) < √2 := by nlinarith
  have hrhi : √(2 : ℝ) < 2 := by nlinarith
  have hrne : √(2 : ℝ) ≠ 0 := by positivity
  have hinv : (√(2 : ℝ))⁻¹ = √2/2 := by
    field_simp [hrne]
    nlinarith
  have hD := mul_pos (show 0 < 1-a by linarith) (show 0 < 2-√(2 : ℝ) by linarith)
  have hBD := mul_pos (show 0 < a-(1/4 : ℝ) by linarith) (show 0 < 6-√(2 : ℝ) by linarith)
  have hC := mul_pos (show 0 < (1/3 : ℝ)-a by linarith) (show 0 < 2+√(2 : ℝ) by positivity)
  have hAC := mul_pos (sub_pos.mpr hl) (show 0 < 4+√(2 : ℝ) by positivity)
  dsimp [aInf,limitingHeight] at hAC
  change -1 < -a-(1-a)/√2 ∧ -a-(1-a)/√2 < 2*a-1 ∧ 2*a-1 < 0 ∧
    0 < -a+(1-a)/√2 ∧ -a+(1-a)/√2 < a ∧ a < 1 ∧
    a+(2*a-1)=3*a-1 ∧ a+(2*a-1)<0
  simp only [div_eq_mul_inv, hinv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end ThomsonNegative.Geometry


namespace ThomsonNegative.Geometry

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

end ThomsonNegative.Geometry


namespace ThomsonNegative.Geometry

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

end ThomsonNegative.Geometry
namespace ThomsonNegative.Geometry
alias contact_injective := contacts_injective
lemma contacts_bounds (a : ℝ) (ha : physical a) (i : Fin 4) :
    contacts a i ∈ Set.Ioo (-1:ℝ) 1 := by
  obtain ⟨hD,hDB,hB,hC,hCA,hA,_,_⟩ := contact_order_ordered_contacts a ha
  change -1 < -a-(1-a)/√2 at hD
  change -a-(1-a)/√2 < 2*a-1 at hDB
  change 2*a-1 < 0 at hB
  change 0 < -a+(1-a)/√2 at hC
  change -a+(1-a)/√2 < a at hCA
  change a < 1 at hA
  fin_cases i <;> constructor <;> norm_num [contacts] <;> linarith
#print axioms contacts_bounds
end ThomsonNegative.Geometry
