import AllS.Units.N_FI.N_contact_counts.N_baseline

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def contactDenominator (a : ℝ) (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (contacts a i-contacts a j)

def contactNullVector (a : ℝ) (i : Fin 4) : ℝ :=
  (contacts a i-(a-1))/contactDenominator a i

def contactQuartic (a : ℝ) : Polynomial ℝ := Lagrange.nodal Finset.univ (contacts a)

theorem contactDenominator_derivative (a : ℝ) (i : Fin 4) :
    contactDenominator a i = (contactQuartic a).derivative.eval (contacts a i) := by
  rw [contactQuartic,Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i)]
  simp [contactDenominator,Lagrange.nodal,Polynomial.eval_prod]

theorem contact_sum (a : ℝ) : (∑ i, contacts a i)=a-1 := by
  simp [contacts,Fin.sum_univ_succ]
  ring

theorem contact_injective (a : ℝ) (ha : physical a) : Function.Injective (contacts a) := by
  obtain ⟨hD,hDB,hB,hC,hCA,hA,_,_⟩ := contact_order_ordered_contacts a ha
  change -1 < -a-(1-a)/√2 at hD
  change -a-(1-a)/√2 < 2*a-1 at hDB
  change 2*a-1 < 0 at hB
  change 0 < -a+(1-a)/√2 at hC
  change -a+(1-a)/√2 < a at hCA
  change a < 1 at hA
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (exfalso; norm_num [contacts] at h; linarith)

theorem prod_three_fin4 (f : Fin 4 → ℝ) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∏ x ∈ ({i,j,k} : Finset (Fin 4)), f x)=f i*f j*f k := by
  rw [Finset.prod_insert (by simp [hij,hik]),Finset.prod_pair hjk]
  ring

theorem four_contact_null_vector (v : Fin 4 → ℝ) (hv : Function.Injective v) :
    let w := fun i => (v i-(∑ j, v j))/(∏ j ∈ Finset.univ.erase i, (v i-v j))
    (∑ i, w i)=0 ∧ (∑ i, w i*v i)=0 ∧ (∑ i, w i*(v i)^3)=0 := by
  have hne (i j : Fin 4) (h : i ≠ j) : v i-v j ≠ 0 := sub_ne_zero.mpr (hv.ne h)
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h03 := hne 0 3 (by decide)
  have h12 := hne 1 2 (by decide)
  have h13 := hne 1 3 (by decide)
  have h23 := hne 2 3 (by decide)
  have h10 := hne 1 0 (by decide)
  have h20 := hne 2 0 (by decide)
  have h30 := hne 3 0 (by decide)
  have h21 := hne 2 1 (by decide)
  have h31 := hne 3 1 (by decide)
  have h32 := hne 3 2 (by decide)
  have e0 : Finset.univ.erase (0:Fin 4)={1,2,3} := by decide
  have e1 : Finset.univ.erase (1:Fin 4)={0,2,3} := by decide
  have e2 : Finset.univ.erase (2:Fin 4)={0,1,3} := by decide
  have e3 : Finset.univ.erase (3:Fin 4)={0,1,2} := by decide
  dsimp only
  simp only [Fin.sum_univ_four]
  simp only [e0,e1,e2,e3]
  rw [prod_three_fin4 _ 1 2 3 (by decide) (by decide) (by decide),
    prod_three_fin4 _ 0 2 3 (by decide) (by decide) (by decide),
    prod_three_fin4 _ 0 1 3 (by decide) (by decide) (by decide),
    prod_three_fin4 _ 0 1 2 (by decide) (by decide) (by decide)]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem contact_counts_null_vector (a : ℝ) (ha : physical a) :
    (∑ i, contactNullVector a i)=0 ∧
    (∑ i, contactNullVector a i*contacts a i)=0 ∧
    (∑ i, contactNullVector a i*(contacts a i)^3)=0 := by
  simpa only [contactNullVector,contactDenominator,contact_sum] using
    four_contact_null_vector (contacts a) (contact_injective a ha)

#check contact_counts_null_vector
#print axioms contact_counts_null_vector
end Blueprint.Thomson.Finite
