import AllS.Units.N_FI.N_compatibility.N_family_functionals
import AllS.Units.N_F.N_kernels

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Vanishing on the actual 21 contact points, including every coordinate order. -/
def ContactVanishes (a : ℝ) (f : Poly3) : Prop :=
  ∀ r σ,MvPolynomial.eval (permutedContact a r σ) f=0

theorem candidateTriangleLabels_mem (i j k : Fin 8) (h : i≠j ∧ j≠k ∧ k≠i) :
    ∃ r,candidateTriangleLabels i j k∈contactLabelOrbit r := by
  have he : ∀ i j k : Fin 8,i≠j ∧ j≠k ∧ k≠i →
      ∃ r,candidateTriangleLabels i j k∈contactLabelOrbit r := by decide
  exact he i j k h

theorem contactVanishes_subst_eval (a : ℝ) (f : Poly3) (hf : ContactVanishes a f)
    (i j k : Fin 8) (h : i≠j ∧ j≠k ∧ k≠i) :
    (candidateTripleSubst i j k f).eval a=0 := by
  obtain ⟨r,hr⟩ := candidateTriangleLabels_mem i j k h
  obtain ⟨σ,hσ,he⟩ := Finset.mem_image.mp hr
  rw [candidateTripleSubst_eval]
  have hv : ![contacts a (candidateContactLabel i j),contacts a (candidateContactLabel i k),
      contacts a (candidateContactLabel j k)]=permutedContact a r σ := by
    funext q
    have hq := congrFun he q
    change contactRepresentative r (σ q)=candidateTriangleLabels i j k q at hq
    simp only [permutedContact,contactTripleEval,Function.comp_apply]
    rw [hq]
    fin_cases q <;> rfl
  rw [hv]
  exact hf r σ

theorem ContactVanishes.rename {a : ℝ} {f : Poly3} (hf : ContactVanishes a f)
    (τ : Equiv.Perm (Fin 3)) : ContactVanishes a (MvPolynomial.rename τ f) := by
  intro r σ
  rw [MvPolynomial.eval_rename]
  change MvPolynomial.eval (permutedContact a r (σ*τ)) f=0
  exact hf r (σ*τ)

theorem candidateFamilyMap_zero_jet (a : ℝ) (f : Poly3)
    (h : ∀ i j k,i≠j ∧ j≠k ∧ k≠i →
      (candidateTripleSubst i j k f).eval a=0 ∧
      (candidateTripleSubst i j k f).derivative.eval a=0) : L0 a f=0 ∧ L1 a f=0 := by
  have hv : (candidateFamilyMap f).eval a=0 := by
    rw [candidateFamilyMap_apply,Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro k hk
    split_ifs with hd
    · exact (h i j k hd).1
    · simp
  have hd : (candidateFamilyMap f).derivative.eval a=0 := by
    rw [candidateFamilyMap_apply]
    simp only [map_sum,Polynomial.eval_finsetSum]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro k hk
    split_ifs with ht
    · exact (h i j k ht).2
    · simp
  exact ⟨hv,hd⟩

theorem contact_product_zero_jet (a : ℝ) (w f g : Poly3)
    (hf : ContactVanishes a f) (hg : ContactVanishes a g) :
    L0 a (w*f*g)=0 ∧ L1 a (w*f*g)=0 := by
  apply candidateFamilyMap_zero_jet
  intro i j k h
  have hfv := contactVanishes_subst_eval a f hf i j k h
  have hgv := contactVanishes_subst_eval a g hg i j k h
  simp only [map_mul,Polynomial.eval_mul,Polynomial.derivative_mul,Polynomial.eval_add,hfv,hgv,
    mul_zero,zero_mul,add_zero,and_self]

def ScalarAnnihilationContract : Prop := ∀ a : ℝ,physical a →
  ∀ w f g : Poly3,ContactVanishes a f → ContactVanishes a g →
    L0 a (reynolds (w*f*g))=0 ∧ L1 a (reynolds (w*f*g))=0

theorem compatibility_scalar_annihilation : ScalarAnnihilationContract := by
  intro a ha w f g hf hg
  have h (σ : Equiv.Perm (Fin 3)) :
      L0 a (MvPolynomial.rename σ (w*f*g))=0 ∧ L1 a (MvPolynomial.rename σ (w*f*g))=0 := by
    simp only [map_mul]
    exact contact_product_zero_jet a _ _ _ (hf.rename σ) (hg.rename σ)
  constructor
  · simp only [reynolds,LinearMap.smul_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply,
      map_smul,map_sum]
    simp only [fun σ => (h σ).1,Finset.sum_const_zero,smul_zero]
  · simp only [reynolds,LinearMap.smul_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply,
      map_smul,map_sum]
    simp only [fun σ => (h σ).2,Finset.sum_const_zero,smul_zero]

#check compatibility_scalar_annihilation
#print axioms compatibility_scalar_annihilation
end Blueprint.Thomson.Finite
