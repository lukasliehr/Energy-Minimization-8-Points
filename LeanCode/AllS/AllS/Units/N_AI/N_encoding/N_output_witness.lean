import AllS.Units.N_AI.N_encoding.N_injectivity
import AllS.Units.N_AI.N_encoding.N_product_bound

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def EncodingOutputWitnessStatement : Prop :=
  ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) (List ℤ))
    (B : Matrix (Fin n) (Fin p) (List ℤ)) (T : Matrix (Fin m) (Fin p) (List ℤ))
    (K : ℕ) (C MT H : ℤ),
    0 ≤ C → 0 ≤ MT → C+MT<H →
    (∀ i j, (T i j).length=K) →
    (∀ i j, ((∑ h, listPolynomial (A i h)*listPolynomial (B h j)) : Polynomial ℤ).natDegree<K) →
    (∀ i j k, |((∑ h, listPolynomial (A i h)*listPolynomial (B h j)) : Polynomial ℤ).coeff k|≤C) →
    (∀ i j t, t∈T i j → |t|≤MT) →
    (∀ i j, (∑ h, BalancedProof.encode (2*H) (A i h)*BalancedProof.encode (2*H) (B h j))=
      BalancedProof.encode (2*H) (T i j)) →
    ∀ i j, (∑ h, listPolynomial (A i h)*listPolynomial (B h j))=listPolynomial (T i j)

theorem listPolynomial_ofFn_coeff (P : Polynomial ℤ) (K : ℕ) (hK : P.natDegree<K) :
    listPolynomial (List.ofFn (fun k : Fin K=>P.coeff k.val))=P := by
  ext k
  rw [listPolynomial_coeff]
  by_cases hk : k<K
  · simp [List.length_ofFn, hk]
  · have hp : P.coeff k=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [List.length_ofFn, hk, hp]

theorem polynomial_eq_of_bounded_eval (P : Polynomial ℤ) (t : List ℤ)
    (H C MT : ℤ) (hC : 0 ≤ C) (hMT : 0 ≤ MT) (hH : C+MT<H)
    (hdeg : P.natDegree<t.length) (hp : ∀ k, |P.coeff k|≤C)
    (ht : ∀ x∈t, |x|≤MT) (he : P.eval (2*H)=BalancedProof.encode (2*H) t) :
    P=listPolynomial t := by
  let u := List.ofFn (fun k : Fin t.length=>P.coeff k.val)
  have huPoly : listPolynomial u=P := listPolynomial_ofFn_coeff P t.length hdeg
  have hpos : 0<H := lt_of_le_of_lt (add_nonneg hC hMT) hH
  have hu : ∀ x∈u, -H≤x ∧ x<H := by
    intro x hx
    obtain ⟨k,hk⟩ := List.mem_ofFn.mp hx
    rw [←hk]
    have h := abs_le.mp (hp k.val)
    constructor <;> omega
  have ht' : ∀ x∈t, -H≤x ∧ x<H := by
    intro x hx
    have h := abs_le.mp (ht x hx)
    constructor <;> omega
  have huEnc : BalancedProof.encode (2*H) u=BalancedProof.encode (2*H) t := by
    rw [encoding_list_evaluation, huPoly]
    exact he
  have hh := encoding_injectivity u t H hpos (by simp [u]) hu ht' huEnc
  exact huPoly.symm.trans hh.2

theorem encoding_output_witness : EncodingOutputWitnessStatement := by
  intro m n p A B T K C MT H hC hMT hH hlen hdeg hp ht he i j
  apply polynomial_eq_of_bounded_eval _ (T i j) H C MT hC hMT hH
  · rw [hlen]
    exact hdeg i j
  · exact hp i j
  · exact ht i j
  · rw [Polynomial.eval_finsetSum]
    have hm : ∀ l : List ℤ, (listPolynomial l).eval (2*H)=BalancedProof.encode (2*H) l :=
      fun l=>(encoding_list_evaluation l (2*H)).symm
    simpa only [Polynomial.eval_mul, hm] using he i j

#check encoding_output_witness
#print EncodingOutputWitnessStatement
#print axioms encoding_output_witness
end Blueprint.CAP
