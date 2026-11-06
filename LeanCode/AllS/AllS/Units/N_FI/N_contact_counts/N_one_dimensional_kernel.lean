import AllS.Units.N_FI.N_contact_counts.N_signs

noncomputable section
namespace Blueprint.Thomson.Finite

theorem three_odd_kernel (A B C x y z : ℝ)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hT : A+B+C ≠ 0)
    (h0 : x+y+z=0) (h1 : x*A+y*B+z*C=0) (h3 : x*A^3+y*B^3+z*C^3=0) :
    x=0 ∧ y=0 ∧ z=0 := by
  have hxprod : x*((A-B)*(A-C)*(A+B+C))=0 := by
    linear_combination h3-(B^2+B*C+C^2)*h1+B*C*(B+C)*h0
  have hx : x=0 := (mul_eq_zero.mp hxprod).resolve_right
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hAB) (sub_ne_zero.mpr hAC)) hT)
  have hyprod : y*(B-C)=0 := by rw [hx] at h1 h0; linear_combination h1-C*h0
  have hy : y=0 := (mul_eq_zero.mp hyprod).resolve_right (sub_ne_zero.mpr hBC)
  exact ⟨hx,hy,by linarith⟩

theorem contact_counts_one_dimensional_kernel (a : ℝ) (ha : physical a) (δ : Fin 4 → ℝ)
    (h0 : (∑ i, δ i)=0) (h1 : (∑ i, δ i*contacts a i)=0)
    (h3 : (∑ i, δ i*(contacts a i)^3)=0) :
    ∀ i, δ i=(δ 3/contactNullVector a 3)*contactNullVector a i := by
  let lam := δ 3/contactNullVector a 3
  let w : Fin 4 → ℝ := fun i => δ i-lam*contactNullVector a i
  obtain ⟨n0,n1,n3⟩ := contact_counts_null_vector a ha
  have hwd : w 3=0 := by
    dsimp [w,lam]
    have hn := (contactNullVector_signs a ha).2.2.2.ne'
    field_simp <;> ring
  have hw0 : (∑ i, w i)=0 := by
    simp only [w,Finset.sum_sub_distrib,← Finset.mul_sum,h0,n0,mul_zero,sub_self]
  have hw1 : (∑ i, w i*contacts a i)=0 := by
    simp only [w,sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum,h1,n1,mul_zero,sub_self]
  have hw3 : (∑ i, w i*(contacts a i)^3)=0 := by
    simp only [w,sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum,h3,n3,mul_zero,sub_self]
  obtain ⟨_,hDB,hB,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
  have hsum : 0 < contacts a 0+contacts a 1+contacts a 2 := by
    have ht := (contact_trace_bounds a ha).1
    have hs := contact_sum a
    rw [Fin.sum_univ_four] at hs
    linarith
  simp only [Fin.sum_univ_four,hwd,zero_mul,add_zero] at hw0 hw1 hw3
  obtain ⟨hwA,hwB,hwC⟩ := three_odd_kernel (contacts a 0) (contacts a 1) (contacts a 2)
    (w 0) (w 1) (w 2) (by linarith) (by linarith) (by linarith) hsum.ne' hw0 hw1 hw3
  have hw : ∀ i, w i=0 := by
    intro i
    fin_cases i
    · exact hwA
    · exact hwB
    · exact hwC
    · exact hwd
  intro i
  exact sub_eq_zero.mp (hw i)

#check contact_counts_one_dimensional_kernel
#print axioms contact_counts_one_dimensional_kernel
end Blueprint.Thomson.Finite
