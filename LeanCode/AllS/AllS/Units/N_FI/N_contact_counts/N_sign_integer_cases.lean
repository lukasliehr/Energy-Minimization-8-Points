import AllS.Units.N_FI.N_contact_counts.N_one_dimensional_kernel

noncomputable section
namespace Blueprint.Thomson.Finite

theorem contact_counts_sign_integer_cases (a : ℝ) (ha : physical a) (n : Fin 4 → ℕ)
    (hsum : (∑ i, n i)=7)
    (h1 : 1+(∑ i, (n i:ℝ)*contacts a i)=0)
    (h3 : 1+(∑ i, (n i:ℝ)*(contacts a i)^3)=0) : n=baselineCounts := by
  let δ : Fin 4 → ℝ := fun i => (n i:ℝ)-(baselineCounts i:ℝ)
  obtain ⟨b0,b1,b3⟩ := contact_counts_baseline a
  have d0 : (∑ i, δ i)=0 := by
    dsimp [δ]
    rw [Finset.sum_sub_distrib,← Nat.cast_sum,← Nat.cast_sum,hsum,b0]
    norm_num
  have d1 : (∑ i, δ i*contacts a i)=0 := by
    simp only [δ,sub_mul,Finset.sum_sub_distrib]
    linarith
  have d3 : (∑ i, δ i*(contacts a i)^3)=0 := by
    simp only [δ,sub_mul,Finset.sum_sub_distrib]
    linarith
  let lam := δ 3/contactNullVector a 3
  have he : ∀ i, δ i=lam*contactNullVector a i :=
    contact_counts_one_dimensional_kernel a ha δ d0 d1 d3
  obtain ⟨vA,vB,_,vD⟩ := contactNullVector_signs a ha
  have eA := he 0
  have eB := he 1
  have eD := he 3
  change (n 0:ℝ)-2=lam*contactNullVector a 0 at eA
  change (n 1:ℝ)-(↑(1:ℕ):ℝ)=lam*contactNullVector a 1 at eB
  norm_num only [Nat.cast_one] at eB
  change (n 3:ℝ)-2=lam*contactNullVector a 3 at eD
  have hlam : lam=0 := by
    rcases lt_trichotomy lam 0 with hl | hz | hl
    · have hnB : (n 1:ℝ)<1 := by linarith [mul_neg_of_neg_of_pos hl vB]
      have hnD : (n 3:ℝ)<2 := by linarith [mul_neg_of_neg_of_pos hl vD]
      have nB : n 1=0 := by
        have : n 1<1 := by exact_mod_cast hnB
        omega
      have nD : (n 3:ℝ) ≤ 1 := by
        have : n 3<2 := by exact_mod_cast hnD
        have : n 3 ≤ 1 := by omega
        exact_mod_cast this
      obtain ⟨hD,hDB,hB,hC,hCA,_,_,_⟩ := contact_order_ordered_contacts a ha
      have hA : 0 < contacts a 0 := hC.trans hCA
      have hna := mul_nonneg (show 0 ≤ (n 0:ℝ) by positivity) hA.le
      have hnc := mul_nonneg (show 0 ≤ (n 2:ℝ) by positivity) hC.le
      have hnd := mul_le_mul_of_nonpos_right nD (show contacts a 3 ≤ 0 by linarith)
      rw [Fin.sum_univ_four,nB] at h1
      norm_num only [Nat.cast_zero,zero_mul,one_mul] at h1 hnd
      linarith
    · exact hz
    · have hnA : 2 < (n 0:ℝ) := by linarith [mul_pos hl vA]
      have hnB : 1 < (n 1:ℝ) := by linarith [mul_pos hl vB]
      have hnD : 2 < (n 3:ℝ) := by linarith [mul_pos hl vD]
      have nA : 2 < n 0 := by exact_mod_cast hnA
      have nB : 1 < n 1 := by exact_mod_cast hnB
      have nD : 2 < n 3 := by exact_mod_cast hnD
      rw [Fin.sum_univ_four] at hsum
      omega
  funext i
  have hi := he i
  rw [hlam,zero_mul] at hi
  dsimp [δ] at hi
  exact_mod_cast (sub_eq_zero.mp hi)

#check contact_counts_sign_integer_cases
#print axioms contact_counts_sign_integer_cases
end Blueprint.Thomson.Finite
