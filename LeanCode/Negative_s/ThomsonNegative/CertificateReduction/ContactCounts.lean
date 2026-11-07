import Mathlib

/-!
Conditional negative-range equality reduction.  The stronger height lower
bound `5/16 ≤ a` is an explicit hypothesis, not an already assembled root fact.
-/

noncomputable section
namespace ThomsonNegative.CertificateReduction
set_option maxHeartbeats 1000000

theorem contact_counts_from_first_moment (a δ : ℝ)
    (ha : (5 : ℝ)/16 ≤ a) (ha' : a < 1/3)
    (hδ : (7 : ℝ)/10*(1-a) ≤ δ)
    (hδ' : δ ≤ (71 : ℝ)/100*(1-a))
    (nA nB nC nD : ℕ) (hn : nA+nB+nC+nD=7)
    (hm : 1+a*nA+(2*a-1)*nB+(-a+δ)*nC+(-a-δ)*nD=0) :
    nA=2 ∧ nB=1 ∧ nC=2 ∧ nD=2 := by
  have hA : nA ≤ 7 := by omega
  interval_cases nA
  · have hB : nB ≤ 7 := by omega
    interval_cases nB
    · have hC : nC ≤ 7 := by omega
      interval_cases nC
      · have hD : nD = 7 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 6 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 5 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 6 := by omega
      interval_cases nC
      · have hD : nD = 6 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 5 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 5 := by omega
      interval_cases nC
      · have hD : nD = 5 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 4 := by omega
      interval_cases nC
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 3 := by omega
      interval_cases nC
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 2 := by omega
      interval_cases nC
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 6 := by omega
    interval_cases nB
    · have hC : nC ≤ 6 := by omega
      interval_cases nC
      · have hD : nD = 6 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 5 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 5 := by omega
      interval_cases nC
      · have hD : nD = 5 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 4 := by omega
      interval_cases nC
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 3 := by omega
      interval_cases nC
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 2 := by omega
      interval_cases nC
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 5 := by omega
    interval_cases nB
    · have hC : nC ≤ 5 := by omega
      interval_cases nC
      · have hD : nD = 5 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 4 := by omega
      interval_cases nC
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 3 := by omega
      interval_cases nC
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 2 := by omega
      interval_cases nC
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 4 := by omega
    interval_cases nB
    · have hC : nC ≤ 4 := by omega
      interval_cases nC
      · have hD : nD = 4 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 3 := by omega
      interval_cases nC
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 2 := by omega
      interval_cases nC
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 3 := by omega
    interval_cases nB
    · have hC : nC ≤ 3 := by omega
      interval_cases nC
      · have hD : nD = 3 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 2 := by omega
      interval_cases nC
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 2 := by omega
    interval_cases nB
    · have hC : nC ≤ 2 := by omega
      interval_cases nC
      · have hD : nD = 2 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 1 := by omega
    interval_cases nB
    · have hC : nC ≤ 1 := by omega
      interval_cases nC
      · have hD : nD = 1 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith
  · have hB : nB ≤ 0 := by omega
    interval_cases nB
    · have hC : nC ≤ 0 := by omega
      interval_cases nC
      · have hD : nD = 0 := by omega
        subst nD
        norm_num at hm ⊢
        linarith

theorem reciprocal_sqrt_two_bounds :
    (7 : ℝ)/10 ≤ 1/Real.sqrt 2 ∧ 1/Real.sqrt 2 ≤ (71 : ℝ)/100 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  constructor
  · apply (le_div_iff₀ hs).2
    nlinarith
  · apply (div_le_iff₀ hs).2
    nlinarith

theorem antiprism_contact_counts_from_first_moment (a : ℝ)
    (ha : (5 : ℝ)/16 ≤ a) (ha' : a < 1/3)
    (nA nB nC nD : ℕ) (hn : nA+nB+nC+nD=7)
    (hm : 1+a*nA+(2*a-1)*nB+
      (-a+(1-a)/Real.sqrt 2)*nC+(-a-(1-a)/Real.sqrt 2)*nD=0) :
    nA=2 ∧ nB=1 ∧ nC=2 ∧ nD=2 := by
  have hnonneg : 0 ≤ 1-a := by linarith
  have hlo := mul_le_mul_of_nonneg_right reciprocal_sqrt_two_bounds.1 hnonneg
  have hhi := mul_le_mul_of_nonneg_right reciprocal_sqrt_two_bounds.2 hnonneg
  have he : (1/Real.sqrt 2)*(1-a) = (1-a)/Real.sqrt 2 := by ring
  rw [he] at hlo hhi
  exact contact_counts_from_first_moment a ((1-a)/Real.sqrt 2) ha ha'
    hlo hhi nA nB nC nD hn hm

theorem candidate_third_moment (a : ℝ) :
    1+2*a^3+(2*a-1)^3+2*(-a+(1-a)/Real.sqrt 2)^3+
      2*(-a-(1-a)/Real.sqrt 2)^3=0 := by
  have hq : (1/Real.sqrt 2)^2=(1/2 : ℝ) := by
    norm_num [div_pow, Real.sq_sqrt]
  linear_combination (-12*a*(1-a)^2)*hq

theorem third_moment_from_first_moment (a : ℝ)
    (ha : (5 : ℝ)/16 ≤ a) (ha' : a < 1/3)
    (nA nB nC nD : ℕ) (hn : nA+nB+nC+nD=7)
    (hm : 1+a*nA+(2*a-1)*nB+
      (-a+(1-a)/Real.sqrt 2)*nC+(-a-(1-a)/Real.sqrt 2)*nD=0) :
    1+a^3*nA+(2*a-1)^3*nB+
      (-a+(1-a)/Real.sqrt 2)^3*nC+(-a-(1-a)/Real.sqrt 2)^3*nD=0 := by
  obtain ⟨rfl,rfl,rfl,rfl⟩ :=
    antiprism_contact_counts_from_first_moment a ha ha' nA nB nC nD hn hm
  convert candidate_third_moment a using 1 <;> norm_num <;> ring

#print axioms contact_counts_from_first_moment
#print axioms antiprism_contact_counts_from_first_moment
#print axioms third_moment_from_first_moment
end ThomsonNegative.CertificateReduction
