import AllS.Units.N_FI.N_upstream_evaluation.N_moment_sums
import AllS.Units.N_FI.N_geometry.N_gram_entries

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.Finite

/-- Finite even-binomial polynomial from manuscript1054–1073. -/
def momentR (k : ℕ) (c d a : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (k+1)).filter (fun j => j%2=0),
    (k.choose j : ℝ)*c^(k-j)*d^j*(-1)^(j/2)*a^((k-j-k%2)/2)

def momentP (k i : ℕ) (a : ℝ) : ℝ :=
  if k=0 then 1+2*(contacts a 0)^i+(contacts a 1)^i+2*(contacts a 2)^i+2*(contacts a 3)^i
  else 2^k*a^(k/2)*(contacts a 1)^i+
    2*(contacts a 0)^i*momentR k 1 1 a+
    2*(contacts a 2)^i*momentR k (-1-1/Real.sqrt 2) (1/Real.sqrt 2) a+
    2*(contacts a 3)^i*momentR k (-1+1/Real.sqrt 2) (1/Real.sqrt 2) a

def candidateGram (a : ℝ) (i j : Fin 8) : ℝ :=
  if i=j then 1 else contacts a (candidateContactLabel i j)

def candidateTransportTable : Fin 8 → Fin 8 → Fin 8 :=
  ![![0,1,2,3,4,5,6,7],![1,2,3,0,5,6,7,4],![2,3,0,1,6,7,4,5],![3,0,1,2,7,4,5,6],
    ![4,7,6,5,0,3,2,1],![5,4,7,6,1,0,3,2],![6,5,4,7,2,1,0,3],![7,6,5,4,3,2,1,0]]

def candidateRootTangent (a : ℝ) : Fin 8 → ℂ :=
  fun i => (Real.sqrt (1-a) : ℂ)*
    (![0,⟨Real.sqrt a,1⟩,⟨2*Real.sqrt a,0⟩,⟨Real.sqrt a,-1⟩,
      ⟨-(1+1/Real.sqrt 2)*Real.sqrt a,1/Real.sqrt 2⟩,
      ⟨-(1-1/Real.sqrt 2)*Real.sqrt a,1/Real.sqrt 2⟩,
      ⟨-(1-1/Real.sqrt 2)*Real.sqrt a,-1/Real.sqrt 2⟩,
      ⟨-(1+1/Real.sqrt 2)*Real.sqrt a,-1/Real.sqrt 2⟩] i)

def candidateRootFeature (a : ℝ) (k i : ℕ) : ℂ :=
  ∑ j : Fin 8,(candidateGram a 0 j : ℂ)^i*(candidateRootTangent a j)^k

def CandidateMomentFactorContract : Prop := ∀ a : ℝ,physical a → ∀ m k : ℕ,k≤8 →
  canonicalMoment m k (X a)=(fun i j =>
    8*(1-a)^k*a^(k%2)*momentP k i.val a*momentP k j.val a) ∧ momentP 0 0 a=8

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem candidateTransportTable_bijective : ∀ i,Function.Bijective (candidateTransportTable i) := by decide

def candidateTransport (i : Fin 8) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (candidateTransportTable i) (candidateTransportTable_bijective i)

theorem candidateTransport_zero (i : Fin 8) : candidateTransport i 0=i := by
  have h : ∀ i,candidateTransportTable i 0=i := by decide
  exact h i

theorem candidateTransport_label (i j l : Fin 8) :
    candidateContactLabel (candidateTransport i j) (candidateTransport i l)=candidateContactLabel j l := by
  have h : ∀ i j l,candidateContactLabel (candidateTransportTable i j) (candidateTransportTable i l)=
      candidateContactLabel j l := by decide
  exact h i j l

theorem candidateGram_transport (a : ℝ) (i j l : Fin 8) :
    candidateGram a (candidateTransport i j) (candidateTransport i l)=candidateGram a j l := by
  simp only [candidateGram,(candidateTransport i).injective.eq_iff,candidateTransport_label]

theorem candidateGram_root_transport (a : ℝ) (i j : Fin 8) :
    candidateGram a i (candidateTransport i j)=candidateGram a 0 j := by
  simpa only [candidateTransport_zero] using candidateGram_transport a i 0 j

theorem candidateCenteredSum_eq_root (a : ℝ) (i : Fin 8) (f : ℝ → ℝ → ℝ → ℝ) :
    (∑ j : Fin 8,∑ l : Fin 8,f (candidateGram a i j) (candidateGram a i l) (candidateGram a j l))=
      ∑ j : Fin 8,∑ l : Fin 8,f (candidateGram a 0 j) (candidateGram a 0 l) (candidateGram a j l) := by
  calc
    _ = ∑ j : Fin 8,∑ l : Fin 8,
        f (candidateGram a i (candidateTransport i j)) (candidateGram a i (candidateTransport i l))
          (candidateGram a (candidateTransport i j) (candidateTransport i l)) := by
      trans ∑ j : Fin 8,∑ l : Fin 8,
        f (candidateGram a i (candidateTransport i j)) (candidateGram a i l)
          (candidateGram a (candidateTransport i j) l)
      · exact (Equiv.sum_comp (candidateTransport i) (fun j =>
          ∑ l : Fin 8,f (candidateGram a i j) (candidateGram a i l) (candidateGram a j l))).symm
      · apply Finset.sum_congr rfl
        intro j hj
        exact (Equiv.sum_comp (candidateTransport i) _).symm
    _ = _ := by simp only [candidateGram_root_transport,candidateGram_transport]

theorem candidateMoment_root_sum (a : ℝ) (ha : physical a) (m k : ℕ) (i j : Fin m) :
    canonicalMoment m k (X a) i j=8*∑ x : Fin 8,∑ y : Fin 8,
      (candidateGram a 0 x)^i.val*(candidateGram a 0 y)^j.val*
        GenericMoments.kernelQ k (candidateGram a 0 x) (candidateGram a 0 y) (candidateGram a x y) := by
  rw [canonicalMoment_eq_generic,GenericMoments.momentMatrix_entry]
  simp only [GenericMoments.tripleSum,GenericMoments.onTriples,candidate_gram_entry a ha]
  change (∑ z : Fin 8,∑ x : Fin 8,∑ y : Fin 8,
    (candidateGram a z x)^i.val*(candidateGram a z y)^j.val*
      GenericMoments.kernelQ k (candidateGram a z x) (candidateGram a z y) (candidateGram a x y))=_
  calc
    _ = ∑ _z : Fin 8,∑ x : Fin 8,∑ y : Fin 8,
        (candidateGram a 0 x)^i.val*(candidateGram a 0 y)^j.val*
          GenericMoments.kernelQ k (candidateGram a 0 x) (candidateGram a 0 y) (candidateGram a x y) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact candidateCenteredSum_eq_root a z (fun u v t => u^i.val*v^j.val*GenericMoments.kernelQ k u v t)
    _ = _ := by simp

theorem candidateRootTangent_normSq (a : ℝ) (ha : physical a) (j : Fin 8) :
    Complex.normSq (candidateRootTangent a j)=1-(candidateGram a 0 j)^2 := by
  obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
  have hr : (Real.sqrt (1-a))^2=1-a := Real.sq_sqrt (by linarith)
  have hh : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  have hq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hqn : Real.sqrt (2 : ℝ)≠0 := by positivity
  fin_cases j <;> norm_num [candidateRootTangent,candidateGram,candidateContactLabel,contacts,
    Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [hr,hh,hq]
  all_goals ring

theorem candidateRootTangent_re (a : ℝ) (ha : physical a) (j l : Fin 8) :
    (candidateRootTangent a j*star (candidateRootTangent a l)).re=
      candidateGram a j l-candidateGram a 0 j*candidateGram a 0 l := by
  obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
  have hr : (Real.sqrt (1-a))^2=1-a := Real.sq_sqrt (by linarith)
  have hh : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  have hq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hqn : Real.sqrt (2 : ℝ)≠0 := by positivity
  fin_cases j <;> fin_cases l <;>
    norm_num [candidateRootTangent,candidateGram,candidateContactLabel,contacts,
      Complex.mul_re,Complex.mul_im,Complex.star_def,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [hr,hh,hq]
  all_goals ring

theorem candidateRootKernel (a : ℝ) (ha : physical a) (k : ℕ) (j l : Fin 8) :
    GenericMoments.kernelQ k (candidateGram a 0 j) (candidateGram a 0 l) (candidateGram a j l)=
      ((candidateRootTangent a j)^k).re*((candidateRootTangent a l)^k).re+
      ((candidateRootTangent a j)^k).im*((candidateRootTangent a l)^k).im := by
  rw [GenericMoments.kernelQ_complex k _ _ _ (candidateRootTangent a j*star (candidateRootTangent a l))
    (candidateRootTangent_re a ha j l)]
  · exact GenericMoments.complex_power_gram _ _ _
  · simp [Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,candidateRootTangent_normSq a ha]

theorem candidateRootFeature_re (a : ℝ) (k i : ℕ) :
    (candidateRootFeature a k i).re=∑ j : Fin 8,(candidateGram a 0 j)^i*((candidateRootTangent a j)^k).re := by
  simp [candidateRootFeature,← Complex.ofReal_pow,Complex.mul_re]

theorem candidateRootFeature_im (a : ℝ) (k i : ℕ) :
    (candidateRootFeature a k i).im=∑ j : Fin 8,(candidateGram a 0 j)^i*((candidateRootTangent a j)^k).im := by
  simp [candidateRootFeature,← Complex.ofReal_pow,Complex.mul_im]

theorem candidateMoment_feature (a : ℝ) (ha : physical a) (m k : ℕ) (i j : Fin m) :
    canonicalMoment m k (X a) i j=8*((candidateRootFeature a k i.val).re*(candidateRootFeature a k j.val).re+
      (candidateRootFeature a k i.val).im*(candidateRootFeature a k j.val).im) := by
  rw [candidateMoment_root_sum a ha]
  congr 1
  simp_rw [candidateRootKernel a ha]
  simp only [candidateRootFeature_re,candidateRootFeature_im,
    mul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro x hx <;>
    apply Finset.sum_congr rfl <;> intro y hy <;> ring

theorem power_even_odd (a h : ℝ) (hh : h^2=a) (n : ℕ) :
    h^n=a^(n/2)*h^(n%2) := by
  calc
    _ = h^(2*(n/2)+n%2) := by congr 1;omega
    _ = (h^2)^(n/2)*h^(n%2) := by rw [pow_add,pow_mul]
    _ = _ := by rw [hh]

theorem complexMomentR (a h c d : ℝ) (hh : h^2=a) (k : ℕ) (hk : k≤8) :
    ((⟨c*h,d⟩ : ℂ)^k).re=h^(k%2)*momentR k c d a := by
  have h3 := power_even_odd a h hh 3
  have h4 := power_even_odd a h hh 4
  have h5 := power_even_odd a h hh 5
  have h6 := power_even_odd a h hh 6
  have h7 := power_even_odd a h hh 7
  have h8 := power_even_odd a h hh 8
  norm_num at h3 h4 h5 h6 h7 h8
  interval_cases k <;>
    norm_num [momentR,Finset.sum_filter,Finset.sum_range_succ,Nat.choose,pow_succ,Complex.mul_re,Complex.mul_im]
  all_goals ring_nf
  all_goals try simp only [hh,h3,h4,h5,h6,h7,h8]
  all_goals ring

theorem complexCoord_conj_re (c d : ℝ) (k : ℕ) :
    ((⟨c,-d⟩ : ℂ)^k).re=((⟨c,d⟩ : ℂ)^k).re := by
  have he : (⟨c,-d⟩ : ℂ)=star (⟨c,d⟩ : ℂ) := rfl
  rw [he,← star_pow]
  rfl

theorem complexCoord_conj_im (c d : ℝ) (k : ℕ) :
    ((⟨c,-d⟩ : ℂ)^k).im=-((⟨c,d⟩ : ℂ)^k).im := by
  have he : (⟨c,-d⟩ : ℂ)=star (⟨c,d⟩ : ℂ) := rfl
  rw [he,← star_pow]
  rfl

theorem candidateRootFeature_formula (a : ℝ) (ha : physical a) (k i : ℕ) (hk : k≤8) :
    candidateRootFeature a k i=
      ((Real.sqrt (1-a))^k*(Real.sqrt a)^(k%2)*momentP k i a : ℝ) := by
  obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
  have hh : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  have hc : -(1+1/Real.sqrt 2)*Real.sqrt a=(-1-1/Real.sqrt 2)*Real.sqrt a := by ring
  have hd : -(1-1/Real.sqrt 2)*Real.sqrt a=(-1+1/Real.sqrt 2)*Real.sqrt a := by ring
  have hb : (⟨2*Real.sqrt a,0⟩ : ℂ)=(2*Real.sqrt a : ℝ) := rfl
  by_cases hk0 : k=0
  · subst k
    apply Complex.ext <;> simp only [Complex.ofReal_re,Complex.ofReal_im] <;>
      simp [candidateRootFeature_re,candidateRootFeature_im,candidateGram,candidateContactLabel,
        Fin.sum_univ_succ,momentP,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring
  apply Complex.ext <;> simp only [Complex.ofReal_re,Complex.ofReal_im]
  · rw [candidateRootFeature_re]
    simp only [candidateRootTangent,candidateGram,candidateContactLabel,Fin.sum_univ_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three,
      mul_pow,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,mul_zero,sub_zero,one_pow,zero_pow hk0,Complex.zero_re,
      hc,hd,hb,neg_div,complexCoord_conj_re]
    norm_num [Fin.ext_iff]
    rw [show (⟨Real.sqrt a,1⟩ : ℂ)=(⟨1*Real.sqrt a,1⟩ : ℂ) by simp]
    simp only [complexMomentR a (Real.sqrt a) _ _ hh k hk]
    rw [momentP,if_neg hk0]
    rw [power_even_odd a (Real.sqrt a) hh k]
    simp only [one_div,neg_div]
    ring
  · rw [candidateRootFeature_im]
    simp [candidateRootTangent,candidateGram,candidateContactLabel,Fin.sum_univ_succ,
      mul_pow,← Complex.ofReal_pow,Complex.mul_im,zero_pow hk0,
      hc,hd,hb,neg_div,complexCoord_conj_im,Matrix.cons_val_two,Matrix.cons_val_three]
    have h2 : ((2 : ℂ)^k).im=0 := by
      rw [← Complex.ofReal_ofNat,← Complex.ofReal_pow,Complex.ofReal_im]
    simp [complexCoord_conj_im,h2]

theorem moment_kernels_candidate_factor : CandidateMomentFactorContract := by
  intro a ha m k hk
  obtain ⟨ha0,ha1⟩ := physical_mem_Ioo a ha
  have hr : (Real.sqrt (1-a))^2=1-a := Real.sq_sqrt (by linarith)
  have hh : (Real.sqrt a)^2=a := Real.sq_sqrt ha0.le
  constructor
  · ext i j
    rw [candidateMoment_feature a ha, candidateRootFeature_formula a ha k i.val hk,
      candidateRootFeature_formula a ha k j.val hk]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,add_zero]
    calc
      _ = 8*((Real.sqrt (1-a))^2)^k*((Real.sqrt a)^2)^(k%2)*
          momentP k i.val a*momentP k j.val a := by ring
      _ = _ := by rw [hr,hh]
  · norm_num [momentP]

#check moment_kernels_candidate_factor
#print axioms moment_kernels_candidate_factor
end Blueprint.Thomson.Finite
