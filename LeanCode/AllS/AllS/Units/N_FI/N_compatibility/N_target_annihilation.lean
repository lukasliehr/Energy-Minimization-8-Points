import AllS.Units.N_FI.N_compatibility.N_family_functionals
import AllS.Units.N_F.N_hermite
import AllS.Units.N_FI.N_energy_lower.N_summed_certificate

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem candidate_label_pair_sum (g : Fin 4 → ℝ) :
    PairSum (fun i j => g (candidateContactLabel i j))=8*g 0+4*g 1+8*g 2+8*g 3 := by
  classical
  let S : Finset (Fin 8 × Fin 8) := Finset.univ.filter (fun p => p.1<p.2)
  have he := Finset.sum_fiberwise' S (fun p : Fin 8 × Fin 8 => candidateContactLabel p.1 p.2) g
  have hc (r : Fin 4) : S.filter (fun p => candidateContactLabel p.1 p.2=r)=candidatePairLabels r := by
    ext p
    simp only [S,candidatePairLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  have hleft : (∑ r : Fin 4,∑ p ∈ S with candidateContactLabel p.1 p.2=r,g r)=
      8*g 0+4*g 1+8*g 2+8*g 3 := by
    simp only [hc,Finset.sum_const,candidatePairLabels_card,nsmul_eq_mul]
    simp [candidatePairCount,Fin.sum_univ_succ]
    ring
  have hright : (∑ p ∈ S,g (candidateContactLabel p.1 p.2))=
      PairSum (fun i j => g (candidateContactLabel i j)) := by
    simp only [S,Finset.sum_filter,Fintype.sum_prod_type,PairSum]
  rw [hleft,hright] at he
  exact he.symm

theorem candidate_pair_sum (a : ℝ) (ha : physical a) (f : ℝ → ℝ) :
    PairSum (fun i j => f (inner ℝ (X a i) (X a j)))=
      8*f (contacts a 0)+4*f (contacts a 1)+8*f (contacts a 2)+8*f (contacts a 3) := by
  rw [← candidate_label_pair_sum (fun r => f (contacts a r))]
  unfold PairSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [candidate_gram_entry a ha,if_neg (ne_of_lt (Finset.mem_filter.mp hj).2)]

def contactSlope : Fin 4 → ℝ := ![1,2,-1-1/Real.sqrt 2,-1+1/Real.sqrt 2]

theorem hasDerivAt_contact (a : ℝ) (r : Fin 4) :
    HasDerivAt (fun b => contacts b r) (contactSlope r) a := by
  fin_cases r
  · exact hasDerivAt_id a
  · convert! ((hasDerivAt_id a).const_mul 2).sub_const 1 using 1 <;> norm_num [contacts,contactSlope]
  · change HasDerivAt (fun b : ℝ => -b+(1-b)/Real.sqrt 2) (-1-1/Real.sqrt 2) a
    convert! (hasDerivAt_id a).neg.add (((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).div_const (Real.sqrt 2)) using 1 <;> ring
  · change HasDerivAt (fun b : ℝ => -b-(1-b)/Real.sqrt 2) (-1+1/Real.sqrt 2) a
    convert! (hasDerivAt_id a).neg.sub (((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).div_const (Real.sqrt 2)) using 1 <;> ring

theorem hermite_contact_jets (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hm : Profile.Valid D m) (r : Fin 4) :
    (hermitePolynomial s a m).eval (contacts a r)=phi s (contacts a r) ∧
    HasDerivAt (fun t => (hermitePolynomial s a m).eval t) (potentialJet s 1 (contacts a r)) (contacts a r) := by
  have h := (hermite_minorant s a D m hs ha hm).2
  fin_cases r
  · exact h 4 (by decide)
  · exact h 2 (by decide)
  · exact h 3 (by decide)
  · exact h 1 (by decide)

theorem contact_jet_stationarity (s a : ℝ) :
    8*(potentialJet s 1 (contacts a 0)*contactSlope 0)+
      4*(potentialJet s 1 (contacts a 1)*contactSlope 1)+
      8*(potentialJet s 1 (contacts a 2)*contactSlope 2)+
      8*(potentialJet s 1 (contacts a 3)*contactSlope 3)=F s a/2 := by
  have hq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ)≠0 := by positivity
  have hi : (Real.sqrt (2 : ℝ))⁻¹=Real.sqrt 2/2 := by
    field_simp
    nlinarith
  have hA : 2-2*contacts a 0=dA a := by change 2-2*a=2*(1-a);ring
  have hB : 2-2*contacts a 1=dB a := by change 2-2*(2*a-1)=4*(1-a);ring
  have hC : 2-2*contacts a 2=dC a := by
    change 2-2*(-a+(1-a)/Real.sqrt 2)=2-Real.sqrt 2+(2+Real.sqrt 2)*a
    rw [div_eq_mul_inv,hi]
    ring
  have hD : 2-2*contacts a 3=dD a := by
    change 2-2*(-a-(1-a)/Real.sqrt 2)=2+Real.sqrt 2+(2-Real.sqrt 2)*a
    rw [div_eq_mul_inv,hi]
    ring
  simp only [potentialJet_one,hA,hB,hC,hD]
  change 8*((dA a)^(-1-s/2)*1)+4*((dB a)^(-1-s/2)*2)+
    8*((dC a)^(-1-s/2)*(-1-1/Real.sqrt 2))+
    8*((dD a)^(-1-s/2)*(-1+1/Real.sqrt 2))=F s a/2
  rw [show -1-s/2= -(1+s/2) by ring]
  simp only [F,one_div,hi]
  ring

theorem hermite_candidate_pair_value (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hm : Profile.Valid D m) :
    polyPairEnergy (hermitePolynomial s a m) (X a)=Ehat s (X a) := by
  unfold polyPairEnergy Ehat
  rw [candidate_pair_sum a ha (fun t => (hermitePolynomial s a m).eval t),
    candidate_pair_sum a ha (phi s)]
  simp only [fun r => (hermite_contact_jets s a D m hs ha hm r).1]

theorem hermite_candidate_pair_derivative (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hm : Profile.Valid D m) :
    HasDerivAt (fun b => polyPairEnergy (hermitePolynomial s a m) (X b)) (F s a/2) a := by
  have h (r : Fin 4) := ((hermite_contact_jets s a D m hs ha hm r).2).comp a (hasDerivAt_contact a r)
  have hd := (((h 0).const_mul 8).add ((h 1).const_mul 4)).add ((h 2).const_mul 8) |>.add ((h 3).const_mul 8)
  rw [contact_jet_stationarity] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [physical_eventually a ha] with b hb
  exact candidate_pair_sum b hb (fun t => (hermitePolynomial s a m).eval t)

def TargetAnnihilationContract : Prop := ∀ s a D m,0 ≤ s → physical a → F s a=0 →
  Profile.Valid D m → ∀ β : ℝ,L0 a (normalizedTarget s a β m)=0 ∧ L1 a (normalizedTarget s a β m)=0

theorem compatibility_target_annihilation : TargetAnnihilationContract := by
  intro s a D m hs ha hF hm β
  have hv := hermite_candidate_pair_value s a D m hs ha hm
  have hd := hermite_candidate_pair_derivative s a D m hs ha hm
  constructor
  · rw [L0_eq_distinctPolySum a ha,normalizedTarget_distinctSum,hv,sub_self,mul_zero]
  · have ht : HasDerivAt (fun b => distinctPolySum (X b) (normalizedTarget s a β m))
        (12*β*(F s a/2)) a := by
      convert! (hd.sub_const (Ehat s (X a))).const_mul (12*β) using 1
      funext b
      exact normalizedTarget_distinctSum s a β m (X b)
    have he := (compatibility_family_functionals a ha (normalizedTarget s a β m)).2.unique ht
    rw [hF] at he
    simpa using he

#check compatibility_target_annihilation
#print axioms compatibility_target_annihilation
end Blueprint.Thomson.Finite
