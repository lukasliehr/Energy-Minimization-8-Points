import AllS.Units.N_FI.N_raw_projection.N_power_recurrences
import AllS.Units.N_FI.N_quotient.N_inverse_laws
import AllS.Units.N_FI.N_certificate.N_balanced_target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

/-- Newton power-sum polynomial in the invariant-coordinate variables σ,b,c. -/
def rawInvariantPowerSum : ℕ → Poly3
  | 0 => 3
  | 1 => MvPolynomial.X 0
  | 2 => MvPolynomial.X 0^2-2*MvPolynomial.X 1
  | n+3 => MvPolynomial.X 0*rawInvariantPowerSum (n+2)-
      MvPolynomial.X 1*rawInvariantPowerSum (n+1)+MvPolynomial.X 2*rawInvariantPowerSum n

theorem rawInvariantPowerSum_subst (n : ℕ) :
    invariantSubst (rawInvariantPowerSum n)=rawPowerSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · simp only [rawInvariantPowerSum,rawPowerSum,map_ofNat,pow_zero]
      ring
    · simp [rawInvariantPowerSum,rawPowerSum,invariantSubst,sigma]
    · simp only [rawInvariantPowerSum,map_sub,map_mul,map_pow,map_ofNat]
      simpa [invariantSubst] using rawPowerSum_initial.2.2.symm
    · rw [rawInvariantPowerSum,map_add,map_sub,map_mul,map_mul,map_mul,
        ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      simpa [invariantSubst] using (rawPowerSum_recurrence n).symm

theorem rawPowerSum_symmetric (n : ℕ) : (rawPowerSum n).IsSymmetric := by
  rw [← rawInvariantPowerSum_subst]
  exact invariantSubst_symmetric _

/-- Identification uses injectivity of the invariant substitution, so no
computed inverse or coefficient array is trusted. -/
theorem bounded_coordinates_of_invariantSubst (D : ℕ) (p : boundedSymmetric D)
    (q : Poly3) (hq : invariantSubst q=p.val) (t : TagIndex D) :
    ((sympoly_finite_equivalence D).symm p) t=MvPolynomial.coeff (tagExponent t.val) q := by
  let c := (sympoly_finite_equivalence D).symm p
  have hc : invariantSubst (rawInvariantSynthesis D c)=p.val :=
    congrArg Subtype.val ((sympoly_finite_equivalence D).apply_symm_apply p)
  have he : rawInvariantSynthesis D c=q := invariantSubst_injective (hc.trans hq.symm)
  rw [← he,coeff_rawInvariantSynthesis]

theorem retained_coordinates_of_invariantSubst (D : ℕ) (p : boundedSymmetric D)
    (q : Poly3) (hq : invariantSubst q=p.val) (t : RetainedIndex D) :
    retainedCoordinates D p t=MvPolynomial.coeff (tagExponent t.val) q :=
  bounded_coordinates_of_invariantSubst D p q hq (retainedInclusion D t)

def rawInvariantAverage (H : Polynomial ℝ) : Poly3 :=
  ∑ n ∈ Finset.range (H.natDegree+1),(H.coeff n/3) • rawInvariantPowerSum n

theorem averagedPolynomial_powerSum (H : Polynomial ℝ) :
    averagedPolynomial H=∑ n ∈ Finset.range (H.natDegree+1),(H.coeff n/3) • rawPowerSum n := by
  unfold averagedPolynomial univariateLift
  simp only [Polynomial.aeval_eq_sum_range]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply MvPolynomial.funext
  intro x
  simp [rawPowerSum,Algebra.smul_def]
  ring

theorem rawInvariantAverage_subst (H : Polynomial ℝ) :
    invariantSubst (rawInvariantAverage H)=averagedPolynomial H := by
  rw [averagedPolynomial_powerSum]
  simp only [rawInvariantAverage,map_sum,map_smul,rawInvariantPowerSum_subst]

def rawInvariantTarget (H : Polynomial ℝ) (β energy : ℝ) : Poly3 :=
  β • rawInvariantAverage H-MvPolynomial.C (β*energy/28)

theorem rawInvariantTarget_subst (H : Polynomial ℝ) (β energy : ℝ) :
    invariantSubst (rawInvariantTarget H β energy)=MvPolynomial.C β*centeredPolynomial H energy := by
  simp only [rawInvariantTarget,map_sub,map_smul,rawInvariantAverage_subst]
  simp only [invariantSubst,MvPolynomial.aeval_C]
  apply MvPolynomial.funext
  intro x
  simp [centeredPolynomial,Algebra.smul_def]
  ring

theorem rawPowerSum_degree (n : ℕ) : (rawPowerSum n).totalDegree≤n := by
  have hx (i : Fin 3) : ((MvPolynomial.X i:Poly3)^n).totalDegree≤n := by
    simpa using (MvPolynomial.totalDegree_pow (MvPolynomial.X i:Poly3) n)
  exact polyDegree_add_le _ _ n (polyDegree_add_le _ _ n (hx 0) (hx 1)) (hx 2)

theorem averagedPolynomial_degree (H : Polynomial ℝ) :
    (averagedPolynomial H).totalDegree≤H.natDegree := by
  rw [averagedPolynomial_powerSum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  exact ((MvPolynomial.totalDegree_smul_le _ _).trans (rawPowerSum_degree n)).trans
    (by have := Finset.mem_range.mp hn;omega)

def boundedNormalizedPolynomial (D : ℕ) (H : Polynomial ℝ) (hd : H.natDegree≤D)
    (β energy : ℝ) : boundedSymmetric D :=
  ⟨MvPolynomial.C β*centeredPolynomial H energy,(mem_boundedSymmetric D _).mpr ⟨by
    rw [← rawInvariantTarget_subst]
    exact invariantSubst_symmetric _,by
    apply (polyDegree_C_mul_le _ _).trans
    exact polyDegree_sub_le _ _ D ((averagedPolynomial_degree H).trans hd) (by simp)⟩⟩

theorem retained_tagExponent_ne_zero (D : ℕ) (t : RetainedIndex D) : tagExponent t.val≠0 := by
  intro he
  have ht := congrArg exponentTag he
  have hz : t.val=(0,0,0) := (exponentTag_tagExponent t.val).symm.trans ht
  exact (mem_RetainedTags.mp t.property).2.1 hz

def RawTargetDirectionsContract : Prop := ∀ (D : ℕ) (H : Polynomial ℝ) (hd : H.natDegree≤D)
    (β energy : ℝ) (t : RetainedIndex D),
  retainedCoordinates D (boundedNormalizedPolynomial D H hd β energy) t=
    ∑ n ∈ Finset.range (H.natDegree+1),β*H.coeff n/3*
      MvPolynomial.coeff (tagExponent t.val) (rawInvariantPowerSum n)

theorem raw_projection_target_directions : RawTargetDirectionsContract := by
  intro D H hd β energy t
  rw [retained_coordinates_of_invariantSubst D _ (rawInvariantTarget H β energy)
    (rawInvariantTarget_subst H β energy)]
  simp only [rawInvariantTarget,rawInvariantAverage,MvPolynomial.coeff_sub,
    MvPolynomial.coeff_smul,MvPolynomial.coeff_sum,MvPolynomial.coeff_C,
    if_neg (Ne.symm (retained_tagExponent_ne_zero D t)),sub_zero,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem rawPowerSum_homogeneous (n : ℕ) : (rawPowerSum n).IsHomogeneous n := by
  have hx (i : Fin 3) : ((MvPolynomial.X i:Poly3)^n).IsHomogeneous n := by
    simpa using (MvPolynomial.isHomogeneous_X ℝ i).pow n
  exact ((hx 0).add (hx 1)).add (hx 2)

theorem rawInvariantPowerSum_weighted_component (n : ℕ) :
    MvPolynomial.weightedHomogeneousComponent invariantWeight n (rawInvariantPowerSum n)=
      rawInvariantPowerSum n := by
  apply invariantSubst_injective
  rw [sympoly_component_commutation,rawInvariantPowerSum_subst,
    MvPolynomial.homogeneousComponent_of_mem (rawPowerSum_homogeneous n)]
  simp only [ite_true,rawInvariantPowerSum_subst]

theorem rawInvariantPowerSum_coeff_zero (n : ℕ) (t : Tag) (hn : tagWeight t≠n) :
    MvPolynomial.coeff (tagExponent t) (rawInvariantPowerSum n)=0 := by
  have h := congrArg (MvPolynomial.coeff (tagExponent t)) (rawInvariantPowerSum_weighted_component n)
  simpa only [MvPolynomial.coeff_weightedHomogeneousComponent,weight_tagExponent,if_neg hn]
    using h.symm

theorem raw_projection_target_coordinate (D : ℕ) (H : Polynomial ℝ) (hd : H.natDegree≤D)
    (β energy : ℝ) (t : RetainedIndex D) :
    retainedCoordinates D (boundedNormalizedPolynomial D H hd β energy) t=
      β*H.coeff (tagWeight t.val)/3*
        MvPolynomial.coeff (tagExponent t.val) (rawInvariantPowerSum (tagWeight t.val)) := by
  rw [raw_projection_target_directions]
  apply Finset.sum_eq_single (tagWeight t.val)
  · intro n hn hne
    rw [rawInvariantPowerSum_coeff_zero n t.val (Ne.symm hne),mul_zero]
  · intro hout
    have hw : H.natDegree<tagWeight t.val := by
      have hh : ¬tagWeight t.val<H.natDegree+1 := fun h=>hout (Finset.mem_range.mpr h)
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hw]
    ring

#print axioms raw_projection_target_directions
#print axioms raw_projection_target_coordinate
end Blueprint.Thomson.Finite
