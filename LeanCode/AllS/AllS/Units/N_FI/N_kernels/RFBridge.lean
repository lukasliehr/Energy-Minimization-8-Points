import AllS.Units.N_F.N_kernels
import AllS.Units.N_AI.N_correction_linkage.N_all_input_identity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Auxiliary exact linkage between source RF columns and the proved canonical
interpolation operators. Literal data are checked separately. -/
noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
namespace RFBridge
set_option maxHeartbeats 0

def coefficientPolynomial {n : ℕ} (c : Fin n → ℝ) : Polynomial ℝ :=
  ∑ i,Polynomial.C (c i)*Polynomial.X^i.val

theorem coefficientPolynomial_eval {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    (coefficientPolynomial c).eval x=∑ i,c i*x^i.val := by
  simp [coefficientPolynomial,Polynomial.eval_finsetSum]

theorem coefficientPolynomial_coeff {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    (coefficientPolynomial c).coeff i.val=c i := by
  classical
  simp only [coefficientPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : i.val≠j.val := fun h=>hji (Fin.ext h.symm)
    simp [hne]
  · simp

theorem coefficientPolynomial_degree {n : ℕ} (c : Fin n → ℝ) :
    (coefficientPolynomial c).degree<n := Polynomial.degree_sum_fin_lt c

theorem coefficientPolynomial_natDegree {n : ℕ} (c : Fin (n+1) → ℝ) :
    (coefficientPolynomial c).natDegree≤n := by
  by_cases h : coefficientPolynomial c=0
  · simp [h]
  have hd := (Polynomial.natDegree_lt_iff_degree_lt h).mpr (coefficientPolynomial_degree c)
  omega

theorem scalar_coefficient_unique {n : ℕ} (z v c : Fin n → ℝ) (hz : Function.Injective z)
    (he : ∀ r,∑ i,c i*z r^i.val=v r) :
    ∀ i,(scalarLagrange z v).coeff i.val=c i := by
  have hvalues : v=fun r=>(coefficientPolynomial c).eval (z r) := by
    funext r
    rw [coefficientPolynomial_eval,he]
  rw [hvalues,scalarLagrange_fix z hz _ (coefficientPolynomial_degree c)]
  exact coefficientPolynomial_coeff c

theorem invariant_coefficients_unique (a : ℝ) (ha : physical a) (t : Tag)
    (c : Fin 5 → ℝ)
    (he : ∀ r,∑ i,c i*contactSigma a r^i.val=orbitData a (invariantMonomial t) r) :
    invariantKernelCoefficients a t=c := by
  funext i
  exact scalar_coefficient_unique _ _ c (contactSigma_injective a ha) he i

theorem sign_coefficients_unique (a : ℝ) (ha : physical a) (t : Tag)
    (c : Fin 2 → ℝ)
    (he : ∀ r,∑ i,c i*signSigmaNodes a r^i.val=orbitData a (invariantMonomial t) (regularOrbit r)) :
    signKernelCoefficients a t=c := by
  funext i
  exact scalar_coefficient_unique _ _ c (signSigmaNodes_injective a ha) he i

theorem standard_coefficients_unique (a : ℝ) (ha : physical a) (t : StandardTag)
    (cF : Fin 4 → ℝ) (cG : Fin 3 → ℝ)
    (hr : ∀ r : Fin 2,
      (∑ i,cF i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputF t) (regularOrbit r) ∧
      (∑ i,cG i*contactSigma a (regularOrbit r)^i.val)=orbitData a (standardInputG t) (regularOrbit r))
    (he : ∀ r : Fin 3,
      (∑ i,cF i*contactSigma a (Fin.castAdd 2 r)^i.val)+
        repeatedLambda a r*(∑ i,cG i*contactSigma a (Fin.castAdd 2 r)^i.val)=
      orbitData a (standardInputF t) (Fin.castAdd 2 r)+
        repeatedLambda a r*orbitData a (standardInputG t) (Fin.castAdd 2 r)) :
    standardKernelFCoefficients a t=cF ∧ standardKernelGCoefficients a t=cG := by
  let F := orbitData a (standardInputF t)
  let G := orbitData a (standardInputG t)
  have hr0 : ∀ r : Fin 2,
      (standardFStar a F G-coefficientPolynomial cF).eval (contactSigma a (regularOrbit r))=0 ∧
      (standardGStar a F G-coefficientPolynomial cG).eval (contactSigma a (regularOrbit r))=0 := by
    intro r
    obtain ⟨hf,hg⟩ := standard_interpolant_regular a ha F G r
    simp only [Polynomial.eval_sub,coefficientPolynomial_eval,hf,hg]
    exact ⟨sub_eq_zero.mpr (hr r).1.symm,sub_eq_zero.mpr (hr r).2.symm⟩
  have he0 : ∀ r : Fin 3,
      (standardFStar a F G-coefficientPolynomial cF).eval (contactSigma a (Fin.castAdd 2 r))+
        repeatedLambda a r*(standardGStar a F G-coefficientPolynomial cG).eval
          (contactSigma a (Fin.castAdd 2 r))=0 := by
    intro r
    have hs := standard_interpolant_repeated a ha F G r
    have hc := he r
    simp only [Polynomial.eval_sub,coefficientPolynomial_eval]
    dsimp [F,G] at hs
    linear_combination hs-hc
  obtain ⟨hF,hG⟩ := standard_zero_unique a ha _ _
    ((Polynomial.natDegree_sub_le _ _).trans (max_le (standardFStar_degree a ha F G)
      (coefficientPolynomial_natDegree cF)))
    ((Polynomial.natDegree_sub_le _ _).trans (max_le (standardGStar_degree a ha F G)
      (coefficientPolynomial_natDegree cG))) hr0 he0
  constructor
  · funext i
    change (standardFStar a F G).coeff i.val=cF i
    rw [sub_eq_zero.mp hF,coefficientPolynomial_coeff]
  · funext i
    change (standardGStar a F G).coeff i.val=cG i
    rw [sub_eq_zero.mp hG,coefficientPolynomial_coeff]

#print axioms invariant_coefficients_unique
#print axioms sign_coefficients_unique
#print axioms standard_coefficients_unique


def parityIndexTag (odd : Bool) (r : ParityIndex odd) : Tag := (r.1.val,r.2.val,0)

set_option maxRecDepth 100000 in
theorem parityIndexTag_mem : ∀ odd (r : ParityIndex odd),
    parityIndexTag odd r∈(parityPivotTags odd).toFinset := by decide

def parityTagMap (odd : Bool) (r : ParityIndex odd) :
    {t : Tag // t∈(parityPivotTags odd).toFinset} :=
  ⟨parityIndexTag odd r,parityIndexTag_mem odd r⟩

set_option maxRecDepth 100000 in
theorem parityTagMap_bijective : ∀ odd,Function.Bijective (parityTagMap odd) := by decide

def parityPivotEquiv (odd : Bool) : ParityIndex odd ≃ {t : Tag // t∈(parityPivotTags odd).toFinset} :=
  Equiv.ofBijective (parityTagMap odd) (parityTagMap_bijective odd)

theorem parityIndexTag_injective (odd : Bool) : Function.Injective (parityIndexTag odd) := by
  intro r s he
  exact (parityTagMap_bijective odd).1 (Subtype.ext he)

def parityIndexedSynthesis (odd : Bool) : (ParityIndex odd → ℝ) →ₗ[ℝ] Poly3 where
  toFun c := ∑ r,c r • parityBiPivot (parityIndexTag odd r)
  map_add' c d := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by simp [Pi.smul_apply,Finset.smul_sum,smul_smul]

theorem parityIndexedSynthesis_eq (odd : Bool) (c : Tag → ℝ) :
    parityIndexedSynthesis odd (fun r=>c (parityIndexTag odd r))=parityBiSynthesis odd c := by
  classical
  change (∑ r,c (parityIndexTag odd r) • parityBiPivot (parityIndexTag odd r))=
    ∑ t∈(parityPivotTags odd).toFinset,c t • parityBiPivot t
  refine Finset.sum_bij (fun r _=>parityIndexTag odd r) ?_ ?_ ?_ ?_
  · intro r hr
    exact parityIndexTag_mem odd r
  · intro r hr s hs he
    exact parityIndexTag_injective odd he
  · intro t ht
    obtain ⟨r,hr⟩ := (parityTagMap_bijective odd).2 ⟨t,ht⟩
    exact ⟨r,Finset.mem_univ _,congrArg Subtype.val hr⟩
  · intro r hr
    rfl

def parityEvaluation (a : ℝ) (odd : Bool) : Poly3 →ₗ[ℝ] (ParityIndex odd → ℝ) where
  toFun p r := parityBiEval p (parityFiberU a odd r.1) (parityFiberZ a odd r.1 r.2)
  map_add' p q := by funext r; simp [parityBiEval]
  map_smul' c p := by funext r; simp [parityBiEval]

def parityEvaluationMatrix (a : ℝ) (odd : Bool) :
    (ParityIndex odd → ℝ) →ₗ[ℝ] (ParityIndex odd → ℝ) :=
  (parityEvaluation a odd).comp (parityIndexedSynthesis odd)

theorem parityEvaluationMatrix_surjective (a : ℝ) (ha : physical a) (odd : Bool) :
    Function.Surjective (parityEvaluationMatrix a odd) := by
  intro v
  let V : ParityData odd := fun i j=>v ⟨i,j⟩
  obtain ⟨c,hc⟩ := parityBiInterpolant_mem a ha odd V
  refine ⟨fun r=>c (parityIndexTag odd r),?_⟩
  change parityEvaluation a odd (parityIndexedSynthesis odd _)=v
  rw [parityIndexedSynthesis_eq]
  change parityEvaluation a odd (parityBiSynthesis odd c)=v
  rw [hc]
  funext r
  exact parityBiInterpolant_eval a ha odd V r.1 r.2

theorem parityEvaluationMatrix_injective (a : ℝ) (ha : physical a) (odd : Bool) :
    Function.Injective (parityEvaluationMatrix a odd) :=
  LinearMap.injective_iff_surjective.mpr (parityEvaluationMatrix_surjective a ha odd)

theorem parityEvaluation_injective_on_range (a : ℝ) (ha : physical a) (odd : Bool)
    {p q : Poly3} (hp : p∈parityBiRange odd) (hq : q∈parityBiRange odd)
    (he : parityEvaluation a odd p=parityEvaluation a odd q) : p=q := by
  obtain ⟨c,hc⟩ := hp
  obtain ⟨d,hd⟩ := hq
  have hec : parityEvaluationMatrix a odd (fun r=>c (parityIndexTag odd r))=
      parityEvaluationMatrix a odd (fun r=>d (parityIndexTag odd r)) := by
    change parityEvaluation a odd (parityIndexedSynthesis odd _)=
      parityEvaluation a odd (parityIndexedSynthesis odd _)
    rw [parityIndexedSynthesis_eq,parityIndexedSynthesis_eq,hc,hd]
    exact he
  have hcd := parityEvaluationMatrix_injective a ha odd hec
  have hpoly := congrArg (parityIndexedSynthesis odd) hcd
  simpa only [parityIndexedSynthesis_eq,hc,hd] using hpoly

theorem parity_interpolant_unique (a : ℝ) (ha : physical a) (odd : Bool)
    (V : ParityData odd) (p : Poly3) (hp : p∈parityBiRange odd)
    (he : ∀ i j,parityBiEval p (parityFiberU a odd i) (parityFiberZ a odd i j)=V i j) :
    parityBiInterpolant a odd V=p := by
  apply parityEvaluation_injective_on_range a ha odd
    (parityBiInterpolant_mem a ha odd V) hp
  funext r
  change parityBiEval (parityBiInterpolant a odd V) _ _=parityBiEval p _ _
  rw [parityBiInterpolant_eval a ha,he]

#print axioms parity_interpolant_unique


theorem parityIndexedSynthesis_mem (odd : Bool) (c : ParityIndex odd → ℝ) :
    parityIndexedSynthesis odd c∈parityBiRange odd := by
  change (∑ r,c r • parityBiPivot (parityIndexTag odd r))∈parityBiRange odd
  apply Submodule.sum_mem
  intro r hr
  exact (parityBiRange odd).smul_mem _
    (parityBiRange_pivot odd _ (parityIndexTag_mem odd r))

theorem parityIndexedSynthesis_eval (odd : Bool) (c : ParityIndex odd → ℝ) (u z : ℝ) :
    parityBiEval (parityIndexedSynthesis odd c) u z=∑ r,c r*u^r.1.val*z^r.2.val := by
  simp only [parityIndexedSynthesis,LinearMap.coe_mk,AddHom.coe_mk,parityBiEval,
    map_sum,map_smul,parityBiPivot,parityIndexTag,map_mul,map_pow,MvPolynomial.eval_X,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← MvPolynomial.C_mul']
  simp only [map_mul,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X]
  change c r*(u^r.1.val*z^r.2.val)=_
  ring

theorem parityIndexedSynthesis_coeff (odd : Bool) (c : ParityIndex odd → ℝ)
    (r : ParityIndex odd) :
    MvPolynomial.coeff (tagExponent (parityIndexTag odd r)) (parityIndexedSynthesis odd c)=c r := by
  classical
  change MvPolynomial.coeff _ (∑ s,c s • parityBiPivot (parityIndexTag odd s))=_
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul]
  rw [Finset.sum_eq_single r]
  · rw [parityBiPivot_monomial _ rfl]
    simp
  · intro s hs hsr
    rw [parityBiPivot_monomial _ rfl]
    have hn : tagExponent (parityIndexTag odd s)≠tagExponent (parityIndexTag odd r) :=
      fun h=>hsr (parityIndexTag_injective odd (tagExponent_injective h))
    simp [hn]
  · simp

theorem parity_coefficients_unique (a : ℝ) (ha : physical a) (odd : Bool) (t : Tag)
    (c : ParityIndex odd → ℝ)
    (he : ∀ i j, (∑ r,c r*(parityFiberU a odd i)^r.1.val*(parityFiberZ a odd i j)^r.2.val)=
      paritySourceData a odd t i j) :
    ∀ r,parityKernelCoefficients a odd t (parityIndexTag odd r)=c r := by
  have hpoly := parity_interpolant_unique a ha odd (paritySourceData a odd t)
    (parityIndexedSynthesis odd c) (parityIndexedSynthesis_mem odd c)
    (fun i j=>by rw [parityIndexedSynthesis_eval]; exact he i j)
  intro r
  unfold parityKernelCoefficients
  rw [hpoly,parityIndexedSynthesis_coeff]

#print axioms parity_coefficients_unique
end RFBridge
end Blueprint.Thomson.Finite
