import AllS.Units.N_F.N_contact_interpolation

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def invariantKernelFeature (a : ℝ) (t : Tag) : Poly3 :=
  invariantMonomial t-invariantProjector a (invariantMonomial t)
def signKernelFeature (a : ℝ) (t : Tag) : Poly3 :=
  deltaPoly*invariantMonomial t-alternatingProjector a (invariantMonomial t)
def standardInputF (t : StandardTag) : Poly3 := if t.1 then 0 else invariantMonomial t.2
def standardInputG (t : StandardTag) : Poly3 := if t.1 then invariantMonomial t.2 else 0

def standardKernelComponent (a : ℝ) (t : StandardTag) (i : Fin 3) : Poly3 :=
  standardComponent (standardInputF t) (standardInputG t) i-
    standardProjector a (standardInputF t) (standardInputG t) i
def standardKernelFeature (minus : Bool) (a : ℝ) (t : StandardTag) : Poly3 :=
  if minus then standardKernelComponent a t 1-standardKernelComponent a t 2
  else standardKernelComponent a t 0

def invariantKernelCoefficients (a : ℝ) (t : Tag) : Fin 5 → ℝ :=
  fun i => (scalarLagrange (contactSigma a) (orbitData a (invariantMonomial t))).coeff i.val
def signKernelCoefficients (a : ℝ) (t : Tag) : Fin 2 → ℝ :=
  fun i => (scalarLagrange (signSigmaNodes a)
    (fun r => orbitData a (invariantMonomial t) (regularOrbit r))).coeff i.val
def standardKernelFCoefficients (a : ℝ) (t : StandardTag) : Fin 4 → ℝ :=
  fun i => (standardFStar a (orbitData a (standardInputF t))
    (orbitData a (standardInputG t))).coeff i.val
def standardKernelGCoefficients (a : ℝ) (t : StandardTag) : Fin 3 → ℝ :=
  fun i => (standardGStar a (orbitData a (standardInputF t))
    (orbitData a (standardInputG t))).coeff i.val

def standardPivotP (minus : Bool) (i : ℕ) : Poly3 :=
  (if minus then standardPPoly 1-standardPPoly 2 else standardPPoly 0)*sigma^i
def standardPivotQ (minus : Bool) (i : ℕ) : Poly3 :=
  (if minus then standardQPoly 1-standardQPoly 2 else standardQPoly 0)*sigma^i

def S3VanishingContract : Prop := ∀ a : ℝ, physical a →
  (∀ t r σ, MvPolynomial.eval (permutedContact a r σ) (invariantKernelFeature a t)=0) ∧
  (∀ t r σ, MvPolynomial.eval (permutedContact a r σ) (signKernelFeature a t)=0) ∧
  (∀ b t r σ, MvPolynomial.eval (permutedContact a r σ) (standardKernelFeature b a t)=0) ∧
  (∀ t, invariantKernelFeature a t = invariantMonomial t-
    ∑ i : Fin 5, MvPolynomial.C (invariantKernelCoefficients a t i)*sigma^i.val) ∧
  (∀ t, signKernelFeature a t = deltaPoly*invariantMonomial t-
    ∑ i : Fin 2, MvPolynomial.C (signKernelCoefficients a t i)*(deltaPoly*sigma^i.val)) ∧
  (∀ b t, standardKernelFeature b a t = standardRawFeature b t-
    (∑ i : Fin 4, MvPolynomial.C (standardKernelFCoefficients a t i)*standardPivotP b i.val)-
    (∑ i : Fin 3, MvPolynomial.C (standardKernelGCoefficients a t i)*standardPivotQ b i.val))

theorem invariantMonomial_symmetric (t : Tag) : (invariantMonomial t).IsSymmetric := by
  have h := invariantSubst_symmetric (MvPolynomial.monomial (tagExponent t) (1 : ℝ))
  simpa [invariantSubst_monomial,tagExponent,invariantMonomial] using h

theorem standardInputF_symmetric (t : StandardTag) : (standardInputF t).IsSymmetric := by
  cases ht : t.1 <;> simp only [standardInputF,ht,Bool.false_eq_true,if_false,if_true]
  · exact invariantMonomial_symmetric _
  · intro σ; simp

theorem standardInputG_symmetric (t : StandardTag) : (standardInputG t).IsSymmetric := by
  cases ht : t.1 <;> simp only [standardInputG,ht,Bool.false_eq_true,if_false,if_true]
  · intro σ; simp
  · exact invariantMonomial_symmetric _

theorem invariantKernelFeature_vanish (a : ℝ) (ha : physical a) (t : Tag)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (invariantKernelFeature a t)=0 := by
  rw [invariantKernelFeature,map_sub,invariantProjector_eval a ha _ (invariantMonomial_symmetric t),sub_self]

theorem signKernelFeature_vanish (a : ℝ) (ha : physical a) (t : Tag)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (signKernelFeature a t)=0 := by
  rw [signKernelFeature,map_sub,alternatingProjector_eval a ha _ (invariantMonomial_symmetric t),sub_self]

theorem standardKernelComponent_vanish (a : ℝ) (ha : physical a) (t : StandardTag)
    (i : Fin 3) (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (standardKernelComponent a t i)=0 := by
  rw [standardKernelComponent,map_sub,standardProjector_eval a ha _ _
    (standardInputF_symmetric t) (standardInputG_symmetric t),sub_self]

theorem standardKernelFeature_vanish (b : Bool) (a : ℝ) (ha : physical a) (t : StandardTag)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (standardKernelFeature b a t)=0 := by
  cases b <;> simp [standardKernelFeature,standardKernelComponent_vanish a ha]

theorem polyLift_sigma_expansion (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree < n) :
    polyLift p sigma = ∑ i : Fin n, MvPolynomial.C (p.coeff i.val)*sigma^i.val := by
  unfold polyLift
  rw [Polynomial.eval₂_eq_sum_range' MvPolynomial.C hp sigma]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

theorem invariantKernelFeature_expansion (a : ℝ) (ha : physical a) (t : Tag) :
    invariantKernelFeature a t = invariantMonomial t-
      ∑ i : Fin 5, MvPolynomial.C (invariantKernelCoefficients a t i)*sigma^i.val := by
  unfold invariantKernelFeature invariantProjector invariantInterpolant invariantKernelCoefficients
  rw [polyLift_sigma_expansion _ 5 (by
    have h := scalarLagrange_natDegree _ (orbitData a (invariantMonomial t)) (contactSigma_injective a ha)
    omega)]

theorem signKernelFeature_expansion (a : ℝ) (ha : physical a) (t : Tag) :
    signKernelFeature a t = deltaPoly*invariantMonomial t-
      ∑ i : Fin 2, MvPolynomial.C (signKernelCoefficients a t i)*(deltaPoly*sigma^i.val) := by
  unfold signKernelFeature alternatingProjector alternatingInterpolant signKernelCoefficients
  rw [polyLift_sigma_expansion _ 2 (by
    have h := scalarLagrange_natDegree _ (fun r => orbitData a (invariantMonomial t) (regularOrbit r))
      (signSigmaNodes_injective a ha)
    omega),Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem standardRawFeature_component (b : Bool) (t : StandardTag) :
    standardRawFeature b t = if b then
      standardComponent (standardInputF t) (standardInputG t) 1-
      standardComponent (standardInputF t) (standardInputG t) 2
    else standardComponent (standardInputF t) (standardInputG t) 0 := by
  cases ht : t.1 <;> cases b <;>
    simp [standardRawFeature,standardComponent,standardInputF,standardInputG,ht]
  all_goals ring

theorem standardProjector_component_expansion (a : ℝ) (ha : physical a) (t : StandardTag) (j : Fin 3) :
    standardProjector a (standardInputF t) (standardInputG t) j =
      (∑ i : Fin 4, MvPolynomial.C (standardKernelFCoefficients a t i)*(standardPPoly j*sigma^i.val))+
      (∑ i : Fin 3, MvPolynomial.C (standardKernelGCoefficients a t i)*(standardQPoly j*sigma^i.val)) := by
  unfold standardProjector standardComponent standardKernelFCoefficients standardKernelGCoefficients
  have hF := standardFStar_degree a ha (orbitData a (standardInputF t)) (orbitData a (standardInputG t))
  have hG := standardGStar_degree a ha (orbitData a (standardInputF t)) (orbitData a (standardInputG t))
  rw [polyLift_sigma_expansion _ 4 (by omega),polyLift_sigma_expansion _ 3 (by omega)]
  simp only [Finset.mul_sum]
  congr 1
  all_goals apply Finset.sum_congr rfl
  all_goals intro i hi; ring

theorem standardKernelFeature_expansion (b : Bool) (a : ℝ) (ha : physical a) (t : StandardTag) :
    standardKernelFeature b a t = standardRawFeature b t-
      (∑ i : Fin 4, MvPolynomial.C (standardKernelFCoefficients a t i)*standardPivotP b i.val)-
      (∑ i : Fin 3, MvPolynomial.C (standardKernelGCoefficients a t i)*standardPivotQ b i.val) := by
  rw [standardRawFeature_component]
  cases b
  · simp only [standardKernelFeature,standardKernelComponent,standardProjector_component_expansion a ha,
      Bool.false_eq_true,if_false,standardPivotP,standardPivotQ]
    ring
  · simp only [standardKernelFeature,standardKernelComponent,standardProjector_component_expansion a ha,
      if_true,standardPivotP,standardPivotQ,sub_mul,mul_sub,Finset.sum_sub_distrib]
    ring

theorem kernels_s3_vanishing : S3VanishingContract := by
  intro a ha
  exact ⟨invariantKernelFeature_vanish a ha,signKernelFeature_vanish a ha,
    fun b => standardKernelFeature_vanish b a ha,invariantKernelFeature_expansion a ha,
    signKernelFeature_expansion a ha,fun b => standardKernelFeature_expansion b a ha⟩

#check kernels_s3_vanishing
#print axioms kernels_s3_vanishing

#check S3VanishingContract
#print axioms S3VanishingContract
end Blueprint.Thomson.Finite
