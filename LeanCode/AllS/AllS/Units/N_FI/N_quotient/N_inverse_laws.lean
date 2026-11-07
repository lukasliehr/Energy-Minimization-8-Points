import AllS.Units.N_FI.N_quotient.N_recover

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

def restrictRetained (D : ℕ) : (TagIndex D → ℝ) →ₗ[ℝ] (RetainedIndex D → ℝ) where
  toFun c t := c (retainedInclusion D t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def retainedCoordinates (D : ℕ) : boundedSymmetric D →ₗ[ℝ] (RetainedIndex D → ℝ) :=
  (restrictRetained D).comp (sympoly_finite_equivalence D).symm.toLinearMap

def compatibleToBounded (a : ℝ) (D : ℕ) : Compatible a D →ₗ[ℝ] boundedSymmetric D :=
  Submodule.inclusion (by
    intro f hf
    exact (mem_boundedSymmetric D f).mpr ⟨((mem_Compatible a D f).mp hf).1,
      ((mem_Compatible a D f).mp hf).2.1⟩)

def retainCompatible (a : ℝ) (D : ℕ) : Compatible a D →ₗ[ℝ] (RetainedIndex D → ℝ) :=
  (retainedCoordinates D).comp (compatibleToBounded a D)

@[simp] theorem restrict_extendRetained (D : ℕ) (x : RetainedIndex D → ℝ) :
    restrictRetained D (extendRetained D x)=x := by
  funext t
  simp only [restrictRetained,extendRetained,LinearMap.coe_mk,AddHom.coe_mk,retainedInclusion]
  exact dif_pos t.property

theorem retainedInclusion_ne_zero (D : ℕ) (t : RetainedIndex D) :
    retainedInclusion D t≠zeroTag D := by
  intro h
  exact (mem_RetainedTags.mp t.property).2.1 (congrArg Subtype.val h)

theorem retainedInclusion_ne_square (D : ℕ) (hD : 2≤D) (t : RetainedIndex D) :
    retainedInclusion D t≠squareTag D hD := by
  intro h
  exact (mem_RetainedTags.mp t.property).2.2 (congrArg Subtype.val h)

@[simp] theorem restrict_single_zero (D : ℕ) (c : ℝ) :
    restrictRetained D (Pi.single (zeroTag D) c)=0 := by
  classical
  funext t
  simp [restrictRetained,Pi.single_apply,retainedInclusion_ne_zero]

@[simp] theorem restrict_single_square (D : ℕ) (hD : 2≤D) (c : ℝ) :
    restrictRetained D (Pi.single (squareTag D hD) c)=0 := by
  classical
  funext t
  simp [restrictRetained,Pi.single_apply,retainedInclusion_ne_square]

theorem restrict_recoveredCoordinates (a : ℝ) (D : ℕ) (hD : 2≤D)
    (x : RetainedIndex D → ℝ) :
    restrictRetained D (recoveredCoordinates a D hD x)=x := by
  simp [recoveredCoordinates]

theorem coordinates_decomposition (D : ℕ) (hD : 2≤D) (c : TagIndex D → ℝ) :
    extendRetained D (restrictRetained D c)+Pi.single (squareTag D hD) (c (squareTag D hD))+
      Pi.single (zeroTag D) (c (zeroTag D))=c := by
  classical
  funext t
  by_cases h0 : t=zeroTag D
  · subst t
    simp [extendRetained,zeroTag,mem_RetainedTags,Pi.single_apply,squareTag]
  by_cases h2 : t=squareTag D hD
  · subst t
    simp [extendRetained,zeroTag,mem_RetainedTags,Pi.single_apply,squareTag]
  have hv0 : t.val≠(0,0,0) := fun h=>h0 (Subtype.ext h)
  have hv2 : t.val≠(2,0,0) := fun h=>h2 (Subtype.ext h)
  have hr : t.val∈RetainedTags D := mem_RetainedTags.mpr
    ⟨mem_InvariantTags.mp t.property,hv0,hv2⟩
  simp [extendRetained,restrictRetained,retainedInclusion,hr,Pi.single_apply,h0,h2]

theorem bounded_polynomial_decomposition (D : ℕ) (hD : 2≤D) (f : boundedSymmetric D) :
    retainedSynthesis D (retainedCoordinates D f)+
      ((sympoly_finite_equivalence D).symm f) (squareTag D hD) • sigma^2+
      ((sympoly_finite_equivalence D).symm f) (zeroTag D) • (1 : Poly3)=f.val := by
  have he := congrArg (invariantSynthesis D)
    (coordinates_decomposition D hD ((sympoly_finite_equivalence D).symm f))
  simp only [map_add,invariantSynthesis_single,squareTag,zeroTag,
    invariantMonomial_square,invariantMonomial_zero] at he
  refine he.trans ?_
  exact congrArg Subtype.val ((sympoly_finite_equivalence D).apply_symm_apply f)

theorem recoveredPolynomial_retain (a : ℝ) (ha : physical a) (D : ℕ) (hD : 2≤D)
    (f : Compatible a D) : recoveredPolynomial a D (retainCompatible a D f)=f.val := by
  let fB := compatibleToBounded a D f
  let x := retainedCoordinates D fB
  let c := (sympoly_finite_equivalence D).symm fB
  have he : retainedSynthesis D x+c (squareTag D hD) • sigma^2+
      c (zeroTag D) • (1 : Poly3)=f.val := bounded_polynomial_decomposition D hD fB
  have hf := (mem_Compatible a D f.val).mp f.property
  have h0 : ell0 a f.val=0 := by simp [ell0,hf.2.2.1]
  have h1 : ell1 a f.val=0 := by simp [ell1,hf.2.2.2]
  rcases compatibility_low_values a ha with ⟨h01,h11,h02,h12,hn,_⟩
  have hz0 := congrArg (ell0 a) he
  have hz1 := congrArg (ell1 a) he
  simp only [map_add,map_smul,smul_eq_mul,h01,h11,h02,h12,h0,h1,mul_zero,add_zero] at hz0 hz1
  have hc2 : recoverySigmaCoefficient a D x=c (squareTag D hD) := by
    unfold recoverySigmaCoefficient
    apply (div_eq_iff (by nlinarith [ha.2] : 128*(3*a-1)≠0)).mpr
    linarith
  have hc0 : recoveryConstantCoefficient a D x=c (zeroTag D) := by
    unfold recoveryConstantCoefficient
    rw [hc2]
    apply (div_eq_iff (by norm_num : (56 : ℝ)≠0)).mpr
    linarith
  change recoveredPolynomial a D x=f.val
  rw [recoveredPolynomial,hc2,hc0]
  exact he

theorem retainedCoordinates_recoveredPolynomial (a : ℝ) (D : ℕ) (hD : 2≤D)
    (x : RetainedIndex D → ℝ) :
    retainedCoordinates D ⟨recoveredPolynomial a D x,recoveredPolynomial_bounded a D hD x⟩=x := by
  have he : (⟨recoveredPolynomial a D x,recoveredPolynomial_bounded a D hD x⟩ : boundedSymmetric D)=
      sympoly_finite_equivalence D (recoveredCoordinates a D hD x) := by
    apply Subtype.ext
    exact (invariantSynthesis_recoveredCoordinates a D hD x).symm
  rw [he]
  change restrictRetained D ((sympoly_finite_equivalence D).symm
    (sympoly_finite_equivalence D (recoveredCoordinates a D hD x)))=x
  rw [LinearEquiv.symm_apply_apply]
  exact restrict_recoveredCoordinates a D hD x

def recoveryLinearMap (a : ℝ) (D : ℕ) : (RetainedIndex D → ℝ) →ₗ[ℝ] Poly3 where
  toFun := recoveredPolynomial a D
  map_add' x y := by
    have hs : recoverySigmaCoefficient a D (x+y)=recoverySigmaCoefficient a D x+recoverySigmaCoefficient a D y := by
      simp only [recoverySigmaCoefficient,map_add]
      ring
    have hc : recoveryConstantCoefficient a D (x+y)=recoveryConstantCoefficient a D x+recoveryConstantCoefficient a D y := by
      simp only [recoveryConstantCoefficient,hs,map_add]
      ring
    simp only [recoveredPolynomial,hs,hc,map_add,add_smul]
    module
  map_smul' r x := by
    have hs : recoverySigmaCoefficient a D (r • x)=r*recoverySigmaCoefficient a D x := by
      simp only [recoverySigmaCoefficient,map_smul,smul_eq_mul]
      ring
    have hc : recoveryConstantCoefficient a D (r • x)=r*recoveryConstantCoefficient a D x := by
      simp only [recoveryConstantCoefficient,hs,map_smul,smul_eq_mul]
      ring
    simp only [recoveredPolynomial,hs,hc,map_smul,mul_smul,smul_add]
    rfl

def recoveryCompatible (a : ℝ) (ha : physical a) (D : ℕ) (hD : 2≤D) :
    (RetainedIndex D → ℝ) →ₗ[ℝ] Compatible a D :=
  (recoveryLinearMap a D).codRestrict (Compatible a D) (quotient_recover a ha D hD)

theorem quotient_inverse_laws (a : ℝ) (ha : physical a) (D : ℕ) (hD : 2≤D) :
    (∀ f : Compatible a D,recoveryCompatible a ha D hD (retainCompatible a D f)=f) ∧
    (∀ x : RetainedIndex D → ℝ,retainCompatible a D (recoveryCompatible a ha D hD x)=x) := by
  constructor
  · intro f
    apply Subtype.ext
    exact recoveredPolynomial_retain a ha D hD f
  · intro x
    exact retainedCoordinates_recoveredPolynomial a D hD x

#check quotient_inverse_laws
#print axioms quotient_inverse_laws
end Blueprint.Thomson.Finite
