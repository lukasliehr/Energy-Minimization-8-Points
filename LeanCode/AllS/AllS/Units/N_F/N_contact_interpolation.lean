import AllS.Units.N_FI.N_contact_interpolation.N_kernel_projector

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def ContactInterpolationContract : Prop := KernelProjectorContract ∧
  (∀ a : ℝ, physical a →
    (∀ p : Poly3, (invariantProjector a p).totalDegree ≤ 4) ∧
    (∀ p : Poly3, (alternatingProjector a p).totalDegree ≤ 4) ∧
    (∀ F G : Poly3, ∀ i, (standardProjector a F G i).totalDegree ≤ 4)) ∧
  (∀ a : ℝ, ∀ F G : Poly3, ∀ (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) i,
    MvPolynomial.eval (x ∘ σ) (standardProjector a F G i) =
      MvPolynomial.eval x (standardProjector a F G (σ i)))

theorem polyLift_sigma_degree (p : Polynomial ℝ) : (polyLift p sigma).totalDegree ≤ p.natDegree := by
  unfold polyLift
  rw [Polynomial.eval₂_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (polyDegree_C_mul_le _ _).trans
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have h1 := Nat.mul_le_mul_left i sigma_degree
  have h2 := Finset.mem_range.mp hi
  omega

theorem scalarLagrange_natDegree {n : ℕ} (z : Fin n → ℝ) (v : Fin n → ℝ)
    (hz : Function.Injective z) : (scalarLagrange z v).natDegree ≤ n-1 := by
  by_cases hp : scalarLagrange z v=0
  · simp [hp]
  have h : (scalarLagrange z v).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (scalarLagrange_degree z v hz)
  omega

theorem invariantProjector_degree (a : ℝ) (ha : physical a) (p : Poly3) :
    (invariantProjector a p).totalDegree ≤ 4 :=
  (polyLift_sigma_degree _).trans
    (scalarLagrange_natDegree _ _ (contactSigma_injective a ha))

theorem alternatingProjector_degree (a : ℝ) (ha : physical a) (p : Poly3) :
    (alternatingProjector a p).totalDegree ≤ 4 := by
  have h : (polyLift (scalarLagrange (signSigmaNodes a)
      (fun r => orbitData a p (regularOrbit r))) sigma).totalDegree ≤ 1 :=
    (polyLift_sigma_degree _).trans
      (scalarLagrange_natDegree _ _ (signSigmaNodes_injective a ha))
  exact polyDegree_mul_le _ _ 3 1 deltaPoly_degree h

theorem standardProjector_degree (a : ℝ) (ha : physical a) (F G : Poly3) (i : Fin 3) :
    (standardProjector a F G i).totalDegree ≤ 4 := by
  apply polyDegree_add_le
  · exact polyDegree_mul_le _ _ 1 3 (standardPPoly_degree i)
      ((polyLift_sigma_degree _).trans (standardFStar_degree a ha _ _))
  · exact polyDegree_mul_le _ _ 2 2 (standardQPoly_degree i)
      ((polyLift_sigma_degree _).trans (standardGStar_degree a ha _ _))

theorem sigma_eval_permute (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (x ∘ σ) sigma = MvPolynomial.eval x sigma := by
  simp only [sigma_eval,Function.comp_apply]
  exact Equiv.sum_comp σ x

theorem standardProjector_permute (a : ℝ) (F G : Poly3)
    (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    MvPolynomial.eval (x ∘ σ) (standardProjector a F G i) =
      MvPolynomial.eval x (standardProjector a F G (σ i)) := by
  simp only [standardProjector,standardComponent_eval,polyLift_eval,
    standardP_permute,standardQ_permute,sigma_eval_permute]

/-- The source standard-coordinate matrices, derived from the zero-sum relation. -/
theorem standard_coordinate_action (z : Fin 3 → ℝ) (hz : (∑ i,z i)=0) :
    z 1 = -(1/2 : ℝ)*z 0+(1/2 : ℝ)*(z 1-z 2) ∧
    z 2-z 0 = -(3/2 : ℝ)*z 0-(1/2 : ℝ)*(z 1-z 2) ∧
    z 2-z 1 = -(z 1-z 2) := by
  simp [Fin.sum_univ_succ] at hz
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem standardProjector_sum_zero (a : ℝ) (F G : Poly3) (x : Fin 3 → ℝ) :
    (∑ i,MvPolynomial.eval x (standardProjector a F G i))=0 := by
  simp only [standardProjector,standardComponent_eval,Finset.sum_add_distrib,
    ← Finset.sum_mul,standardP_sum,standardQ_sum,zero_mul,add_zero]

theorem contact_interpolation : ContactInterpolationContract := by
  refine ⟨contact_interpolation_kernel_projector,?_,standardProjector_permute⟩
  intro a ha
  exact ⟨invariantProjector_degree a ha,alternatingProjector_degree a ha,standardProjector_degree a ha⟩

#check contact_interpolation
#print axioms contact_interpolation
#check standard_coordinate_action
#print axioms standard_coordinate_action

#check ContactInterpolationContract
#print axioms ContactInterpolationContract
end Blueprint.Thomson.Finite
