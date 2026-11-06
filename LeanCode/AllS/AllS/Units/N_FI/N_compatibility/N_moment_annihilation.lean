import AllS.Units.N_FI.N_compatibility.N_family_functionals
import AllS.Units.N_F.N_moment_pos
import AllS.Units.N_FI.N_certificate.N_typed_contract
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem L1_zero_of_candidate_minimum (a : ℝ) (ha : physical a) (f : Poly3)
    (hz : L0 a f=0) (hn : ∀ b,physical b → 0 ≤ distinctPolySum (X b) f) : L1 a f=0 := by
  have hm : IsLocalMin (fun b => distinctPolySum (X b) f) a := by
    filter_upwards [physical_eventually a ha] with b hb
    rw [← L0_eq_distinctPolySum a ha f,hz]
    exact hn b hb
  exact hm.hasDerivAt_eq_zero (compatibility_family_functionals a ha f).2

def gramKernelQuadratic (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (v : Fin (gramBlockDimension d b) → ℝ) : Poly3 :=
  ∑ i,∑ j,(v i*v j) • gramKernel a d p b i j

theorem linear_gramKernelQuadratic (L : Poly3 →ₗ[ℝ] ℝ)
    (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (v : Fin (gramBlockDimension d b) → ℝ) :
    L (gramKernelQuadratic a d p b v)=
      dotProduct v (Matrix.mulVec (fun i j => L (gramKernel a d p b i j)) v) := by
  simp only [gramKernelQuadratic,map_sum,map_smul,smul_eq_mul,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem distinct_gramKernelQuadratic (Y : Configuration)
    (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (v : Fin (gramBlockDimension d b) → ℝ) :
    distinctPolySum Y (gramKernelQuadratic a d p b v)=
      dotProduct v ((gramBlockMoment Y a d p b).mulVec v) := by
  have hsm (c : ℝ) (f : Poly3) : distinctPolySum Y (c • f)=c*distinctPolySum Y f := by
    rw [← MvPolynomial.C_mul',distinctPolySum_C_mul]
  simp only [gramKernelQuadratic,distinctPolySum_sum,hsm,Matrix.mulVec,dotProduct,
    gramBlockMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem candidate_momentKernelMatrix_zero (a : ℝ) (ha : physical a)
    (d : ℕ) (hd : d≤9) (p : MomentPivots d) (hp : ValidMomentPivots p) (k : Fin d) :
    canonicalMoment (d-k.val+1) k.val (X a)*momentKernelMatrix a d p k=0 := by
  have hm := (candidate_moment_nullspace a ha (d-k.val+1) k.val (by omega) (p k) (hp k)).2.1
  ext r i
  exact congrFun (congrFun hm r) (finSuccAboveEquiv (p k) i)

theorem candidate_momentBlock_zero (a : ℝ) (ha : physical a)
    (d : ℕ) (hd : d≤9) (p : MomentPivots d) (hp : ValidMomentPivots p) (k : Fin d) :
    gramBlockMoment (X a) a d p (.inl k)=0 := by
  rw [gramBlockMoment_moment _ (candidate_is_configuration a (physical_mem_Ioo a ha)).1,
    Matrix.mul_assoc,candidate_momentKernelMatrix_zero a ha d hd p hp k,Matrix.mul_zero,smul_zero]
  rfl

theorem symmetric_matrix_zero_of_quadratic_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hz : ∀ v : Fin n → ℝ,dotProduct v (M.mulVec v)=0) : M=0 := by
  classical
  have hd (i : Fin n) : M i i=0 := by
    simpa only [Matrix.mulVec_single_one,single_one_dotProduct,Matrix.col,Matrix.transpose_apply] using hz (Pi.single i 1)
  ext i j
  have h := hz (Pi.single i 1+Pi.single j 1)
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,Matrix.mulVec_single_one,
    single_one_dotProduct,Matrix.col,Matrix.transpose_apply,hd,zero_add,add_zero] at h
  have hs := hM.apply i j
  change M i j=0
  linarith

def MomentAnnihilationContract : Prop := ∀ a,physical a → ∀ d,d≤9 →
  ∀ p : MomentPivots d,ValidMomentPivots p → ∀ k : Fin d,∀ i j : Fin (d-k.val),
    L0 a (momentBilinearKernel a d p k i j)=0 ∧ L1 a (momentBilinearKernel a d p k i j)=0

theorem compatibility_moment_annihilation : MomentAnnihilationContract := by
  intro a ha d hd p hp k
  have hblock := candidate_momentBlock_zero a ha d hd p hp k
  have hz0 (i j : Fin (d-k.val)) : L0 a (momentBilinearKernel a d p k i j)=0 := by
    rw [L0_eq_distinctPolySum a ha]
    exact congrFun (congrFun hblock i) j
  let M : Matrix (Fin (d-k.val)) (Fin (d-k.val)) ℝ :=
    fun i j => L1 a (momentBilinearKernel a d p k i j)
  have hsym : M.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change L1 a (gramKernel a d p (.inl k) j i)=L1 a (gramKernel a d p (.inl k) i j)
    exact congrArg (L1 a) (gramKernel_transpose a d p (.inl k) j i)
  have hquad (v : Fin (d-k.val) → ℝ) : dotProduct v (M.mulVec v)=0 := by
    change Fin (gramBlockDimension d (.inl k)) → ℝ at v
    have hq := linear_gramKernelQuadratic (L1 a) a d p (.inl k) v
    change L1 a (gramKernelQuadratic a d p (.inl k) v)=dotProduct v (M.mulVec v) at hq
    refine hq.symm.trans ?_
    apply L1_zero_of_candidate_minimum a ha
    · rw [L0_eq_distinctPolySum a ha,distinct_gramKernelQuadratic,hblock,Matrix.zero_mulVec,dotProduct_zero]
    · intro b hb
      rw [distinct_gramKernelQuadratic]
      have hpsd := weightedOuterRep_posSemidef _ (moment_pos_weighted_outer_products (X b)
        (candidate_is_configuration b (physical_mem_Ioo b hb)).1 a d p (.inl k))
      simpa only [star_trivial] using hpsd.dotProduct_mulVec_nonneg v
  have hz1 := symmetric_matrix_zero_of_quadratic_zero M hsym hquad
  intro i j
  exact ⟨hz0 i j,congrFun (congrFun hz1 i) j⟩

#check compatibility_moment_annihilation
#print axioms compatibility_moment_annihilation
end Blueprint.Thomson.Finite
