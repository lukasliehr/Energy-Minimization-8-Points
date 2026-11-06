import AllS.Units.N_F.N_gram_map
import AllS.Units.N_F.N_counting
import AllS.Units.N_F.N_generic_moments
import AllS.Units.N_F.N_sympoly

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.Finite
open MvPolynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Explicit finite positive weighted outer-product representation. -/
def WeightedOuterRep {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ N : ℕ,∃ w : Fin N → ℝ,∃ v : Fin N → Fin n → ℝ,
    (∀ t,0 ≤ w t) ∧ M=∑ t,w t • Matrix.vecMulVec (v t) (v t)

def gramBlockMoment (Y : Configuration) (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d) :
    Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) ℝ :=
  fun i j => distinctPolySum Y (gramKernel a d p b i j)

def WeightedOuterProductsContract : Prop := ∀ Y : Configuration,(∀ i,‖Y i‖=1) →
  ∀ a d p b,WeightedOuterRep (gramBlockMoment Y a d p b)

theorem weightedOuterRep_of_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (v : ι → Fin n → ℝ) (hw : ∀ t,0 ≤ w t) :
    WeightedOuterRep (∑ t,w t • Matrix.vecMulVec (v t) (v t)) := by
  classical
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι,w ∘ e,v ∘ e,fun t => hw (e t),?_⟩
  exact (Equiv.sum_comp e (fun t => w t • Matrix.vecMulVec (v t) (v t))).symm

theorem weightedOuterRep_posSemidef {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : WeightedOuterRep M) : M.PosSemidef := by
  obtain ⟨N,w,v,hw,rfl⟩ := h
  apply Matrix.posSemidef_sum
  intro t ht
  have hv : (Matrix.vecMulVec (v t) (v t)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v t)
  exact hv.smul (hw t)

theorem weightedOuterRep_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : WeightedOuterRep M) (c : ℝ) (hc : 0 ≤ c) : WeightedOuterRep (c • M) := by
  obtain ⟨N,w,v,hw,rfl⟩ := h
  refine ⟨N,fun t => c*w t,v,fun t => mul_nonneg hc (hw t),?_⟩
  simp only [Finset.smul_sum,smul_smul]

theorem weightedOuterRep_congruence {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (h : WeightedOuterRep M) (B : Matrix (Fin n) (Fin m) ℝ) :
    WeightedOuterRep (B*M*B.transpose) := by
  obtain ⟨N,w,v,hw,rfl⟩ := h
  refine ⟨N,w,fun t => B.mulVec (v t),hw,?_⟩
  rw [Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul]
  congr 2
  ext i
  simp [Matrix.vecMul,Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm]

theorem canonicalMoment_outer (m k : ℕ) (Y : Configuration) (hY : ∀ i,‖Y i‖=1) :
    WeightedOuterRep (canonicalMoment m k Y) := by
  rw [canonicalMoment_eq_generic]
  obtain ⟨v,w,h⟩ := generic_moments_outer_product_identity m k Y hY
  have he : GenericMoments.momentMatrix m k Y=
      ∑ t : Fin 8 × Fin 2,(1 : ℝ) • Matrix.vecMulVec
        (if t.2=0 then v t.1 else w t.1) (if t.2=0 then v t.1 else w t.1) := by
    rw [h]
    ext r c
    simp [Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.vecMulVec,Matrix.sum_apply]
  rw [he]
  exact weightedOuterRep_of_sum _ _ (by intro t;norm_num)

theorem distinctPolySum_add (Y : Configuration) (f g : Poly3) :
    distinctPolySum Y (f+g)=distinctPolySum Y f+distinctPolySum Y g := by
  unfold distinctPolySum polyOnTriples
  simp only [map_add]
  exact GenericMoments.distinctSum_add _ _

theorem distinctPolySum_C_mul (Y : Configuration) (c : ℝ) (f : Poly3) :
    distinctPolySum Y (C c*f)=c*distinctPolySum Y f := by
  simp [distinctPolySum,polyOnTriples,DistinctSum,mul_ite,Finset.mul_sum]

theorem distinctPolySum_sum {ι : Type*} (Y : Configuration) (s : Finset ι) (f : ι → Poly3) :
    distinctPolySum Y (∑ i∈s,f i)=∑ i∈s,distinctPolySum Y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [distinctPolySum,polyOnTriples,DistinctSum]
  | @insert i s hi h => simp only [Finset.sum_insert hi,distinctPolySum_add,h]

theorem gramBlockMoment_moment (Y : Configuration) (hY : ∀ i,‖Y i‖=1)
    (a : ℝ) (d : ℕ) (p : MomentPivots d) (k : Fin d) :
    gramBlockMoment Y a d p (.inl k)=(6 : ℝ) •
      ((momentKernelMatrix a d p k).transpose*canonicalMoment (d-k.val+1) k.val Y*
        momentKernelMatrix a d p k) := by
  ext i j
  change Fin (d-k.val) at i j
  change distinctPolySum Y (momentBilinearKernel a d p k i j)=
    (6 : ℝ)*((momentKernelMatrix a d p k).transpose*canonicalMoment (d-k.val+1) k.val Y*
      momentKernelMatrix a d p k) i j
  simp only [momentBilinearKernel,distinctPolySum_sum,distinctPolySum_C_mul,
    counting_moment_identity _ _ Y hY,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,
    Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem determinantWeightPoly_isSymmetric : determinantWeightPoly.IsSymmetric := by
  have he : determinantWeightPoly=invariantSubst
      (1+C 2*MvPolynomial.X 2-MvPolynomial.X 0^2+C 2*MvPolynomial.X 1) := by
    simp [determinantWeightPoly,invariantSubst,sigma,e2,e3]
    norm_num only [map_ofNat]
    ring
  rw [he]
  exact invariantSubst_symmetric _

def sphericalTriple (x y z : Point) : Fin 3 → ℝ :=
  ![inner ℝ x y,inner ℝ x z,inner ℝ y z]

theorem scalarWeight_eval_nonneg (b : ScalarBlockName) (x y z : Point)
    (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) (σ : Equiv.Perm (Fin 3)) :
    0 ≤ MvPolynomial.eval (sphericalTriple x y z ∘ σ) (scalarWeightPoly b) := by
  have hedge : 0 ≤ MvPolynomial.eval (sphericalTriple x y z ∘ σ) edgeWeightPoly := by
    simp only [edgeWeightPoly,map_sub,map_one,map_pow,eval_X,Function.comp_apply]
    generalize he : σ 0=q
    fin_cases q
    · exact sub_nonneg.mpr (unit_inner_square_le_one x y hx hy)
    · exact sub_nonneg.mpr (unit_inner_square_le_one x z hx hz)
    · exact sub_nonneg.mpr (unit_inner_square_le_one y z hy hz)
  have hdet : 0 ≤ MvPolynomial.eval (sphericalTriple x y z ∘ σ) determinantWeightPoly := by
    rw [← MvPolynomial.eval_rename,determinantWeightPoly_isSymmetric σ]
    simpa only [sphericalTriple,determinantWeightPoly_eval] using gramDetScalar_nonneg x y z hx hy hz
  cases b <;> first | exact hedge | exact hdet | simp [scalarWeightPoly]

def scalarComponentWeight (b : ScalarBlockName) (c : Fin 2) : ℝ :=
  if c=0 then 1 else if scalarBlockStandard b then 1/3 else 0

theorem scalarComponentWeight_nonneg (b : ScalarBlockName) (c : Fin 2) :
    0 ≤ scalarComponentWeight b c := by
  unfold scalarComponentWeight
  split_ifs <;> norm_num

theorem eval_reynolds_sum (x : Fin 3 → ℝ) (f : Poly3) :
    MvPolynomial.eval x (reynolds f)=(1/6 : ℝ)*
      ∑ σ : Equiv.Perm (Fin 3),MvPolynomial.eval (x ∘ σ) f := by
  simp only [reynolds,LinearMap.smul_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply,
    MvPolynomial.smul_eval,map_sum,MvPolynomial.eval_rename,smul_eq_mul,one_div]

theorem scalarBilinearKernel_eval (x : Fin 3 → ℝ) (b : ScalarBlockName) (a : ℝ) (d : ℕ)
    (i j : Fin (scalarBlockDimension b d)) :
    MvPolynomial.eval x (scalarBilinearKernel b a d i j)=
      ∑ σ : Equiv.Perm (Fin 3),∑ c : Fin 2,
        (1/6 : ℝ)*MvPolynomial.eval (x ∘ σ) (scalarWeightPoly b)*scalarComponentWeight b c*
          MvPolynomial.eval (x ∘ σ) (scalarFeature b a d c i)*
          MvPolynomial.eval (x ∘ σ) (scalarFeature b a d c j) := by
  rw [scalarBilinearKernel,eval_reynolds_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Fin.sum_univ_two]
  simp only [scalarComponentWeight,eq_self_iff_true,if_true,if_neg (show (1 : Fin 2)≠0 by decide),
    map_mul,map_add,eval_C]
  ring

abbrev ScalarOuterIndex := (Fin 8 × Fin 8 × Fin 8) × Equiv.Perm (Fin 3) × Fin 2

def scalarOuterWeight (Y : Configuration) (b : ScalarBlockName) (t : ScalarOuterIndex) : ℝ :=
  if t.1.1≠t.1.2.1 ∧ t.1.2.1≠t.1.2.2 ∧ t.1.2.2≠t.1.1 then
    (1/6)*MvPolynomial.eval
      (sphericalTriple (Y t.1.1) (Y t.1.2.1) (Y t.1.2.2) ∘ t.2.1) (scalarWeightPoly b)*
      scalarComponentWeight b t.2.2 else 0

def scalarOuterVector (Y : Configuration) (b : ScalarBlockName) (a : ℝ) (d : ℕ)
    (t : ScalarOuterIndex) (i : Fin (scalarBlockDimension b d)) : ℝ :=
  MvPolynomial.eval (sphericalTriple (Y t.1.1) (Y t.1.2.1) (Y t.1.2.2) ∘ t.2.1)
    (scalarFeature b a d t.2.2 i)

theorem scalarOuterWeight_nonneg (Y : Configuration) (hY : ∀ i,‖Y i‖=1)
    (b : ScalarBlockName) (t : ScalarOuterIndex) : 0 ≤ scalarOuterWeight Y b t := by
  unfold scalarOuterWeight
  split_ifs
  · exact mul_nonneg (mul_nonneg (by norm_num) (scalarWeight_eval_nonneg b _ _ _
      (hY _) (hY _) (hY _) _)) (scalarComponentWeight_nonneg b _)
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
theorem gramBlockMoment_scalar (Y : Configuration) (a : ℝ) (d : ℕ) (p : MomentPivots d)
    (b : ScalarBlockName) : gramBlockMoment Y a d p (.inr b)=
      ∑ t : ScalarOuterIndex,scalarOuterWeight Y b t • Matrix.vecMulVec
        (scalarOuterVector Y b a d t) (scalarOuterVector Y b a d t) := by
  ext i j
  change Fin (scalarBlockDimension b d) at i j
  change distinctPolySum Y (scalarBilinearKernel b a d i j)=
    (∑ t : ScalarOuterIndex,scalarOuterWeight Y b t • Matrix.vecMulVec
      (scalarOuterVector Y b a d t) (scalarOuterVector Y b a d t)) i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec,Matrix.of_apply]
  simp only [distinctPolySum,DistinctSum,polyOnTriples,scalarBilinearKernel_eval,
    Fintype.sum_prod_type,Matrix.sum_apply,Finset.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec,
    scalarOuterWeight,scalarOuterVector,sphericalTriple]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : x≠y ∧ y≠z ∧ z≠x
  · rw [if_pos h]
    simp_rw [if_pos h]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro c hc
    ring
  · rw [if_neg h]
    simp_rw [if_neg h]
    simp

theorem moment_pos_weighted_outer_products : WeightedOuterProductsContract := by
  intro Y hY a d p b
  cases b with
  | inl k =>
    rw [gramBlockMoment_moment Y hY]
    have h := weightedOuterRep_congruence _ (canonicalMoment_outer (d-k.val+1) k.val Y hY)
      (momentKernelMatrix a d p k).transpose
    simp only [Matrix.transpose_transpose] at h
    exact weightedOuterRep_smul _ h 6 (by norm_num)
  | inr b =>
    rw [gramBlockMoment_scalar]
    exact weightedOuterRep_of_sum _ _ (scalarOuterWeight_nonneg Y hY b)

#check moment_pos_weighted_outer_products
#print axioms moment_pos_weighted_outer_products
end Blueprint.Thomson.Finite
