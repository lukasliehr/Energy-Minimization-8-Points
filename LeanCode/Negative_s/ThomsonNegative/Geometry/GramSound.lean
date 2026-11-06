import ThomsonNegative.Geometry.Moments
import ThomsonNegative.Structure.Basic

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThomsonNegative.Geometry
open GenericMoments

def WeightedOuterRep {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ N : ℕ,∃ w : Fin N → ℝ,∃ v : Fin N → Fin n → ℝ,
    (∀ t,0 ≤ w t) ∧ M=∑ t,w t • Matrix.vecMulVec (v t) (v t)


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


def gramMatrixPairing {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i,∑ j,W i j*M i j


theorem gramMatrixPairing_sum {n : ℕ} {ι : Type*}
    (W : Matrix (Fin n) (Fin n) ℝ) (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℝ) :
    gramMatrixPairing W (∑ t∈s,f t)=∑ t∈s,gramMatrixPairing W (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gramMatrixPairing]
  | @insert t s ht h =>
    simp only [Finset.sum_insert ht]
    rw [show gramMatrixPairing W (f t+∑ x∈s,f x)=
        gramMatrixPairing W (f t)+gramMatrixPairing W (∑ x∈s,f x) by
      simp [gramMatrixPairing,mul_add,Finset.sum_add_distrib]]
    rw [h]

theorem gramMatrixPairing_smul {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    gramMatrixPairing W (c • M)=c*gramMatrixPairing W M := by
  simp only [gramMatrixPairing,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gramMatrixPairing_outer {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    gramMatrixPairing W (Matrix.vecMulVec v v)=dotProduct v (W.mulVec v) := by
  simp only [gramMatrixPairing,Matrix.vecMulVec,Matrix.of_apply,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gramMatrixPairing_nonneg {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.PosSemidef) (hM : WeightedOuterRep M) : 0 ≤ gramMatrixPairing W M := by
  obtain ⟨N,w,v,hw,rfl⟩ := hM
  rw [gramMatrixPairing_sum]
  apply Finset.sum_nonneg
  intro t ht
  rw [gramMatrixPairing_smul,gramMatrixPairing_outer]
  exact mul_nonneg (hw t) (by simpa only [star_trivial] using hW.dotProduct_mulVec_nonneg (v t))


def sphericalTriple (Y : Configuration) (i j k : Fin 8) : Fin 3 → ℝ :=
  ![inner ℝ (Y i) (Y j),inner ℝ (Y i) (Y k),inner ℝ (Y j) (Y k)]

def polyOnTriples (Y : Configuration) (p : Poly3) (i j k : Fin 8) : ℝ :=
  MvPolynomial.eval (sphericalTriple Y i j k) p

def distinctPolySum (Y : Configuration) (p : Poly3) : ℝ := DistinctSum (polyOnTriples Y p)

def distinctMatrixSum {n : ℕ} (Y : Configuration)
    (P : Matrix (Fin n) (Fin n) Poly3) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => distinctPolySum Y (P i j)

/-- Exact algebraic meanings of the two retained block families. A realization
contains only scalar evaluation identities, never a positivity or energy claim. -/
inductive BlockRealization {m : ℕ} (P : Matrix (Fin m) (Fin m) Poly3) : Prop
  | moment (n k : ℕ) (B : Matrix (Fin n) (Fin m) ℝ)
      (evaluation : ∀ (i j : Fin m) (u : Fin 3 → ℝ), MvPolynomial.eval u (P i j)=
        ∑ r : Fin n, ∑ s : Fin n, B r i*Rfun k r.val s.val (u 0) (u 1) (u 2)*B s j) :
      BlockRealization P
  | sos (n : ℕ) (w : Fin n → ℝ) (v : Fin n → (Fin 3 → ℝ) → Fin m → ℝ)
      (weights : ∀ r, 0 ≤ w r)
      (evaluation : ∀ (i j : Fin m) (u : Fin 3 → ℝ), MvPolynomial.eval u (P i j)=
        ∑ r, w r*v r u i*v r u j) : BlockRealization P

lemma distinctSum_sum {ι : Type*} [Fintype ι] (f : ι → Fin 8 → Fin 8 → Fin 8 → ℝ) :
    DistinctSum (fun i j k => ∑ t, f t i j k)=∑ t,DistinctSum (f t) := by
  let L : (Fin 8 → Fin 8 → Fin 8 → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := DistinctSum
      map_add' := distinctSum_add
      map_smul' := fun c f => by
        change DistinctSum (fun i j k => c*f i j k)=c*DistinctSum f
        exact distinctSum_mul c f }
  have hh := map_sum L f Finset.univ
  change DistinctSum (∑ t,f t)=∑ t,DistinctSum (f t) at hh
  convert hh using 1
  congr 1
  funext i j k
  simp only [Finset.sum_apply]

lemma distinctPolySum_add (Y : Configuration) (p r : Poly3) :
    distinctPolySum Y (p+r)=distinctPolySum Y p+distinctPolySum Y r := by
  unfold distinctPolySum polyOnTriples
  simp only [map_add]
  exact distinctSum_add _ _

lemma distinctPolySum_C_mul (Y : Configuration) (c : ℝ) (p : Poly3) :
    distinctPolySum Y (MvPolynomial.C c*p)=c*distinctPolySum Y p := by
  unfold distinctPolySum polyOnTriples
  simp only [map_mul,MvPolynomial.eval_C]
  exact distinctSum_mul _ _

lemma distinctPolySum_sum {ι : Type*} [Fintype ι] (Y : Configuration) (p : ι → Poly3) :
    distinctPolySum Y (∑ i,p i)=∑ i,distinctPolySum Y (p i) := by
  unfold distinctPolySum polyOnTriples
  simp only [map_sum]
  exact distinctSum_sum _

lemma genericMoment_outer (m k : ℕ) (Y : Configuration) (hY : ∀ i,‖Y i‖=1) :
    WeightedOuterRep (momentMatrix m k Y) := by
  obtain ⟨v,w,h⟩ := momentMatrix_exists_outer_products m k Y hY
  have he : momentMatrix m k Y=∑ t : Fin 8 × Fin 2,(1:ℝ) • Matrix.vecMulVec
      (if t.2=0 then v t.1 else w t.1) (if t.2=0 then v t.1 else w t.1) := by
    rw [h]
    ext r c
    simp [Fintype.sum_prod_type,Fin.sum_univ_succ,Matrix.vecMulVec,Matrix.sum_apply]
  rw [he]
  exact weightedOuterRep_of_sum _ _ (by intro t;norm_num)

lemma moment_block_sum {m n : ℕ} (P : Matrix (Fin m) (Fin m) Poly3) (k : ℕ)
    (B : Matrix (Fin n) (Fin m) ℝ)
    (heval : ∀ (i j : Fin m) (u : Fin 3 → ℝ), MvPolynomial.eval u (P i j)=
      ∑ r : Fin n,∑ s : Fin n,B r i*Rfun k r.val s.val (u 0) (u 1) (u 2)*B s j)
    (Y : Configuration) (hY : ∀ i,‖Y i‖=1) :
    distinctMatrixSum Y P=(6:ℝ) • (B.transpose*momentMatrix n k Y*B) := by
  ext i j
  unfold distinctMatrixSum distinctPolySum polyOnTriples
  simp only [heval]
  rw [distinctSum_sum]
  simp_rw [distinctSum_sum]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.transpose_apply,
    Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have he : (fun x y z => B r i*Rfun k r.val s.val
      ((sphericalTriple Y x y z) 0) ((sphericalTriple Y x y z) 1) ((sphericalTriple Y x y z) 2)*B s j)=
      (fun x y z => (B r i*B s j)*onTriples Y (Rfun k r.val s.val) x y z) := by
    funext x y z
    dsimp [sphericalTriple,onTriples]
    ring
  rw [he]
  calc
    _ = (B r i*B s j)*distinctSum (onTriples Y (Rfun k r.val s.val)) :=
      distinctSum_mul _ _
    _ = _ := by rw [sum_Rfun_eq_moment n k Y hY r s]; ring

lemma sos_block_outer {m n : ℕ} (P : Matrix (Fin m) (Fin m) Poly3)
    (w : Fin n → ℝ) (v : Fin n → (Fin 3 → ℝ) → Fin m → ℝ) (hw : ∀ r,0 ≤ w r)
    (heval : ∀ (i j : Fin m) (u : Fin 3 → ℝ), MvPolynomial.eval u (P i j)=∑ r,w r*v r u i*v r u j)
    (Y : Configuration) : WeightedOuterRep (distinctMatrixSum Y P) := by
  let wt : Fin 8 × Fin 8 × Fin 8 × Fin n → ℝ := fun t =>
    if t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2.1 ∧ t.2.2.1 ≠ t.1 then w t.2.2.2 else 0
  let vt : Fin 8 × Fin 8 × Fin 8 × Fin n → Fin m → ℝ := fun t =>
    v t.2.2.2 (sphericalTriple Y t.1 t.2.1 t.2.2.1)
  have hwt (t) : 0 ≤ wt t := by dsimp [wt]; split_ifs; exact hw _; norm_num
  have he : distinctMatrixSum Y P=∑ t,wt t • Matrix.vecMulVec (vt t) (vt t) := by
    ext i j
    simp only [distinctMatrixSum,distinctPolySum,polyOnTriples,heval,DistinctSum,
      Fintype.sum_prod_type,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [wt,vt]
    split_ifs <;> simp [Finset.mul_sum,mul_assoc]
  rw [he]
  exact weightedOuterRep_of_sum wt vt hwt

lemma block_outer {m : ℕ} (P : Matrix (Fin m) (Fin m) Poly3) (hP : BlockRealization P)
    (Y : Configuration) (hY : ∀ i,‖Y i‖=1) : WeightedOuterRep (distinctMatrixSum Y P) := by
  cases hP with
  | moment n k B heval =>
    rw [moment_block_sum P k B heval Y hY]
    apply weightedOuterRep_smul _ _ 6 (by norm_num)
    simpa using weightedOuterRep_congruence _ (genericMoment_outer n k Y hY) B.transpose
  | sos n w v hw heval => exact sos_block_outer P w v hw heval Y

lemma distinct_gramPolynomial (Y : Configuration) (P : Structure.PolynomialFamily)
    (W : Structure.GramFamily) :
    distinctPolySum Y (Structure.gramPolynomial P W)=
      ∑ b,gramMatrixPairing (W b) (distinctMatrixSum Y (P b)) := by
  simp only [Structure.gramPolynomial,distinctPolySum_sum,distinctPolySum_C_mul,
    gramMatrixPairing,distinctMatrixSum]

/-- All retained moment and SOS blocks are nonnegative on spherical
configurations. No cell-specific geometric positivity hypothesis is needed. -/
theorem gramPolynomial_nonneg (P : Structure.PolynomialFamily)
    (hP : ∀ b,BlockRealization (P b)) (W : Structure.GramFamily)
    (hW : ∀ b,(W b).PosSemidef) (Y : Configuration) (hY : ∀ i,‖Y i‖=1) :
    0 ≤ distinctPolySum Y (Structure.gramPolynomial P W) := by
  rw [distinct_gramPolynomial]
  exact Finset.sum_nonneg (fun b _ => gramMatrixPairing_nonneg _ _ (hW b) (block_outer _ (hP b) Y hY))

#print axioms gramPolynomial_nonneg
end ThomsonNegative.Geometry
