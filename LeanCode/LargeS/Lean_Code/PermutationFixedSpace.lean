import Lean_Code.ScottInequality
import Lean_Code.PermutationPartition

noncomputable section
namespace SquareAntiprismVerification

variable {α : Type*} [Fintype α]

def permutationLinearMap (e : Equiv.Perm α) : EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ α where
  toFun v := WithLp.toLp 2 (fun i => v (e i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma permutationLinearMap_inner (e : Equiv.Perm α) (v w : EuclideanSpace ℝ α) :
    inner ℝ (permutationLinearMap e v) (permutationLinearMap e w) = inner ℝ v w := by
  classical
  simp only [PiLp.inner_apply]
  exact Equiv.sum_comp e (fun i => inner ℝ (v i) (w i))

def permutationIsometry (e : Equiv.Perm α) : EuclideanSpace ℝ α ≃ₗᵢ[ℝ] EuclideanSpace ℝ α :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := permutationLinearMap e
      norm_map' v := by
        have h := permutationLinearMap_inner e v v
        simp only [real_inner_self_eq_norm_sq] at h
        nlinarith [norm_nonneg (permutationLinearMap e v), norm_nonneg v] }
    (fun v => ⟨permutationLinearMap e.symm v, by
      ext i
      change v (e.symm (e i)) = v i
      rw [e.symm_apply_apply]⟩)

@[simp] lemma permutationIsometry_apply (e : Equiv.Perm α) (v : EuclideanSpace ℝ α) (i : α) :
    permutationIsometry e v i = v (e i) := rfl

theorem permutationIsometry_trans (e f : Equiv.Perm α) :
    (permutationIsometry f).trans (permutationIsometry e) = permutationIsometry (e.trans f) := by
  ext v i
  rfl

lemma permutation_fixed_sameCycle (e : Equiv.Perm α) (v : EuclideanSpace ℝ α)
    (hv : permutationIsometry e v = v) (x y : α) (hxy : e.SameCycle x y) : v x = v y := by
  classical
  have hstep (a : α) : v (e a) = v a := congrArg (fun w : EuclideanSpace ℝ α => w a) hv
  have hiter (n : ℕ) : v ((⇑e)^[n] x) = v x := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hstep, ih]
  obtain ⟨n, _, _, hn⟩ := Equiv.Perm.SameCycle.exists_pow_eq e hxy
  rw [Equiv.Perm.coe_pow] at hn
  exact (hiter n).symm.trans (congrArg v hn)

/-- Fixed vectors of a permutation are exactly functions on its cycles. -/
def permutationFixedEquiv (e : Equiv.Perm α) :
    (PermutationOrbit e → ℝ) ≃ₗ[ℝ] isometryFixed (permutationIsometry e) where
  toFun f := ⟨WithLp.toLp 2 (fun i => f (Quotient.mk (permutationOrbitSetoid e) i)), by
    change permutationIsometry e _ = _
    ext i
    change f (Quotient.mk (permutationOrbitSetoid e) (e i)) =
      f (Quotient.mk (permutationOrbitSetoid e) i)
    apply congrArg f
    exact Quotient.sound (Equiv.Perm.SameCycle.refl e i).apply_left⟩
  invFun v q := v.val q.out
  left_inv f := by
    funext q
    change f (Quotient.mk (permutationOrbitSetoid e) q.out) = f q
    rw [Quotient.out_eq]
  right_inv v := by
    apply Subtype.ext
    ext i
    change v.val (Quotient.mk (permutationOrbitSetoid e) i).out = v.val i
    have hq := (Quotient.mk (permutationOrbitSetoid e) i).out_eq
    have hxy : e.SameCycle (Quotient.mk (permutationOrbitSetoid e) i).out i := Quotient.exact hq
    exact permutation_fixed_sameCycle e v.val v.property _ i hxy
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permutation_fixed_finrank (e : Equiv.Perm α) :
    Module.finrank ℝ (isometryFixed (permutationIsometry e)) = Fintype.card (PermutationOrbit e) := by
  rw [← (permutationFixedEquiv e).finrank_eq]
  simp

/-- A cycle-count upper bound before specializing joint invariants to
constants on a connected contact graph. -/
theorem permutation_cycle_dimension_bound (e f : Equiv.Perm α) :
    Fintype.card (PermutationOrbit e) + Fintype.card (PermutationOrbit f) +
      Fintype.card (PermutationOrbit (e.trans f)) ≤ Fintype.card α +
        2 * Module.finrank ℝ ↥(isometryFixed (permutationIsometry e) ⊓
          isometryFixed (permutationIsometry f)) := by
  have h := isometry_fixed_dimension_inequality (permutationIsometry e) (permutationIsometry f)
  rw [permutationIsometry_trans, permutation_fixed_finrank, permutation_fixed_finrank,
    permutation_fixed_finrank] at h
  simpa using h

/-- Jointly invariant vectors are constant for a connected permutation
system. Evaluation at one element then bounds their dimension by one. -/
theorem permutation_common_fixed_finrank_le_one (e f : Equiv.Perm α) (a : α)
    (hconnected : ∀ v : EuclideanSpace ℝ α,
      (∀ i, v (e i) = v i) → (∀ i, v (f i) = v i) → ∀ i j, v i = v j) :
    Module.finrank ℝ ↥(isometryFixed (permutationIsometry e) ⊓
      isometryFixed (permutationIsometry f)) ≤ 1 := by
  let K := isometryFixed (permutationIsometry e) ⊓ isometryFixed (permutationIsometry f)
  let ev : K →ₗ[ℝ] ℝ := {
    toFun v := v.val a
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hconst (v : K) (i j : α) : v.val i = v.val j := by
    apply hconnected v.val
    · intro k
      exact congrArg (fun w : EuclideanSpace ℝ α => w k) v.property.1
    · intro k
      exact congrArg (fun w : EuclideanSpace ℝ α => w k) v.property.2
  have hinj : Function.Injective ev := by
    intro v w heq
    apply Subtype.ext
    ext i
    exact (hconst v i a).trans (heq.trans (hconst w i a).symm)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem connected_permutation_cycle_bound (e f : Equiv.Perm α) (a : α)
    (hconnected : ∀ v : EuclideanSpace ℝ α,
      (∀ i, v (e i) = v i) → (∀ i, v (f i) = v i) → ∀ i j, v i = v j) :
    Fintype.card (PermutationOrbit e) + Fintype.card (PermutationOrbit f) +
      Fintype.card (PermutationOrbit (e.trans f)) ≤ Fintype.card α + 2 := by
  have h := permutation_cycle_dimension_bound e f
  have hk := permutation_common_fixed_finrank_le_one e f a hconnected
  omega

end SquareAntiprismVerification
