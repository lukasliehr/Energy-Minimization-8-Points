import Mathlib

noncomputable section
namespace SquareAntiprismVerification

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The elementary fixed-space argument behind the Euler upper bound for
two permutations. No surface classification is used. -/
lemma three_fixed_sum_zero (A B : V ≃ₗᵢ[ℝ] V) (x y z : V)
    (hx : A x = x) (hy : B y = y) (hz : A (B z) = z)
    (hsum : x + y + z = 0) : A y = y ∧ B x = x := by
  have hzx : inner ℝ (B z) x = inner ℝ z x := by
    calc
      _ = inner ℝ (A (B z)) (A x) := (A.inner_map_map _ _).symm
      _ = _ := by rw [hz, hx]
  have hzy : inner ℝ (B z) y = inner ℝ z y := by
    calc
      _ = inner ℝ (B z) (B y) := by rw [hy]
      _ = _ := B.inner_map_map _ _
  have hinner : inner ℝ (B z) z = inner ℝ z z := by
    have h : inner ℝ (B z) (x + y) = inner ℝ z (x + y) := by
      rw [inner_add_right, inner_add_right, hzx, hzy]
    rw [eq_neg_of_add_eq_zero_left hsum, inner_neg_right, inner_neg_right] at h
    exact neg_injective h
  have hBz : B z = z := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    simp only [inner_sub_left, inner_sub_right]
    rw [B.inner_map_map, hinner, real_inner_comm (B z) z, hinner]
    ring
  have hAz : A z = z := by simpa only [hBz] using hz
  constructor
  · have h := congrArg A hsum
    simp only [map_add, map_zero, hx, hAz] at h
    apply add_left_cancel (a := x)
    apply add_right_cancel (b := z)
    exact h.trans hsum.symm
  · have h := congrArg B hsum
    simp only [map_add, map_zero, hy, hBz] at h
    apply add_right_cancel (b := y + z)
    simpa only [add_assoc] using h.trans hsum.symm

def isometryFixed (A : V ≃ₗᵢ[ℝ] V) : Submodule ℝ V where
  carrier := {x | A x = x}
  zero_mem' := map_zero A
  add_mem' {x y} hx hy := by
    change A x = x at hx
    change A y = y at hy
    change A (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' t x hx := by
    change A x = x at hx
    change A (t • x) = t • x
    rw [map_smul, hx]

def fixedSpaceSum (A B : V ≃ₗᵢ[ℝ] V) :
    (isometryFixed A × isometryFixed B × isometryFixed (B.trans A)) →ₗ[ℝ] V where
  toFun p := p.1.val + p.2.1.val + p.2.2.val
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
  map_smul' t p := by simp [smul_add]

lemma fixedSpaceSum_kernel_common (A B : V ≃ₗᵢ[ℝ] V) (p : (fixedSpaceSum A B).ker) :
    p.val.1.val ∈ isometryFixed A ⊓ isometryFixed B ∧
      p.val.2.1.val ∈ isometryFixed A ⊓ isometryFixed B := by
  have hsum : p.val.1.val + p.val.2.1.val + p.val.2.2.val = 0 := p.property
  have h := three_fixed_sum_zero A B p.val.1.val p.val.2.1.val p.val.2.2.val
    p.val.1.property p.val.2.1.property p.val.2.2.property hsum
  exact ⟨⟨p.val.1.property, h.2⟩, ⟨h.1, p.val.2.1.property⟩⟩

def fixedSpaceKernelMap (A B : V ≃ₗᵢ[ℝ] V) :
    (fixedSpaceSum A B).ker →ₗ[ℝ]
      ↥(isometryFixed A ⊓ isometryFixed B) × ↥(isometryFixed A ⊓ isometryFixed B) where
  toFun p := ⟨⟨p.val.1.val, (fixedSpaceSum_kernel_common A B p).1⟩,
    ⟨p.val.2.1.val, (fixedSpaceSum_kernel_common A B p).2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fixedSpaceKernelMap_injective (A B : V ≃ₗᵢ[ℝ] V) :
    Function.Injective (fixedSpaceKernelMap A B) := by
  intro p q heq
  have hx : p.val.1.val = q.val.1.val := congrArg (fun r => r.1.val) heq
  have hy : p.val.2.1.val = q.val.2.1.val := congrArg (fun r => r.2.val) heq
  have hp : p.val.1.val + p.val.2.1.val + p.val.2.2.val = 0 := p.property
  have hq : q.val.1.val + q.val.2.1.val + q.val.2.2.val = 0 := q.property
  have hz : p.val.2.2.val = q.val.2.2.val := by
    rw [hx, hy] at hp
    exact add_left_cancel (hp.trans hq.symm)
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hx) (Prod.ext (Subtype.ext hy) (Subtype.ext hz))

/-- Scott's dimension inequality for two orthogonal transformations. For
permutations the fixed-space dimensions count their cycles, yielding the
Euler upper bound after joint connectedness is supplied. -/
theorem isometry_fixed_dimension_inequality [FiniteDimensional ℝ V] (A B : V ≃ₗᵢ[ℝ] V) :
    Module.finrank ℝ (isometryFixed A) + Module.finrank ℝ (isometryFixed B) +
      Module.finrank ℝ (isometryFixed (B.trans A)) ≤
        Module.finrank ℝ V + 2 * Module.finrank ℝ ↥(isometryFixed A ⊓ isometryFixed B) := by
  have hk := LinearMap.finrank_le_finrank_of_injective (fixedSpaceKernelMap_injective A B)
  rw [Module.finrank_prod] at hk
  have hr := (fixedSpaceSum A B).range.finrank_le
  have hdim := (fixedSpaceSum A B).finrank_range_add_finrank_ker
  simp only [Module.finrank_prod] at hdim
  omega

end SquareAntiprismVerification
