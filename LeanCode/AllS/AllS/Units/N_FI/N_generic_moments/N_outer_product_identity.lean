import AllS.Units.N_FI.N_generic_moments.N_frame_features
import AllS.Units.N_FI.N_generic_moments.N_moment_entry
import AllS.Units.N_FI.N_generic_moments.N_unit_frame
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Generic all-parameter proof. S/R identities adapt upstream RCounting
(commit50d14bc06bd41f61573eb6a36eedb8d00759af8f); outer products expand
the explicit proved tangent features. No fixed-exponent certificate. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
namespace Blueprint.Thomson.GenericMoments
noncomputable def realFeature (m k : ℕ) (y : Configuration)
    (b : Index → OrthonormalBasis (Fin 3) ℝ Point) (i : Index) (a : Fin m) : ℝ :=
  ∑ j : Index, (inner ℝ (y i) (y j)) ^ a.val * ((tangentComplex (b i) (y j)) ^ k).re

noncomputable def imagFeature (m k : ℕ) (y : Configuration)
    (b : Index → OrthonormalBasis (Fin 3) ℝ Point) (i : Index) (a : Fin m) : ℝ :=
  ∑ j : Index, (inner ℝ (y i) (y j)) ^ a.val * ((tangentComplex (b i) (y j)) ^ k).im

theorem momentMatrix_outer_products (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) (b : Index → OrthonormalBasis (Fin 3) ℝ Point)
    (hb : ∀ i, b i 0 = y i) :
    momentMatrix m k y = ∑ i : Index, (fun a c =>
      realFeature m k y b i a * realFeature m k y b i c +
      imagFeature m k y b i a * imagFeature m k y b i c) := by
  ext a c
  rw [momentMatrix_entry]
  simp only [tripleSum, onTriples, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hf (j l : Index) :
      kernelQ k (inner ℝ (y i) (y j)) (inner ℝ (y i) (y l)) (inner ℝ (y j) (y l)) =
      ((tangentComplex (b i) (y j))^k).re * ((tangentComplex (b i) (y l))^k).re +
      ((tangentComplex (b i) (y j))^k).im * ((tangentComplex (b i) (y l))^k).im := by
    simpa only [hb i] using spherical_kernel_features (b i) (y j) (y l) (hy j) (hy l) k
  simp_rw [hf]
  simp only [realFeature, imagFeature, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    apply Finset.sum_congr rfl <;> intro l _ <;> ring

theorem momentMatrix_exists_outer_products (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) :
    ∃ v w : Index → Fin m → ℝ,
      momentMatrix m k y = ∑ i : Index, (fun a c => v i a * v i c + w i a * w i c) := by
  classical
  let b : Index → OrthonormalBasis (Fin 3) ℝ Point :=
    fun i => Classical.choose (unit_frame (y i) (hy i))
  have hb (i : Index) : b i 0 = y i := Classical.choose_spec (unit_frame (y i) (hy i))
  exact ⟨realFeature m k y b, imagFeature m k y b,
    momentMatrix_outer_products m k y hy b hb⟩

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments

theorem generic_moments_outer_product_identity (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) :
    ∃ v w : Fin 8 → Fin m → ℝ,
      momentMatrix m k y = ∑ i : Fin 8, (fun a c => v i a * v i c + w i a * w i c) :=
  momentMatrix_exists_outer_products m k y hy
end Blueprint.Thomson.Finite

#check Blueprint.Thomson.Finite.generic_moments_outer_product_identity
#print axioms Blueprint.Thomson.Finite.generic_moments_outer_product_identity
