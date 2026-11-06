import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
namespace ThomsonNegative.Certificate.Bridges

theorem finite_rightInverse_unique {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A R D : V →ₗ[K] V)
    (hR : A.comp R=LinearMap.id) (hD : A.comp D=LinearMap.id) : R=D := by
  have hsurj : Function.Surjective A := by
    intro x
    exact ⟨R x,LinearMap.congr_fun hR x⟩
  have hinj : Function.Injective A := LinearMap.injective_iff_surjective.mpr hsurj
  ext x
  apply hinj
  exact (LinearMap.congr_fun hR x).trans (LinearMap.congr_fun hD x).symm

theorem finite_rightInverse_leftInverse {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A R : V →ₗ[K] V)
    (hR : A.comp R=LinearMap.id) : R.comp A=LinearMap.id := by
  have hsurj : Function.Surjective A := by
    intro x
    exact ⟨R x,LinearMap.congr_fun hR x⟩
  have hinj : Function.Injective A := LinearMap.injective_iff_surjective.mpr hsurj
  ext x
  apply hinj
  exact LinearMap.congr_fun hR (A x)

#print axioms finite_rightInverse_unique
end ThomsonNegative.Certificate.Bridges
