import ThomsonNegative.Structure.Coordinates

/-! The fixed coefficient-map interface consumed by the finite cell assembly. -/

noncomputable section

namespace ThomsonNegative.Structure

structure HybridCoefficientSystem where
  family : PolynomialFamily
  coefficientMap : GramFamily →ₗ[ℝ] FullSpace
  coefficient_spec : ∀ W, physicalSynthesize (coefficientMap W) = gramPolynomial family W
  compatibility : CompatibilityData FullSpace
  compatibility_one : compatibility.one = Pi.single (0 : Fin 102) (1 : ℝ)
  compatibility_square : compatibility.square = Pi.single (3 : Fin 102) (1 : ℝ)
  high_image : ∀ W, HighCompatible (coefficientMap W)
  ell0_image : ∀ W, compatibility.ell0 (coefficientMap W) = 0
  ell1_image : ∀ W, compatibility.ell1 (coefficientMap W) = 0

structure HybridRightInverse (S : HybridCoefficientSystem) where
  correction : ChartSpace →ₗ[ℝ] GramFamily
  right_inverse : retainLinear.comp (S.coefficientMap.comp correction) = LinearMap.id

def HybridRightInverse.corrected (S : HybridCoefficientSystem) (D : HybridRightInverse S)
    (target : FullSpace) (initial : GramFamily) : GramFamily :=
  initial + D.correction (retain (target-S.coefficientMap initial))

theorem HybridRightInverse.retained_identity (S : HybridCoefficientSystem)
    (D : HybridRightInverse S) (target : FullSpace) (initial : GramFamily) :
    retain (S.coefficientMap (D.corrected S target initial)) = retain target := by
  have h := LinearMap.congr_fun D.right_inverse (retain (target-S.coefficientMap initial))
  change retain (S.coefficientMap (D.correction (retain (target-S.coefficientMap initial)))) =
    retain (target-S.coefficientMap initial) at h
  change retainLinear (S.coefficientMap (initial + D.correction _)) = _
  rw [map_add, map_add]
  change retain (S.coefficientMap initial) +
    retain (S.coefficientMap (D.correction _)) = _
  rw [h]
  change retainLinear (S.coefficientMap initial) + retainLinear (target-S.coefficientMap initial) = _
  rw [map_sub]
  abel

theorem HybridRightInverse.coefficient_identity (S : HybridCoefficientSystem)
    (D : HybridRightInverse S) (target : FullSpace) (initial : GramFamily)
    (hhigh : HighCompatible target) (h0 : S.compatibility.ell0 target=0)
    (h1 : S.compatibility.ell1 target=0) :
    S.coefficientMap (D.corrected S target initial) = target :=
  coefficient_recovery S.compatibility S.compatibility_one S.compatibility_square
    (S.high_image _) hhigh (S.ell0_image _) (S.ell1_image _) h0 h1
    (D.retained_identity S target initial)

/-- Four correction bounds may be applied to this exact polynomial identity. -/
theorem HybridRightInverse.corrected_gram_identity (S : HybridCoefficientSystem)
    (D : HybridRightInverse S) (target : FullSpace) (initial : GramFamily)
    (hhigh : HighCompatible target) (h0 : S.compatibility.ell0 target=0)
    (h1 : S.compatibility.ell1 target=0) :
    gramPolynomial S.family (D.corrected S target initial) = physicalSynthesize target := by
  rw [← S.coefficient_spec, D.coefficient_identity S target initial hhigh h0 h1]

end ThomsonNegative.Structure
