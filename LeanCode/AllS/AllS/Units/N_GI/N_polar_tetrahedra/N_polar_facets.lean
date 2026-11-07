import AllS.Units.N_GI.N_polar_tetrahedra.N_relative_interior

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem polar_tetrahedra_polar_facets (A B : Fin 4 → Point) (c : ℝ)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B) (hc : 0<c)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    AffineIndependent ℝ A ∧
    convexHull ℝ (Set.range A)={x | ∀i,inner ℝ x (B i)≤c} ∧
    ∀i,c • B i∈intrinsicInterior ℝ (cubeFacet A i) := by
  have hs := polar_tetrahedra_matched_strict A B c hAunit hAinj hBinj hc hcross hmatched
  exact ⟨cube_affine_independent A B c hcross hs,
    cube_convex_hull_halfspaces A B c hcross hs,
    cube_projection_facet_interior A B c hc hBunit hBinj hcross hs⟩

#print axioms polar_tetrahedra_polar_facets
end Blueprint.Thomson.Tail.Implementation
