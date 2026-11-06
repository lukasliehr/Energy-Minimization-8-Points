import AllS.Units.N_GI.N_polar_tetrahedra.N_polar_facets

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem polar_tetrahedra_assemble (A B : Fin 4 → Point) (c : ℝ)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B) (hc : 0<c)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    (∀i,inner ℝ (A i) (B i)<c) ∧ AffineIndependent ℝ A ∧
    (0 : Point)∈interior (convexHull ℝ (Set.range A)) ∧
    convexHull ℝ (Set.range A)={x | ∀i,inner ℝ x (B i)≤c} ∧
    (∀i,c • B i∈intrinsicInterior ℝ (cubeFacet A i)) ∧
    ∃w : Fin 4 → ℝ,(∀i,0<w i) ∧ (∑i,w i=1) ∧ (∑i,w i • A i=0) ∧
      ∀i,w i=c/(c-inner ℝ (A i) (B i)) := by
  have hs := polar_tetrahedra_matched_strict A B c hAunit hAinj hBinj hc hcross hmatched
  obtain ⟨ha,hh,hf⟩ := polar_tetrahedra_polar_facets A B c hAunit hBunit hAinj hBinj hc hcross hmatched
  exact ⟨hs,ha,cube_origin_interior A B c hc hcross hs,hh,hf,
    polar_tetrahedra_positive_relation A B c hAunit hAinj hBinj hc hcross hmatched⟩

#print axioms polar_tetrahedra_assemble
end Blueprint.Thomson.Tail.Implementation
