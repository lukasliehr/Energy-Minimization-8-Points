import AllS.Units.N_GI.N_boundary_annulus.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem boundary_annulus (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250) :
    181/2000<gnomonicSquareSum Y ∧ gnomonicSquareSum Y<boundaryRho^2 ∧
    ∃y : Fin 13 → ℝ,(∀i,gnomonicTangent Y i=boundaryDisplacement y i) ∧
      3620/3721≤(∑j,boundaryDiagonal j*(y j)^2) ∧ (∑j,boundaryDiagonal j*(y j)^2)≤1 :=
  boundary_annulus_assemble Y hY hal hg

#print axioms boundary_annulus
end Blueprint.Thomson.Tail
