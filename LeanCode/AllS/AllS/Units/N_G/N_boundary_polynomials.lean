import AllS.Units.N_GI.N_boundary_polynomials.N_assemble

noncomputable section
open SquareAntiprismVerification (packingMaxInner)
namespace Blueprint.Thomson.Tail
open Implementation

theorem boundary_polynomials (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hg : productGauge Y=239/250) (hm : packingMaxInner Y≤packingHeight+33/2000) :
    ∃y : Fin 13 → ℝ,
      3620/3721≤(∑j,boundaryDiagonal j*(y j)^2) ∧ (∑j,boundaryDiagonal j*(y j)^2)≤1 ∧
      ∀e : ContactIndex,0≤boundaryContactPolynomial e y :=
  boundary_polynomials_assemble Y hY hg hm

#print axioms boundary_polynomials
end Blueprint.Thomson.Tail
