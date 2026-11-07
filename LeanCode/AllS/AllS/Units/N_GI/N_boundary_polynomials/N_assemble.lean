import AllS.Units.N_GI.N_boundary_polynomials.N_physical_inequalities
import AllS.Units.N_G.N_boundary_annulus

noncomputable section
open Real
open SquareAntiprismVerification (packingMaxInner packingMaxInner_le_iff)
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_polynomials_assemble (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hg : productGauge Y=239/250) (hm : packingMaxInner Y≤packingHeight+33/2000) :
    ∃y : Fin 13 → ℝ,
      3620/3721≤(∑j,boundaryDiagonal j*(y j)^2) ∧ (∑j,boundaryDiagonal j*(y j)^2)≤1 ∧
      ∀e : ContactIndex,0≤boundaryContactPolynomial e y := by
  obtain ⟨U,σ,hZ,hal,hgZ,_⟩ := product_alignment_exists Y hY
  let Z : Fin 8 → Point := fun i=>U (Y (σ i))
  have hmZ : packingMaxInner Z≤packingHeight+33/2000 := by
    apply (packingMaxInner_le_iff Z _).mpr
    intro i j hij
    have h := (packingMaxInner_le_iff Y _).mp hm (σ i) (σ j) (σ.injective.ne hij)
    simpa [Z,U.inner_map_map] using h
  have hgZ : productGauge Z=239/250 := hgZ.trans hg
  obtain ⟨y,hy,hlo,hup⟩ := boundary_annulus_weighted_coordinates Z hZ hal hgZ
  exact ⟨y,hlo,hup,boundary_polynomials_physical_inequalities Z hZ hal hgZ hmZ y hy⟩

#print axioms boundary_polynomials_assemble
end Blueprint.Thomson.Tail.Implementation
