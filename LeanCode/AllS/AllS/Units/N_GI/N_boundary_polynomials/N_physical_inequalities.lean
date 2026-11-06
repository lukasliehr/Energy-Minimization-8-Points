import AllS.Units.N_GI.N_boundary_polynomials.N_polynomial_model
import AllS.Units.N_GI.N_boundary_polynomials.N_gnomonic_quadratic
import Lean_Code.PackingMaximum

noncomputable section
open Real
open SquareAntiprismVerification (packingMaxInner inner_le_packingMaxInner)
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_polynomials_physical_inequalities (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250)
    (hm : packingMaxInner Y≤packingHeight+33/2000)
    (y : Fin 13 → ℝ) (hy : ∀i,gnomonicTangent Y i=boundaryDisplacement y i) :
    ∀e : ContactIndex,0≤boundaryContactPolynomial e y := by
  have hp : 0<productGauge Y := by rw [hg]; norm_num
  intro e
  have hc : 0≤packingHeight+gap/2 := by
    dsimp [gap]
    linarith [packingHeight_mem_Ioo.1]
  have hPi : inner ℝ (packingReference e.1) (packingReference (contactNext e))=packingHeight :=
    (constants_pair_table.2.2.2.1 e).1
  have hgi := (gnomonic_inverse Y hY e.1 (product_slice_positive_factors Y hal hp e.1).1).2
  have hgj := (gnomonic_inverse Y hY (contactNext e) (product_slice_positive_factors Y hal hp (contactNext e)).1).2
  rw [hy] at hgi hgj
  have hb : inner ℝ (Y e.1) (Y (contactNext e))≤packingHeight+gap/2 := by
    have h := (inner_le_packingMaxInner Y e.1 (contactNext e) (contactNext_ne e)).trans hm
    dsimp [gap]
    linarith [h]
  rw [boundaryContactPolynomial_physical]
  exact boundary_gnomonic_quadratic _ _ _ _ _ _ _ _ hPi hc hgi hgj hb

#print axioms boundary_polynomials_physical_inequalities
end Blueprint.Thomson.Tail.Implementation
