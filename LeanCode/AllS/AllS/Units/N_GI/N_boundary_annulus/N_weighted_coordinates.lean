import AllS.Units.N_GI.N_boundary_annulus.N_upper

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_annulus_weighted_coordinates (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hal : IsProductAligned Y) (hg : productGauge Y=239/250) :
    ∃y : Fin 13 → ℝ,(∀i,gnomonicTangent Y i=boundaryDisplacement y i) ∧
      3620/3721≤(∑j,boundaryDiagonal j*(y j)^2) ∧ (∑j,boundaryDiagonal j*(y j)^2)≤1 := by
  have hp : 0<productGauge Y := by rw [hg]; norm_num
  have hρ : 0<boundaryRho := by norm_num [boundaryRho]
  have hq := gnomonicCoordinates_mem_slice Y hal hp
  obtain ⟨y,hy⟩ := boundarySynthesis_surjective (boundaryRho⁻¹ • gnomonicCoordinates Y)
    (rotationSlice.smul_mem _ hq)
  have he : boundaryRho • boundarySynthesis y=gnomonicCoordinates Y := by
    rw [hy,smul_smul,mul_inv_cancel₀ hρ.ne',one_smul]
  have hn : gnomonicSquareSum Y=boundaryRho^2*(∑j,boundaryDiagonal j*(y j)^2) := by
    rw [←gnomonicCoordinates_norm_sq Y hal hp,←he,norm_smul,Real.norm_eq_abs,abs_of_pos hρ,
      mul_pow,boundarySynthesis_norm_sq]
  refine ⟨y,?_,?_,?_⟩
  · intro i
    rw [←gnomonicCoordinates_tangent Y hal hp i,←he,tangentVector_smul]
    rfl
  · have hlo := boundary_annulus_lower Y hY hal hg
    rw [hn] at hlo
    norm_num [boundaryRho] at hlo
    linarith
  · have hup := boundary_annulus_upper Y hY hal hg
    rw [hn] at hup
    norm_num [boundaryRho] at hup
    linarith

#print axioms boundary_annulus_weighted_coordinates
end Blueprint.Thomson.Tail.Implementation
