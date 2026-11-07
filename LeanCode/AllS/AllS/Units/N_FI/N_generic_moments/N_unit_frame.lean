import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/SphereFrame.lean:8-19. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.GenericMoments

theorem unit_frame (x : Point) (hx : ‖x‖ = 1) : ∃ b : OrthonormalBasis (Fin 3) ℝ Point, b 0 = x := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => x)) := by
    constructor
    · intro i; exact hx
    · intro i j hij
      exfalso
      apply hij
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.property).trans
        (Set.mem_singleton_iff.mp j.property).symm
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [Point])
  exact ⟨b, hb 0 (by simp)⟩

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
theorem generic_moments_unit_frame (x : Point) (hx : ‖x‖ = 1) : ∃ b : OrthonormalBasis (Fin 3) ℝ Point, b 0 = x :=
  GenericMoments.unit_frame x hx
#check generic_moments_unit_frame
#print axioms generic_moments_unit_frame
end Blueprint.Thomson.Finite

