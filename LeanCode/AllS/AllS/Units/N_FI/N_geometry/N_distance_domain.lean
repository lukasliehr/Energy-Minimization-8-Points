import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions

noncomputable section
namespace Blueprint.Thomson.Finite

def DistanceDomainContract : Prop := ∀ x y : Point, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y →
  (-1 ≤ inner ℝ x y ∧ inner ℝ x y < 1) ∧
  0 < ‖x-y‖ ∧ ‖x-y‖^2 = 2-2*inner ℝ x y
theorem geometry_distance_domain : DistanceDomainContract := by
  intro x y hx hy hne
  have hb := abs_real_inner_le_norm x y
  rw [hx, hy, one_mul] at hb
  have hsq := norm_sub_sq_real x y
  rw [hx, hy] at hsq
  have hp : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  refine ⟨⟨(abs_le.mp hb).1, ?_⟩, hp, ?_⟩
  · nlinarith [sq_pos_of_pos hp]
  · nlinarith

#check geometry_distance_domain
#print axioms geometry_distance_domain
#check DistanceDomainContract
#print axioms DistanceDomainContract
end Blueprint.Thomson.Finite
