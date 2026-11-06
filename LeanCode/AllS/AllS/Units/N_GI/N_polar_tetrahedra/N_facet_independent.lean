import AllS.Units.N_G.N_spanning_cube
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option maxHeartbeats 600000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

/-- Three distinct unit vectors on a nonzero affine hyperplane are a linear basis. -/
theorem unit_plane_triple_independent (A : Fin 3 → Point) (n : Point) (c : ℝ)
    (hunit : ∀i,‖A i‖=1) (hinj : Function.Injective A) (hc : c≠0)
    (hplane : ∀i,inner ℝ n (A i)=c) : LinearIndependent ℝ A := by
  have hcos : EuclideanGeometry.Cospherical (Set.range A) := by
    refine ⟨0,1,?_⟩
    rintro p ⟨i,rfl⟩
    simpa only [dist_zero_right] using hunit i
  have haff := hcos.affineIndependent (Set.Subset.refl _) hinj
  apply Fintype.linearIndependent_iff.mpr
  intro w hw i
  have hsum : (∑j,w j)=0 := by
    have hh := congrArg (fun x : Point => inner ℝ n x) hw
    simp only [inner_sum,inner_smul_right,hplane,inner_zero_right,←Finset.sum_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_right hc
  exact haff.eq_zero_of_sum_eq_zero hsum hw i (Finset.mem_univ _)

theorem polar_tetrahedra_facet_independent (A B : Fin 4 → Point) (c : ℝ)
    (hunit : ∀i,‖A i‖=1) (hinj : Function.Injective A) (hc : 0<c)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (f : Fin 3 → Fin 4) (hf : Function.Injective f) : LinearIndependent ℝ (A ∘ f) := by
  have hnot : ¬Function.Surjective f := by
    intro hh
    have hcard := Fintype.card_le_of_surjective f hh
    norm_num at hcard
  unfold Function.Surjective at hnot
  push Not at hnot
  obtain ⟨j,hj⟩ := hnot
  apply unit_plane_triple_independent (A ∘ f) (B j) c (fun i => hunit _) (hinj.comp hf) hc.ne'
  intro i
  exact (real_inner_comm _ _).trans (hcross _ _ (hj i))

#print axioms unit_plane_triple_independent
#print axioms polar_tetrahedra_facet_independent
end Blueprint.Thomson.Tail.Implementation
