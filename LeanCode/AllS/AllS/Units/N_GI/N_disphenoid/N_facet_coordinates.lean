import AllS.Units.N_G.N_polar_tetrahedra
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Simplex

set_option maxHeartbeats 900000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_projection_positive_coordinates (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hBunit : ∀i,‖B i‖=1) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (i : Fin 4) :
    ∃w : Fin 3 → ℝ,(∀j,0<w j) ∧ (∑j,w j=1) ∧
      (∑j,w j • A (i.succAbove j)=c • B i) := by
  obtain ⟨w,hw,hx⟩ := cube_affine_coordinates A (cube_affine_independent A B c hcross hstrict) (c • B i)
  have hself : inner ℝ (c • B i) (B i)=c := by
    rw [inner_smul_left,conj_trivial,real_inner_self_eq_norm_sq,hBunit i];norm_num
  have hi : w i=0 := (cube_coordinate_plane A B c hcross hstrict w hw i).mp (hx ▸ hself)
  have hp : ∀j,j≠i → 0<w j := by
    intro j hji
    have hh := (inner_lt_one_iff_real_of_norm_eq_one (hBunit i) (hBunit j)).mpr
      (fun h => hji (hBinj h).symm)
    have hh' : inner ℝ (c • B i) (B j)<c := by
      rw [inner_smul_left,conj_trivial]
      exact (mul_lt_mul_of_pos_left hh hc).trans_eq (mul_one c)
    rw [hx,cube_cross_inner_sum A B c hcross w j,hw,mul_one] at hh'
    have hs := hstrict j
    nlinarith
  refine ⟨fun j => w (i.succAbove j),fun j => hp _ (Fin.succAbove_ne i j),?_,?_⟩
  · rw [Fin.sum_univ_succAbove w i,hi,zero_add] at hw;exact hw
  · rw [Fin.sum_univ_succAbove (fun j => w j • A j) i,hi,zero_smul,zero_add] at hx
    exact hx.symm

theorem cube_facet_radius_sq (A B : Fin 4 → Point) (c : ℝ)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c) (i : Fin 4) (j : Fin 3) :
    ‖A (i.succAbove j)-c • B i‖^2=1-c^2 := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,conj_trivial,
    real_inner_self_eq_norm_sq,hAunit,hBunit,hcross _ i (Fin.succAbove_ne i j)]
  rw [real_inner_comm (A (i.succAbove j)),hcross _ i (Fin.succAbove_ne i j)]
  ring

theorem cube_facet_circumcenter (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (i : Fin 4) :
    ∃t : Affine.Triangle ℝ Point,t.points=A ∘ i.succAbove ∧
      t.circumcenter=c • B i ∧ t.circumradius=Real.sqrt (1-c^2) := by
  let t : Affine.Triangle ℝ Point := ⟨A ∘ i.succAbove,
    (polar_tetrahedra_facet_independent A B c hAunit hAinj hc hcross i.succAbove
      Fin.succAbove_right_injective).affineIndependent⟩
  have hmem : c • B i∈affineSpan ℝ (Set.range t.points) :=
    convexHull_subset_affineSpan _ (intrinsicInterior_subset
      (cube_projection_facet_interior A B c hc hBunit hBinj hcross hstrict i))
  have hr : ∀j,dist (t.points j) (c • B i)=Real.sqrt (1-c^2) := by
    intro j
    rw [dist_eq_norm]
    rw [←cube_facet_radius_sq A B c hAunit hBunit hcross i j,Real.sqrt_sq (norm_nonneg _)]
    rfl
  exact ⟨t,rfl,(t.eq_circumcenter_of_dist_eq hmem hr).symm,(t.eq_circumradius_of_dist_eq hmem hr).symm⟩

#print axioms cube_projection_positive_coordinates
#print axioms cube_facet_radius_sq
#print axioms cube_facet_circumcenter
end Blueprint.Thomson.Tail.Implementation
