import Lean_Code.HemisphereCoordinates
import Lean_Code.SphericalTriangle

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma cyclic_one_ne (n : ℕ) (i : Fin (n + 3)) : i + 1 ≠ i := by
  intro h
  have h1 : (1 : Fin (n + 3)) = 0 := add_left_cancel (h.trans (add_zero i).symm)
  have hv := congrArg Fin.val h1
  norm_num at hv

lemma cyclic_two_ne (n : ℕ) (i : Fin (n + 3)) : i + 1 + 1 ≠ i := by
  intro h
  have hlast : (1 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
    intro hlast
    have hval := congrArg Fin.val hlast
    norm_num at hval
  have hone : (1 : Fin (n + 3)) + 1 = 2 := by
    apply Fin.ext
    rw [Fin.val_add_one, if_neg hlast]
    norm_num [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  have h2 : (2 : Fin (n + 3)) = 0 := by
    apply add_left_cancel (a := i)
    calc
      i + 2 = i + 1 + 1 := by rw [add_assoc, hone]
      _ = i := h
      _ = i + 0 := (add_zero i).symm
  have hv := congrArg Fin.val h2
  norm_num [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at hv

/-- A unit spherical polygon with every nonincident vertex strictly to
the left of each directed edge. This is a geometric condition, not an
assumption that arbitrary contact boundary cycles already satisfy it. -/
structure StrictSphericalPolygon (n : ℕ) where
  vertex : Fin (n + 3) → ℝ³
  unit : ∀ i, ‖vertex i‖ = 1
  support : ∀ i j, j ≠ i → j ≠ i + 1 →
    0 < inner ℝ (crossVec (vertex i) (vertex (i + 1))) (vertex j)

namespace StrictSphericalPolygon

variable {n : ℕ}

lemma turn_pos (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) :
    0 < inner ℝ (crossVec (Q.vertex i) (Q.vertex (i + 1))) (Q.vertex (i + 1 + 1)) :=
  Q.support i (i + 1 + 1) (cyclic_two_ne n i) (cyclic_one_ne n (i + 1))

lemma edge_cross_ne_zero (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) :
    crossVec (Q.vertex i) (Q.vertex (i + 1)) ≠ 0 := by
  intro h
  have hp := Q.turn_pos i
  rw [h, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

def normal (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) : ℝ³ :=
  sphereEdgeNormal (Q.vertex i) (Q.vertex (i + 1))

lemma normal_unit (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) : ‖Q.normal i‖ = 1 :=
  sphereEdgeNormal_unit _ _ (Q.edge_cross_ne_zero i)

lemma normal_vertex_pos (Q : StrictSphericalPolygon n) (i j : Fin (n + 3))
    (hji : j ≠ i) (hjnext : j ≠ i + 1) : 0 < inner ℝ (Q.normal i) (Q.vertex j) := by
  simp only [normal, sphereEdgeNormal, inner_smul_left, starRingEnd_apply, star_trivial]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr (Q.edge_cross_ne_zero i))) (Q.support i j hji hjnext)

lemma normal_vertex_nonneg (Q : StrictSphericalPolygon n) (i j : Fin (n + 3)) :
    0 ≤ inner ℝ (Q.normal i) (Q.vertex j) := by
  by_cases hji : j = i
  · subst j
    simp [normal, sphereEdgeNormal, inner_smul_left, crossVec_inner_left]
  by_cases hjnext : j = i + 1
  · subst j
    simp [normal, sphereEdgeNormal, inner_smul_left, crossVec_inner_right]
  exact (Q.normal_vertex_pos i j hji hjnext).le

def pole (Q : StrictSphericalPolygon n) : ℝ³ := ∑ i, Q.normal i

lemma pole_vertex_pos (Q : StrictSphericalPolygon n) (j : Fin (n + 3)) :
    0 < inner ℝ Q.pole (Q.vertex j) := by
  classical
  rw [pole, sum_inner]
  apply Finset.sum_pos' (fun i _ => Q.normal_vertex_nonneg i j)
  exact ⟨j + 1, Finset.mem_univ _, Q.normal_vertex_pos (j + 1) j
    (cyclic_one_ne n j).symm (cyclic_two_ne n j).symm⟩

theorem open_hemisphere (Q : StrictSphericalPolygon n) :
    ∃ p : ℝ³, ‖p‖ = 1 ∧ ∀ j, 0 < inner ℝ p (Q.vertex j) := by
  have hp : Q.pole ≠ 0 := by
    intro h
    have hpos := Q.pole_vertex_pos 0
    rw [h, inner_zero_left] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨‖Q.pole‖⁻¹ • Q.pole, ?_, ?_⟩
  · simp [norm_smul, hp]
  · intro j
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hp)) (Q.pole_vertex_pos j)

def turnWeight (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) : ℝ :=
  ‖crossVec (Q.vertex i) (Q.vertex (i + 1))‖⁻¹ *
    (‖crossVec (Q.vertex (i + 1)) (Q.vertex (i + 1 + 1))‖⁻¹ *
      inner ℝ (crossVec (Q.vertex i) (Q.vertex (i + 1))) (Q.vertex (i + 1 + 1)))

lemma turnWeight_pos (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) : 0 < Q.turnWeight i :=
  mul_pos (inv_pos.mpr (norm_pos_iff.mpr (Q.edge_cross_ne_zero i)))
    (mul_pos (inv_pos.mpr (norm_pos_iff.mpr (Q.edge_cross_ne_zero (i + 1)))) (Q.turn_pos i))

lemma cross_normals (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) :
    crossVec (Q.normal i) (Q.normal (i + 1)) = Q.turnWeight i • Q.vertex (i + 1) := by
  simp only [normal, sphereEdgeNormal, crossVec_smul_left, crossVec_smul_right,
    cross_cross_cyclic, smul_smul, turnWeight]
  congr 1
  ring

/-- The polar is constructed from the directed unit edge normals. -/
def polar (Q : StrictSphericalPolygon n) : StrictSphericalPolygon n where
  vertex := Q.normal
  unit := Q.normal_unit
  support i j hji hjnext := by
    rw [Q.cross_normals]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    apply mul_pos (Q.turnWeight_pos i)
    rw [real_inner_comm (Q.normal j) (Q.vertex (i + 1))]
    exact Q.normal_vertex_pos j (i + 1) hjnext.symm
      (fun heq => hji (add_right_cancel heq).symm)

lemma polar_normal (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) :
    Q.polar.normal i = Q.vertex (i + 1) := by
  change ‖crossVec (Q.normal i) (Q.normal (i + 1))‖⁻¹ •
    crossVec (Q.normal i) (Q.normal (i + 1)) = _
  rw [Q.cross_normals]
  simp [norm_smul, abs_of_pos (Q.turnWeight_pos i), Q.unit,
    smul_smul, (Q.turnWeight_pos i).ne']

def angle (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) : ℝ :=
  sphereVertexAngle (Q.vertex i) (Q.vertex (i + 1)) (Q.vertex (i - 1))

def perimeter (Q : StrictSphericalPolygon n) : ℝ :=
  ∑ i, sphereAngle (Q.vertex i) (Q.vertex (i + 1))

theorem polar_angle (Q : StrictSphericalPolygon n) (i : Fin (n + 3)) :
    Q.polar.angle i = Real.pi - sphereAngle (Q.vertex i) (Q.vertex (i + 1)) := by
  have hprev : sphereEdgeNormal (Q.normal (i - 1)) (Q.normal i) = Q.vertex i := by
    simpa only [normal, polar, sub_add_cancel] using Q.polar_normal (i - 1)
  have hnext : sphereEdgeNormal (Q.normal i) (Q.normal (i + 1)) = Q.vertex (i + 1) :=
    Q.polar_normal i
  have h := vertex_angle_polar_identity (Q.normal i) (Q.normal (i + 1)) (Q.normal (i - 1))
    (Q.normal_unit i)
  rw [hprev, hnext] at h
  change sphereVertexAngle (Q.normal i) (Q.normal (i + 1)) (Q.normal (i - 1)) = _
  linarith

/-- The polar-excess calculation that yields the perimeter bound. The
positive-excess hypothesis still has to be supplied by triangulation. -/
theorem perimeter_lt_of_polar_excess (Q : StrictSphericalPolygon n)
    (hexcess : ((n : ℝ) + 1) * Real.pi < ∑ i, Q.polar.angle i) :
    Q.perimeter < 2 * Real.pi := by
  simp only [Q.polar_angle, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hexcess
  push_cast at hexcess
  change _ < _ - Q.perimeter at hexcess
  nlinarith

end StrictSphericalPolygon

end SquareAntiprismVerification
