import Lean_Code.SphericalPolygon
import Lean_Code.TangentWedge

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace StrictSphericalPolygon

variable {n : ℕ}

def fanAngle (Q : StrictSphericalPolygon n) (j : Fin (n + 2)) : ℝ :=
  sphereVertexAngle (Q.vertex 0) (Q.vertex 1) (Q.vertex j.succ)

lemma fanAngle_zero (Q : StrictSphericalPolygon n) : Q.fanAngle 0 = 0 := by
  have ht := sphereTangent_unit (Q.vertex 0) (Q.vertex 1) (Q.unit 0) (Q.unit 1)
    (Q.edge_cross_ne_zero 0)
  change Real.arccos (inner ℝ (sphereTangent (Q.vertex 0) (Q.vertex 1))
    (sphereTangent (Q.vertex 0) (Q.vertex 1))) = 0
  simp [ht]

lemma fan_support (Q : StrictSphericalPolygon n) (j : Fin (n + 2)) (hj : j ≠ 0) :
    0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) (Q.vertex j.succ) := by
  apply Q.support 0 j.succ (Fin.succ_ne_zero j)
  intro heq
  apply hj
  apply Fin.ext
  have hv := congrArg Fin.val heq
  norm_num at hv ⊢
  omega

lemma fan_successor_index (j : Fin (n + 1)) :
    j.castSucc.succ + 1 = j.succ.succ := by
  apply Fin.ext
  rw [Fin.val_add_one]
  split_ifs with h
  · have hv := congrArg Fin.val h
    simp at hv
    omega
  · simp

theorem fanAngle_strictMono (Q : StrictSphericalPolygon n) : StrictMono Q.fanAngle := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  have hside := Q.support j.castSucc.succ 0 (Fin.succ_ne_zero j.castSucc).symm
    (by rw [fan_successor_index]; exact (Fin.succ_ne_zero j.succ).symm)
  rw [fan_successor_index, triple_cyclic, triple_cyclic] at hside
  have hanglepos := sphereVertexAngle_pos (Q.vertex 0) (Q.vertex j.castSucc.succ)
    (Q.vertex j.succ.succ) (Q.unit 0) (Q.unit _) (Q.unit _) hside
  by_cases hj : j = 0
  · subst j
    change Q.fanAngle 0 < Q.fanAngle (Fin.succ 0)
    rw [Q.fanAngle_zero]
    exact hanglepos
  · have hleft : j.castSucc ≠ 0 := by
      intro heq
      apply hj
      apply Fin.ext
      exact congrArg (fun k : Fin (n + 2) => k.val) heq
    have hadd := sphereVertexAngle_add (Q.vertex 0) (Q.vertex 1)
      (Q.vertex j.castSucc.succ) (Q.vertex j.succ.succ)
      (Q.unit 0) (Q.unit 1) (Q.unit _) (Q.unit _)
      (Q.fan_support j.castSucc hleft) hside (Q.fan_support j.succ (Fin.succ_ne_zero j))
    change Q.fanAngle j.castSucc + _ = Q.fanAngle j.succ at hadd
    linarith

/-- All diagonals of the fan from vertex zero have the orientation forced
by the supporting edge halfspaces, not merely the consecutive triples. -/
theorem fan_triple_pos (Q : StrictSphericalPolygon n) (j k : Fin (n + 2)) (hjk : j < k) :
    0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex j.succ)) (Q.vertex k.succ) := by
  have hk : k ≠ 0 := by intro h; subst k; exact (not_lt_of_ge (Fin.zero_le j)) hjk
  by_cases hj : j = 0
  · subst j
    exact Q.fan_support k hk
  · exact sphere_triple_pos_of_vertexAngle_lt (Q.vertex 0) (Q.vertex 1)
      (Q.vertex j.succ) (Q.vertex k.succ) (Q.unit 0) (Q.unit 1) (Q.unit _) (Q.unit _)
      (Q.fan_support j hj) (Q.fan_support k hk) (Q.fanAngle_strictMono hjk)

end StrictSphericalPolygon

end SquareAntiprismVerification
