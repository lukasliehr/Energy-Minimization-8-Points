import Lean_Code.ReducedPatchChains

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def greatCircleTangent (m t : ℝ³) (s : ℝ) : ℝ³ :=
  -Real.sin s • m + Real.cos s • t

lemma greatCircleTangent_unit (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (s : ℝ) : ‖greatCircleTangent m t s‖ = 1 := by
  have hrev : inner ℝ t m = 0 := (real_inner_comm m t).trans horth
  have h := real_inner_self_eq_norm_sq (greatCircleTangent m t s)
  simp only [greatCircleTangent, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq,
    hm, ht, horth, hrev] at h
  change ‖-Real.sin s • m + Real.cos s • t‖ = 1
  nlinarith [Real.sin_sq_add_cos_sq s, norm_nonneg (-Real.sin s • m + Real.cos s • t)]

lemma greatCircleTangent_orthogonal (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (s : ℝ) :
    inner ℝ (greatCirclePoint m t s) (greatCircleTangent m t s) = 0 := by
  have hrev : inner ℝ t m = 0 := (real_inner_comm m t).trans horth
  simp only [greatCirclePoint, greatCircleTangent, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial,
    real_inner_self_eq_norm_sq, hm, ht, horth, hrev]
  ring

lemma greatCirclePoint_add (m t : ℝ³) (s r : ℝ) :
    greatCirclePoint (greatCirclePoint m t s) (greatCircleTangent m t s) r =
      greatCirclePoint m t (s + r) := by
  simp only [greatCirclePoint, greatCircleTangent, smul_add, smul_smul,
    Real.cos_add, Real.sin_add]
  module

lemma greatCirclePoint_backwards (m t : ℝ³) (s r : ℝ) :
    greatCirclePoint (greatCirclePoint m t s) (-greatCircleTangent m t s) r =
      greatCirclePoint m t (s - r) := by
  simp only [greatCirclePoint, greatCircleTangent, smul_add, smul_neg, smul_smul,
    neg_add_rev, Real.cos_sub, Real.sin_sub]
  module

namespace PatchArcChain

variable {ι : Type*} {patch : ι → Set ℝ³} {a b : ℝ³}

/-- Every vertex occurs at its cumulative angular length on one oriented
great circle. This is stronger than mere coplanarity of consecutive triples. -/
def FollowsCircle (m t : ℝ³) (s : ℝ) : {b : ℝ³} → PatchArcChain patch a b → Prop
  | _, .point _ => greatCirclePoint m t s = a
  | _, .tail (b := y) p _ z _ _ =>
      p.FollowsCircle m t s ∧ greatCirclePoint m t (s + p.length + sphereAngle y z) = z

lemma FollowsCircle.endpoint (p : PatchArcChain patch a b) (m t : ℝ³) (s : ℝ)
    (h : p.FollowsCircle m t s) : greatCirclePoint m t (s + p.length) = b := by
  cases p with
  | point => simpa [length, FollowsCircle] using h
  | tail => simpa only [length, ← add_assoc] using h.2

end PatchArcChain
end SquareAntiprismVerification
