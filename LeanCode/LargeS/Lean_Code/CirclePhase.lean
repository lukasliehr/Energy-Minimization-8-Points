import Lean_Code.SphericalMetric

open Real
noncomputable section
namespace SquareAntiprismVerification

/-- A phase in `(-π, π]` for a unit planar vector, with a fixed convention
at the negative horizontal axis. -/
def circlePhase (x y : ℝ) : ℝ := if 0 ≤ y then Real.arccos x else -Real.arccos x

lemma circle_coordinate_range (x y : ℝ) (hunit : x ^ 2 + y ^ 2 = 1) :
    x ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor <;> nlinarith [sq_nonneg y]

lemma circlePhase_cos (x y : ℝ) (hunit : x ^ 2 + y ^ 2 = 1) :
    Real.cos (circlePhase x y) = x := by
  have hx := circle_coordinate_range x y hunit
  unfold circlePhase
  split_ifs <;> simp [Real.cos_arccos hx.1 hx.2]

lemma circlePhase_sin (x y : ℝ) (hunit : x ^ 2 + y ^ 2 = 1) :
    Real.sin (circlePhase x y) = y := by
  have hx := circle_coordinate_range x y hunit
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx.1 hx.2
  have htrig := Real.sin_sq_add_cos_sq (Real.arccos x)
  rw [hcos] at htrig
  have hs : 0 ≤ Real.sin (Real.arccos x) :=
    Real.sin_nonneg_of_mem_Icc ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  unfold circlePhase
  split_ifs with hy
  · nlinarith
  · rw [Real.sin_neg]
    have hyneg : y < 0 := lt_of_not_ge hy
    nlinarith

theorem circlePhase_range (x y : ℝ) (hunit : x ^ 2 + y ^ 2 = 1) :
    circlePhase x y ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hx := circle_coordinate_range x y hunit
  unfold circlePhase
  split_ifs with hy
  · exact ⟨by linarith [Real.arccos_nonneg x, Real.pi_pos], Real.arccos_le_pi x⟩
  · have hyneg : y < 0 := lt_of_not_ge hy
    have hxgt : -1 < x := by nlinarith [sq_pos_of_neg hyneg]
    have hlt := Real.arccos_lt_pi.mpr hxgt
    exact ⟨by linarith, by linarith [Real.arccos_nonneg x, Real.pi_pos]⟩

theorem circlePhase_injective (x y u v : ℝ)
    (hxy : x ^ 2 + y ^ 2 = 1) (huv : u ^ 2 + v ^ 2 = 1)
    (hphase : circlePhase x y = circlePhase u v) : x = u ∧ y = v := by
  constructor
  · have h := congrArg Real.cos hphase
    simpa only [circlePhase_cos x y hxy, circlePhase_cos u v huv] using h
  · have h := congrArg Real.sin hphase
    simpa only [circlePhase_sin x y hxy, circlePhase_sin u v huv] using h

lemma circlePhase_inner (x y u v : ℝ)
    (hxy : x ^ 2 + y ^ 2 = 1) (huv : u ^ 2 + v ^ 2 = 1) :
    x * u + y * v = Real.cos (circlePhase x y - circlePhase u v) := by
  rw [Real.cos_sub, circlePhase_cos x y hxy, circlePhase_cos u v huv,
    circlePhase_sin x y hxy, circlePhase_sin u v huv]

end SquareAntiprismVerification
