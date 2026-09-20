import Lean_Code.PackingEndgame

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

def rhombusDelta (b β : ℝ) : ℝ :=
  2 * Real.arctan (b * Real.cos (β / 2) / Real.sin (β / 2))

def rhombusDenominator (b β : ℝ) : ℝ :=
  Real.sin (β / 2) ^ 2 + b ^ 2 * Real.cos (β / 2) ^ 2

lemma rhombusDenominator_pos (b β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    0 < rhombusDenominator b β := by
  have hs : 0 < Real.sin (β / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])
  unfold rhombusDenominator
  nlinarith [sq_pos_of_pos hs, mul_nonneg (sq_nonneg b) (sq_nonneg (Real.cos (β / 2)))]

lemma rhombusDelta_hasDerivAt (b β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    HasDerivAt (rhombusDelta b) (-b / rhombusDenominator b β) β := by
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) β := by
    simpa using (hasDerivAt_id β).div_const 2
  have hsin := (Real.hasDerivAt_sin (β / 2)).comp β hhalf
  have hcos := (Real.hasDerivAt_cos (β / 2)).comp β hhalf
  have hs : 0 < Real.sin (β / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])
  have hd := ((Real.hasDerivAt_arctan _).comp β ((hcos.const_mul b).div hsin hs.ne')).const_mul 2
  have hden := rhombusDenominator_pos b β hβ
  convert! hd using 1
  dsimp [rhombusDenominator, Function.comp_def] at hden ⊢
  field_simp [hs.ne', hden.ne']
  nlinarith [congrArg (fun x : ℝ => b * x) (Real.sin_sq_add_cos_sq (β / 2))]

lemma rhombusDelta_derivative_hasDerivAt (b β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    HasDerivAt (fun x => -b / rhombusDenominator b x)
      (-b * (b ^ 2 - 1) * Real.sin (β / 2) * Real.cos (β / 2) /
        rhombusDenominator b β ^ 2) β := by
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) β := by
    simpa using (hasDerivAt_id β).div_const 2
  have hsin := (Real.hasDerivAt_sin (β / 2)).comp β hhalf
  have hcos := (Real.hasDerivAt_cos (β / 2)).comp β hhalf
  have hden := rhombusDenominator_pos b β hβ
  have hd := (hasDerivAt_const β (-b)).div ((hsin.pow 2).add ((hcos.pow 2).const_mul (b ^ 2))) hden.ne'
  convert! hd using 1
  dsimp [rhombusDenominator, Function.comp_def] at hden ⊢
  field_simp [hden.ne']
  ring

theorem rhombusDelta_strictConcave (b : ℝ) (hb : 1 < b) :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) Real.pi) (rhombusDelta b) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioo _ _)
  · intro β hβ
    exact (rhombusDelta_hasDerivAt b β hβ).continuousAt.continuousWithinAt
  · intro β hβ
    have hβ' : β ∈ Set.Ioo (0 : ℝ) Real.pi := interior_subset hβ
    have heq : deriv (rhombusDelta b) =ᶠ[nhds β] (fun x => -b / rhombusDenominator b x) := by
      have hnear : ∀ᶠ x in nhds β, x ∈ Set.Ioo (0 : ℝ) Real.pi :=
        isOpen_Ioo.mem_nhds hβ'
      filter_upwards [hnear] with x hx
      exact (rhombusDelta_hasDerivAt b x hx).deriv
    change deriv (deriv (rhombusDelta b)) β < 0
    rw [((rhombusDelta_derivative_hasDerivAt b β hβ').congr_of_eventuallyEq heq).deriv]
    have hs : 0 < Real.sin (β / 2) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hβ'.1]) (by linarith [hβ'.2, Real.pi_pos])
    have hc : 0 < Real.cos (β / 2) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hβ'.1, Real.pi_pos], by linarith [hβ'.2]⟩
    have hbb : 0 < b ^ 2 - 1 := by nlinarith
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by linarith : -b < 0) hbb) hs) hc
    · exact sq_pos_of_pos (rhombusDenominator_pos b β hβ')

def rhombusArea (b β : ℝ) : ℝ := 2 * β + 2 * rhombusDelta b β - 2 * Real.pi

theorem rhombusArea_strictConcave (b : ℝ) (hb : 1 < b) :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) Real.pi) (rhombusArea b) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy hxy a d ha hd had
  have h := (rhombusDelta_strictConcave b hb).2 hx hy hxy ha hd had
  change a * rhombusArea b x + d * rhombusArea b y < rhombusArea b (a * x + d * y)
  change a * rhombusDelta b x + d * rhombusDelta b y < rhombusDelta b (a * x + d * y) at h
  have hπ : (a + d) * Real.pi = Real.pi := by rw [had, one_mul]
  dsimp [rhombusArea]
  nlinarith

end SquareAntiprismVerification
