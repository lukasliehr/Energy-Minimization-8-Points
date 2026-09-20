import Lean_Code.RhombusConcavity
import Lean_Code.ContactGeometryGlobal
import Lean_Code.VertexArea

open Real
noncomputable section
namespace SquareAntiprismVerification

lemma cos_two_pi_fifths : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have hsq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith

lemma packing_equilateral_angle_range (t : ℝ) (ht : 0 < t) (hta : t ≤ aInf) :
    let α := Real.arccos (t / (1 + t))
    2 * Real.pi / 5 < α ∧ α < Real.pi / 2 ∧ Real.cos α = t / (1 + t) := by
  have htthird : t < 1 / 3 := hta.trans_lt aInf_lt_one_third
  have hden : 0 < 1 + t := by linarith
  have hratio : 0 < t / (1 + t) := div_pos ht hden
  have hquarter : t / (1 + t) < 1 / 4 := (div_lt_iff₀ hden).mpr (by linarith)
  have hcos := Real.cos_arccos (by linarith : -1 ≤ t / (1 + t)) (by linarith : t / (1 + t) ≤ 1)
  have hsqrt : 2 < Real.sqrt 5 := by
    have hs : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hcoslow : 1 / 4 < Real.cos (2 * Real.pi / 5) := by rw [cos_two_pi_fifths]; linarith
  refine ⟨?_, Real.arccos_lt_pi_div_two.mpr hratio, hcos⟩
  by_contra hn
  have hle : Real.arccos (t / (1 + t)) ≤ 2 * Real.pi / 5 := le_of_not_gt hn
  have hc := Real.strictAntiOn_cos.antitoneOn
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hle
  rw [hcos] at hc
  linarith

lemma equilateral_half_angle_relations (t α : ℝ) (ht : 0 < t)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hcos : Real.cos α = t / (1 + t)) :
    (1 / t) * Real.cos (α / 2) / Real.sin (α / 2) = Real.tan α ∧
    (1 / t) * Real.cos α / Real.sin α = Real.tan (α / 2) := by
  have hs : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hα.1]) (by linarith [hα.2, Real.pi_pos])
  have hc : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2, Real.pi_pos]⟩
  have hca : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hsa : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    convert Real.sin_two_mul (α / 2) using 1 <;> congr 1 <;> ring
  have hca2 : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (α / 2) using 1 <;> congr 1 <;> ring
  have hsin2 : 2 * Real.sin (α / 2) ^ 2 = 1 - Real.cos α := by
    nlinarith [Real.sin_sq_add_cos_sq (α / 2)]
  have hlinear : Real.cos α * (1 + t) = t :=
    (eq_div_iff (by linarith : 1 + t ≠ 0)).mp hcos
  have hstar : Real.cos α = 2 * t * Real.sin (α / 2) ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => t * x) hsin2]
  constructor
  · rw [Real.tan_eq_sin_div_cos, hsa]
    field_simp [ht.ne', hs.ne', hca.ne']
    rw [hstar]
    ring
  · rw [Real.tan_eq_sin_div_cos, hsa, hstar]
    field_simp [ht.ne', hs.ne', hc.ne']

lemma rhombusDelta_endpoints (t α : ℝ) (ht : 0 < t)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hcos : Real.cos α = t / (1 + t)) :
    rhombusDelta (1 / t) α = 2 * α ∧ rhombusDelta (1 / t) (2 * α) = α := by
  have h := equilateral_half_angle_relations t α ht hα hcos
  constructor
  · unfold rhombusDelta
    rw [h.1, Real.arctan_tan (by linarith [hα.1, Real.pi_pos]) hα.2]
  · unfold rhombusDelta
    rw [show 2 * α / 2 = α by ring, h.2,
      Real.arctan_tan (by linarith [hα.1, Real.pi_pos]) (by linarith [hα.2, Real.pi_pos])]
    ring

lemma rhombusArea_endpoints (t α : ℝ) (ht : 0 < t)
    (hα : α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hcos : Real.cos α = t / (1 + t)) :
    rhombusArea (1 / t) α = 2 * (3 * α - Real.pi) ∧
      rhombusArea (1 / t) (2 * α) = 2 * (3 * α - Real.pi) := by
  have h := rhombusDelta_endpoints t α ht hα hcos
  constructor
  · unfold rhombusArea
    rw [h.1]
    ring
  · unfold rhombusArea
    rw [h.2]
    ring

lemma rhombusDelta_mem_Ioo (b β : ℝ) (hb : 0 < b) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    rhombusDelta b β ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hs : 0 < Real.sin (β / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])
  have hc : 0 < Real.cos (β / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩
  have hp := Real.arctan_pos.mpr (div_pos (mul_pos hb hc) hs)
  have hu := Real.arctan_lt_pi_div_two (b * Real.cos (β / 2) / Real.sin (β / 2))
  unfold rhombusDelta
  constructor <;> linarith

lemma rhombusDelta_tan_relation (b β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.tan (β / 2) * Real.tan (rhombusDelta b β / 2) = b := by
  have hs : 0 < Real.sin (β / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])
  have hc : 0 < Real.cos (β / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩
  unfold rhombusDelta
  rw [show 2 * Real.arctan (b * Real.cos (β / 2) / Real.sin (β / 2)) / 2 =
      Real.arctan (b * Real.cos (β / 2) / Real.sin (β / 2)) by ring,
    Real.tan_arctan, Real.tan_eq_sin_div_cos]
  field_simp [hs.ne', hc.ne']

theorem rhombusDelta_unique (b β γ : ℝ) (hb : 0 < b)
    (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) (hγ : γ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hrel : Real.tan (β / 2) * Real.tan (γ / 2) = b) : γ = rhombusDelta b β := by
  have hδ := rhombusDelta_mem_Ioo b β hb hβ
  have hp : 0 < Real.tan (β / 2) := Real.tan_pos_of_pos_of_lt_pi_div_two
    (by linarith [hβ.1]) (by linarith [hβ.2])
  have ht : Real.tan (γ / 2) = Real.tan (rhombusDelta b β / 2) := by
    apply mul_left_cancel₀ hp.ne'
    rw [hrel, rhombusDelta_tan_relation b β hβ]
  have heq := Real.strictMonoOn_tan.injOn
    (show γ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hγ.1, Real.pi_pos], by linarith [hγ.2]⟩)
    (show rhombusDelta b β / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hδ.1, Real.pi_pos], by linarith [hδ.2]⟩) ht
  linarith

end SquareAntiprismVerification
