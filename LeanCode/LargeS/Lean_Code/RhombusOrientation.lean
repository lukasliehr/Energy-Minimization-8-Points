import Lean_Code.RhombusGram
import Lean_Code.CrossAlgebra
import Lean_Code.SphericalCone

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma contact_chain_triple_sq (a b d : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c) :
    inner ℝ (crossVec a b) d ^ 2 =
      (1 - inner ℝ a d) * (1 + inner ℝ a d - 2 * c ^ 2) := by
  have h := cross_inner_cross (crossVec a b) (crossVec b d) (crossVec a b) (crossVec b d)
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hdb : inner ℝ d b = c := (real_inner_comm b d).trans hbd
  have hda : inner ℝ d a = inner ℝ a d := real_inner_comm a d
  simp only [cross_cross_cyclic, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, cross_inner_cross,
    real_inner_self_eq_norm_sq, ha, hb, hd, one_pow, hab, hbd, hba, hdb, hda] at h
  have habsq : ‖crossVec a b‖ ^ 2 = 1 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, cross_inner_cross]
    simp [ha, hb, hab, hba, pow_two]
  have hbdsq : ‖crossVec b d‖ ^ 2 = 1 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, cross_inner_cross]
    simp [hb, hd, hbd, hdb, pow_two]
  rw [habsq, hbdsq] at h
  nlinarith

theorem contact_rhombus_triple_ne_zero (a b d e : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hc : 0 < c) (had : a ≠ d) (hbe : b ≠ e)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c)
    (hde : inner ℝ d e = c) (hea : inner ℝ e a = c) :
    inner ℝ (crossVec a b) d ≠ 0 := by
  let Q : Fin 4 → ℝ³ := ![a, b, d, e]
  have hQ : ∀ i, ‖Q i‖ = 1 := by intro i; fin_cases i <;> simp [Q, ha, hb, hd, he]
  have hrel := rhombus_diagonal_identity Q c hQ had hbe hab hbd hde hea
  change (1 + inner ℝ a d) * (1 + inner ℝ b e) = 4 * c ^ 2 at hrel
  have hxlow : -1 ≤ inner ℝ a d := by
    have h := abs_real_inner_le_norm a d
    rw [ha, hd, one_mul] at h
    exact (abs_le.mp h).1
  have hylow : -1 ≤ inner ℝ b e := by
    have h := abs_real_inner_le_norm b e
    rw [hb, he, one_mul] at h
    exact (abs_le.mp h).1
  have hx := unit_inner_lt_one a d ha hd had
  have hy := unit_inner_lt_one b e hb he hbe
  have hshort := (rhombus_diagonals_short_scalar c (inner ℝ a d) (inner ℝ b e) hc
    ⟨hxlow, hx⟩ ⟨hylow, hy⟩ hrel).1
  have hs := contact_chain_triple_sq a b d c ha hb hd hab hbd
  intro hzero
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hs
  have hp := mul_pos (sub_pos.mpr hx)
    (show 0 < 1 + inner ℝ a d - 2 * c ^ 2 by linarith)
  linarith

/-- The two diagonal midpoints of a spherical contact quadrilateral lie
on the same ray. The identity is obtained from its rank-three Gram matrix. -/
theorem contact_rhombus_sum_relation (a b d e : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (had : a ≠ d) (hbe : b ≠ e)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c)
    (hde : inner ℝ d e = c) (hea : inner ℝ e a = c) :
    (1 + inner ℝ a d) • (b + e) = (2 * c) • (a + d) := by
  let Q : Fin 4 → ℝ³ := ![a, b, d, e]
  have hQ : ∀ i, ‖Q i‖ = 1 := by
    intro i
    fin_cases i <;> simp [Q, ha, hb, hd, he]
  have hrel := rhombus_diagonal_identity Q c hQ had hbe hab hbd hde hea
  change (1 + inner ℝ a d) * (1 + inner ℝ b e) = 4 * c ^ 2 at hrel
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hdb : inner ℝ d b = c := (real_inner_comm b d).trans hbd
  have hed : inner ℝ e d = c := (real_inner_comm d e).trans hde
  have hae : inner ℝ a e = c := (real_inner_comm e a).trans hea
  have hda : inner ℝ d a = inner ℝ a d := real_inner_comm a d
  have heb : inner ℝ e b = inner ℝ b e := real_inner_comm b e
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, starRingEnd_apply, star_trivial,
    real_inner_self_eq_norm_sq, ha, hb, hd, he, one_pow,
    hab, hbd, hde, hea, hba, hdb, hed, hae, hda, heb]
  nlinarith [congrArg (fun t : ℝ => (1 + inner ℝ a d) * t) hrel]

/-- A contact quadrilateral cannot have opposite orientation signs at
successive corners. One positive turn fixes the orientation of all four. -/
theorem contact_rhombus_orientations (a b d e : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hc : 0 < c) (hbe : b ≠ e)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c)
    (hde : inner ℝ d e = c) (hea : inner ℝ e a = c)
    (ht : 0 < inner ℝ (crossVec a b) d) :
    0 < inner ℝ (crossVec a b) e ∧
    0 < inner ℝ (crossVec a d) e ∧
    0 < inner ℝ (crossVec b d) e := by
  have had : a ≠ d := by
    intro h
    rw [← h, crossVec_inner_left] at ht
    exact (lt_irrefl 0) ht
  have hrel := contact_rhombus_sum_relation a b d e c ha hb hd he had hbe hab hbd hde hea
  have hpos : 0 < 1 + inner ℝ a d := by
    have h := contact_diagonal_short a b d c ha hb hd hab hbd ht.ne'
    nlinarith [sq_pos_of_pos hc]
  have hab' := congrArg (fun z : ℝ³ => inner ℝ (crossVec a b) z) hrel
  have had' := congrArg (fun z : ℝ³ => inner ℝ (crossVec a d) z) hrel
  have hbd' := congrArg (fun z : ℝ³ => inner ℝ (crossVec b d) z) hrel
  simp only [inner_smul_right, inner_add_right, crossVec_inner_left,
    crossVec_inner_right, zero_add, add_zero] at hab' had' hbd'
  have hdab : inner ℝ (crossVec a d) b = -inner ℝ (crossVec a b) d := by
    rw [← triple_cyclic, crossVec_swap, inner_neg_left]
  have hbda : inner ℝ (crossVec b d) a = inner ℝ (crossVec a b) d := by
    rw [← triple_cyclic]
  rw [hdab] at had'
  rw [hbda] at hbd'
  have hp := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hc) ht
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_pos_iff_of_pos_left hpos).mp (hab'.symm ▸ hp)
  · have heq : inner ℝ (crossVec a d) e = inner ℝ (crossVec a b) d := by nlinarith
    rwa [heq]
  · exact (mul_pos_iff_of_pos_left hpos).mp (hbd'.symm ▸ hp)

end SquareAntiprismVerification
