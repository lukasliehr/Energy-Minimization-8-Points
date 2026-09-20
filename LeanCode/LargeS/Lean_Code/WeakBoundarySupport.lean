import Lean_Code.ContactChainConvexity

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- On a supporting great circle, the outgoing contact ray is unique once
the side containing a strictly positive witness is specified. -/
lemma supporting_contact_ray_unique (p a d b : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hpa : inner ℝ p a = c) (hpb : inner ℝ p b = c)
    (ht : 0 < inner ℝ (crossVec p a) d)
    (hplane : inner ℝ (crossVec p a) b = 0)
    (hside : 0 ≤ inner ℝ (crossVec p b) d) : b = a := by
  let t := inner ℝ (crossVec p a) d
  let A := inner ℝ (crossVec a d) b / t
  let B := inner ℝ (crossVec d p) b / t
  have ht0 : t ≠ 0 := ht.ne'
  have hrep : b = A • p + B • a := by
    have h := congrArg (fun v : ℝ³ => t⁻¹ • v) (triple_cramer p a d b)
    simpa [t, A, B, hplane, smul_add, smul_smul, ht.ne',
      div_eq_mul_inv, mul_comm] using h
  have hB : 0 ≤ B := by
    have heq : inner ℝ (crossVec p b) d = B * t := by
      rw [hrep]
      simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ, t]
      <;> ring
    rw [heq] at hside
    exact nonneg_of_mul_nonneg_left hside ht
  have hlin : A + B * c = c := by
    rw [hrep] at hpb
    simpa [inner_add_right, inner_smul_right, hp, hpa] using hpb
  have hsq : A ^ 2 + B ^ 2 + 2 * A * B * c = 1 := by
    have h := real_inner_self_eq_norm_sq b
    rw [hb, hrep] at h
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq, hp, ha,
      hpa, show inner ℝ a p = c from (real_inner_comm p a).trans hpa] at h
    nlinarith [h]
  have hfac : (1 - c ^ 2) * (B ^ 2 - 1) = 0 := by
    have hA : A = c - B * c := by linarith
    rw [hA] at hsq
    nlinarith [hsq]
  have hcpos : 0 < 1 - c ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - c by linarith [hc.2])
      (show 0 < 1 + c by linarith [hc.1])]
  have hBsq : B ^ 2 = 1 := by
    have h := (mul_eq_zero.mp hfac).resolve_left hcpos.ne'
    linarith
  have hB1 : B = 1 := by nlinarith
  have hA0 : A = 0 := by rw [hB1] at hlin; linarith
  simpa [hA0, hB1] using hrep

/-- Weak support at an edge and the two neighboring edges is strict at a
separated unit point which is not an endpoint. This is the algebraic version
of excluding an extension through a strictly convex polygon corner. -/
lemma contact_edge_strict_of_weak_neighbors (p a b d z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hz : ‖z‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hab : inner ℝ a b = c)
    (hprev : 0 < inner ℝ (crossVec p a) b)
    (hnext : 0 < inner ℝ (crossVec a b) d)
    (hpz : 0 ≤ inner ℝ (crossVec p a) z)
    (haz : 0 ≤ inner ℝ (crossVec a b) z)
    (hbz : 0 ≤ inner ℝ (crossVec b d) z)
    (hsepA : inner ℝ a z ≤ c) (hsepB : inner ℝ b z ≤ c) :
    0 < inner ℝ (crossVec a b) z := by
  by_contra hnot
  have hzero : inner ℝ (crossVec a b) z = 0 := le_antisymm (le_of_not_gt hnot) haz
  let t := inner ℝ (crossVec a b) d
  let A := inner ℝ (crossVec b d) z / t
  let B := inner ℝ (crossVec d a) z / t
  have hA : 0 ≤ A := div_nonneg hbz hnext.le
  have hrep : z = A • a + B • b := by
    have h := congrArg (fun v : ℝ³ => t⁻¹ • v) (triple_cramer a b d z)
    simpa [t, A, B, hzero, smul_add, smul_smul, hnext.ne',
      div_eq_mul_inv, mul_comm] using h
  have hB : 0 ≤ B := by
    rw [hrep] at hpz
    simp only [inner_add_right, inner_smul_right, crossVec_inner_right,
      mul_zero, zero_add] at hpz
    exact nonneg_of_mul_nonneg_left hpz hprev
  have hnorm : 1 ≤ A + B := by
    have h := norm_add_le (A • a) (B • b)
    rw [← hrep, hz, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hA, abs_of_nonneg hB, ha, hb] at h
    simpa using h
  have hsum : (1 + c) * (A + B) ≤ 2 * c := by
    rw [hrep] at hsepA hsepB
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      ha, hb, hab, show inner ℝ b a = c from (real_inner_comm a b).trans hab] at hsepA hsepB
    nlinarith [hsepA, hsepB]
  nlinarith [mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 1 + c by linarith [hc.1]), hc.2]

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y}
  {hc : c ∈ Set.Ioo (0 : ℝ) 1}

/-- All boundary vertices are in the closed left halfspace of every edge. -/
def WeakSupport (C : ContactBoundaryCycle Y c hY hc) : Prop :=
  ∀ i j, 0 ≤ inner ℝ (crossVec (Y (C.vertex i))
    (Y (C.vertex (i + 1)))) (Y (C.vertex j))

theorem vertex_injective_of_weak_support (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hs : C.WeakSupport) :
    Function.Injective C.vertex := by
  intro i j hij
  have hpq : inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1))))
      (Y (C.vertex (j + 1))) = 0 := by
    have h1 := hs i (j + 1)
    have h2 := hs j (i + 1)
    rw [← hij, triple_cyclic, crossVec_swap, inner_neg_left,
      ← triple_cyclic] at h2
    linarith
  have htip : Y (C.vertex (j + 1)) = Y (C.vertex (i + 1)) := by
    apply supporting_contact_ray_unique (Y (C.vertex i)) (Y (C.vertex (i + 1)))
      (Y (C.vertex (i + 1 + 1))) (Y (C.vertex (j + 1))) c
      (hY.1 _) (hY.1 _) (hY.1 _) hc (C.contact i)
    · simpa [hij] using C.contact j
    · exact C.strict_turn hirr i
    · exact hpq
    · simpa [hij] using hs j (i + 1 + 1)
  apply C.injective
  apply contactDart_ext
  · exact hij
  · simpa only [← C.vertex_next] using (hY.2 htip).symm

/-- Thus the shortest-path argument only has to establish closed-halfspace
support. Strict support and simplicity follow from checked contact geometry. -/
theorem strict_support_of_weak_support (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hs : C.WeakSupport) : C.StrictSupport := by
  have hinj := C.vertex_injective_of_weak_support hirr hs
  intro i j hji hjnext
  apply contact_edge_strict_of_weak_neighbors
    (Y (C.vertex (i - 1))) (Y (C.vertex i)) (Y (C.vertex (i + 1)))
    (Y (C.vertex (i + 1 + 1))) (Y (C.vertex j)) c
    (hY.1 _) (hY.1 _) (hY.1 _) hc (C.contact i)
  · simpa only [sub_add_cancel] using C.strict_turn hirr (i - 1)
  · exact C.strict_turn hirr i
  · simpa only [sub_add_cancel] using hs (i - 1) j
  · exact hs i j
  · exact hs (i + 1) j
  · exact hbound _ _ (fun h => hji (hinj h).symm)
  · exact hbound _ _ (fun h => hjnext (hinj h).symm)

end ContactBoundaryCycle
end SquareAntiprismVerification
