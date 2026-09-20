import Lean_Code.SphericalCone
import Lean_Code.BoundaryPolygons

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Positive cones on disjoint contact edges cannot meet away from zero.
The exposing normals are the sums of the two endpoints. -/
lemma contact_edge_cones_disjoint (a b d e : ℝ³) (c l μ ν ξ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hde : inner ℝ d e = c)
    (had : inner ℝ a d ≤ c) (hae : inner ℝ a e ≤ c)
    (hbd : inner ℝ b d ≤ c) (hbe : inner ℝ b e ≤ c)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hξ : 0 ≤ ξ)
    (hpos : 0 < l + μ)
    (heq : l • a + μ • b = ν • d + ξ • e) : False := by
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hed : inner ℝ e d = c := (real_inner_comm d e).trans hde
  have h₁ := congrArg (fun z : ℝ³ => inner ℝ (a + b) z) heq
  have h₂ := congrArg (fun z : ℝ³ => inner ℝ z (d + e)) heq
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq,
    ha, hb, hd, he, hab, hba, hde, hed, one_pow] at h₁ h₂
  have hleft : (1 + c) * (l + μ) ≤ 2 * c * (ν + ξ) := by
    nlinarith [mul_le_mul_of_nonneg_left had hν, mul_le_mul_of_nonneg_left hbd hν,
      mul_le_mul_of_nonneg_left hae hξ, mul_le_mul_of_nonneg_left hbe hξ]
  have hright : (1 + c) * (ν + ξ) ≤ 2 * c * (l + μ) := by
    nlinarith [mul_le_mul_of_nonneg_left had hl, mul_le_mul_of_nonneg_left hae hl,
      mul_le_mul_of_nonneg_left hbd hμ, mul_le_mul_of_nonneg_left hbe hμ]
  have htotal : 0 < l + μ + ν + ξ := by linarith
  nlinarith [mul_pos (sub_pos.mpr hc.2) htotal]

/-- Two successive strict left turns in a separated contact chain force
both other orientations of its four vertices to be positive. -/
theorem contact_four_chain_convex (a b d e : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1) (he : ‖e‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hbd : inner ℝ b d = c) (hde : inner ℝ d e = c)
    (had : inner ℝ a d ≤ c) (hae : inner ℝ a e ≤ c) (hbe : inner ℝ b e ≤ c)
    (ht : 0 < inner ℝ (crossVec a b) d)
    (hA : 0 < inner ℝ (crossVec b d) e) :
    0 < inner ℝ (crossVec a b) e ∧ 0 < inner ℝ (crossVec a d) e := by
  let t := inner ℝ (crossVec a b) d
  let A := inner ℝ (crossVec b d) e
  let B := inner ℝ (crossVec d a) e
  let C := inner ℝ (crossVec a b) e
  have ht0 : t ≠ 0 := ht.ne'
  have hA0 : A ≠ 0 := hA.ne'
  have hrep : t • e = A • a + B • b + C • d := triple_cramer a b d e
  have hdiag₁ := contact_diagonal_short a b d c ha hb hd hab hbd ht.ne'
  have hdiag₂ := contact_diagonal_short b d e c hb hd he hbd hde hA.ne'
  have heb : e ≠ b := by
    intro h
    rw [h, real_inner_self_eq_norm_sq, hb] at hbe
    norm_num at hbe
    linarith [hc.2]
  have hadne : a ≠ d := by
    intro h
    rw [h, real_inner_self_eq_norm_sq, hd] at had
    norm_num at had
    linarith [hc.2]
  have hB : B < 0 := by
    by_contra hn
    have hB0 : 0 ≤ B := le_of_not_gt hn
    by_cases hC : 0 ≤ C
    · have hecone : e = (A / t) • a + (B / t) • b + (C / t) • d := by
        have h := congrArg (fun v : ℝ³ => t⁻¹ • v) hrep
        simpa [smul_add, smul_smul, ht0, div_eq_mul_inv, mul_comm] using h
      have hcover := contact_rhombus_cone_covering a b d e c (A / t) (B / t) (C / t)
        ha hb hd he hc.1 hab ((real_inner_comm b d).trans hbd) hdiag₁
        (div_nonneg hA.le ht.le) (div_nonneg hB0 ht.le) (div_nonneg hC ht.le) hecone heb
      have hea : inner ℝ e a ≤ c := (real_inner_comm a e).trans_le hae
      have hed : inner ℝ e d = c := (real_inner_comm d e).trans hde
      rcases hcover with h | h
      · exact (not_lt_of_ge hea) h
      · rw [hed] at h
        exact (lt_irrefl c) h
    · have hCneg : C < 0 := lt_of_not_ge hC
      have hcones : A • a + B • b = (-C) • d + t • e := by
        rw [hrep]
        module
      exact contact_edge_cones_disjoint a b d e c A B (-C) t ha hb hd he hc hab hde
        had hae hbd.le hbe hA.le hB0 (neg_nonneg.mpr hCneg.le) ht.le
        (by linarith) hcones
  have hC : 0 < C := by
    by_contra hn
    have hC0 : C ≤ 0 := le_of_not_gt hn
    have hacone : a = ((-B) / A) • b + ((-C) / A) • d + (t / A) • e := by
      have hsolve : A • a = (-B) • b + (-C) • d + t • e := by
        rw [hrep]
        module
      have h := congrArg (fun v : ℝ³ => A⁻¹ • v) hsolve
      simpa [smul_add, smul_smul, hA0, div_eq_mul_inv, mul_comm] using h
    have hcover := contact_rhombus_cone_covering b d e a c ((-B) / A) ((-C) / A) (t / A)
      hb hd he ha hc.1 hbd ((real_inner_comm d e).trans hde) hdiag₂
      (div_nonneg (neg_nonneg.mpr hB.le) hA.le)
      (div_nonneg (neg_nonneg.mpr hC0) hA.le) (div_nonneg ht.le hA.le) hacone hadne
    rcases hcover with h | h
    · rw [hab] at h
      exact (lt_irrefl c) h
    · exact (not_lt_of_ge hae) h
  refine ⟨hC, ?_⟩
  have hswap : crossVec a d = -crossVec d a := by
    ext i
    fin_cases i <;> simp [crossVec] <;> ring
  rw [hswap, inner_neg_left]
  exact neg_pos.mpr hB

/-- A positively oriented contact triangle occupies the actual next sector;
the boundary permutation cannot turn past its third vertex. -/
theorem contact_triangle_next_tip (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (d : ContactDart Y c) (k : Fin 8)
    (hik : inner ℝ (Y d.1) (Y k) = c)
    (hjk : inner ℝ (Y d.2.val) (Y k) = c)
    (horient : 0 < inner ℝ (crossVec (Y d.1) (Y d.2.val)) (Y k)) :
    (contactFaceNext Y c hY hc d).2.val = k := by
  let e := contactFaceNext Y c hY hc d
  have hturn := contactFaceNext_triple_pos Y c hY hc hirr d
  have hecontact : inner ℝ (Y d.2.val) (Y e.2.val) = c := e.2.property.2
  have hkie : k ≠ d.1 := by
    intro h
    rw [h, crossVec_inner_left] at horient
    exact (lt_irrefl 0) horient
  have hdie : d.1 ≠ e.2.val := by
    intro h
    change 0 < inner ℝ (crossVec (Y d.1) (Y d.2.val)) (Y e.2.val) at hturn
    rw [← h, crossVec_inner_left] at hturn
    exact (lt_irrefl 0) hturn
  by_contra hne
  change e.2.val ≠ k at hne
  have hki : inner ℝ (Y k) (Y d.1) = c := (real_inner_comm (Y d.1) (Y k)).trans hik
  have hkj : inner ℝ (Y k) (Y d.2.val) = c :=
    (real_inner_comm (Y d.2.val) (Y k)).trans hjk
  have horient' : 0 < inner ℝ (crossVec (Y k) (Y d.1)) (Y d.2.val) := by
    rwa [triple_cyclic]
  have hfour := contact_four_chain_convex (Y k) (Y d.1) (Y d.2.val) (Y e.2.val) c
    (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hc hki d.2.property.2 hecontact
    hkj.le (hbound k e.2.val hne.symm) (hbound d.1 e.2.val hdie) horient' hturn
  have hleft : 0 < inner ℝ (crossVec (Y d.2.val) (Y e.2.val)) (Y k) := by
    rw [← triple_cyclic]
    exact hfour.2
  have hright : 0 < inner ℝ (crossVec (Y d.2.val) (Y k)) (Y d.1) := by
    rw [← triple_cyclic]
    exact horient
  exact (not_lt_of_ge hjk.symm.le)
    (contact_corner_interior_strict Y c hY hc hirr hbound d k hleft hright)

lemma contactDart_ext {Y : Fin 8 → ℝ³} {c : ℝ} {d e : ContactDart Y c}
    (hbase : d.1 = e.1) (htip : d.2.val = e.2.val) : d = e := by
  rcases d with ⟨i, j, hj⟩
  rcases e with ⟨k, l, hl⟩
  dsimp at hbase htip
  subst k
  subst l
  rfl

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

lemma two_steps_ne (C : ContactBoundaryCycle Y c hY hc) (hirr : PackingIrreducible c Y)
    (i : Fin (C.size + 1)) : C.vertex i ≠ C.vertex (i + 1 + 1) := by
  intro heq
  have h := C.strict_turn hirr i
  rw [← heq, crossVec_inner_left] at h
  exact (lt_irrefl 0) h

/-- Closing a triangle forces the next directed edge to be its first edge. -/
lemma triangle_return (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (i : Fin (C.size + 1)) (heq : C.vertex (i + 1 + 1 + 1) = C.vertex i) :
    C.point (i + 1 + 1 + 1) = C.point i := by
  have h := contact_triangle_next_tip Y c hY hc hirr hbound (C.point (i + 1 + 1))
    (C.vertex (i + 1))
    ((real_inner_comm _ _).trans (C.contact (i + 1)))
    (by rw [← C.vertex_next, heq]; exact C.contact i)
    (by rw [← C.vertex_next, heq, triple_cyclic]; exact C.strict_turn hirr i)
  rw [C.step] at h
  apply contactDart_ext heq
  simpa only [C.vertex_next] using h

lemma three_steps_ne (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hlength : 3 < C.size + 1) (i : Fin (C.size + 1)) :
    C.vertex i ≠ C.vertex (i + 1 + 1 + 1) := by
  intro heq
  have hi := C.injective (C.triangle_return hirr hbound i heq.symm)
  have hthree : (3 : Fin (C.size + 1)) = 0 := by
    have hsum : i + 1 + 1 + 1 = i + 3 := by
      simp only [add_assoc]
      congr 1
      apply Fin.ext
      change (1 % (C.size + 1) + (1 % (C.size + 1) + 1 % (C.size + 1)) % (C.size + 1)) %
        (C.size + 1) = 3 % (C.size + 1)
      have h1 : 1 % (C.size + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      have h2 : 2 % (C.size + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      norm_num [h1, h2]
    rw [hsum] at hi
    exact add_left_cancel (hi.trans (add_zero i).symm)
  have hv := congrArg Fin.val hthree
  norm_num [Nat.mod_eq_of_lt hlength] at hv

lemma four_chain_orientations (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hlength : 3 < C.size + 1) (i : Fin (C.size + 1)) :
    0 < inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1))))
      (Y (C.vertex (i + 1 + 1 + 1))) ∧
    0 < inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1 + 1))))
      (Y (C.vertex (i + 1 + 1 + 1))) :=
  contact_four_chain_convex _ _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hc
    (C.contact i) (C.contact (i + 1)) (C.contact (i + 1 + 1))
    (hbound _ _ (C.two_steps_ne hirr i)) (hbound _ _ (C.three_steps_ne hirr hbound hlength i))
    (hbound _ _ (C.two_steps_ne hirr (i + 1))) (C.strict_turn hirr i)
    (C.strict_turn hirr (i + 1))

end ContactBoundaryCycle

end SquareAntiprismVerification
