import Lean_Code.ContactCycleEmbedding

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma closedShortSphereArc_comm (a b : ℝ³) : closedShortSphereArc a b = closedShortSphereArc b a := by
  have hsub (a b : ℝ³) : closedShortSphereArc a b ⊆ closedShortSphereArc b a := by
    rintro x ⟨r, hr, rfl⟩
    refine ⟨1 - r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
    unfold shortSphereArc
    congr 1
    module
  exact Set.Subset.antisymm (hsub a b) (hsub b a)

/-- A contact arc at an endpoint is locally a half of its great circle.
The auxiliary normal chooses the half pointing toward the other endpoint. -/
theorem contact_arc_endpoint_halfplane (a b n : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hna : inner ℝ n a = 0) (hnb : 0 < inner ℝ n b) :
    ∃ U : Set ℝ³, IsOpen U ∧ a ∈ U ∧ ∀ y ∈ U,
      y ∈ closedShortSphereArc a b ↔
        ‖y‖ = 1 ∧ inner ℝ (crossVec a b) y = 0 ∧ 0 ≤ inner ℝ n y := by
  let U : Set ℝ³ := {y | 0 < contactEdgeCoordinateA a b c y}
  have hden : 1 - c ^ 2 ≠ 0 := by nlinarith [hc.1, hc.2]
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hAa : contactEdgeCoordinateA a b c a = 1 := by
    unfold contactEdgeCoordinateA
    rw [real_inner_self_eq_norm_sq, ha, hba]
    field_simp
  refine ⟨U, isOpen_lt continuous_const (by unfold contactEdgeCoordinateA; fun_prop), ?_, ?_⟩
  · change 0 < contactEdgeCoordinateA a b c a
    rw [hAa]
    norm_num
  · intro y hy
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨shortSphereArc_unit a b ha hb
        (contact_endpoints_nonantipodal a b hb c hc.1 hab) r hr, ?_, ?_⟩
      · simp only [shortSphereArc, sphereNormalize_inner, inner_add_right, inner_smul_right,
          crossVec_inner_left, crossVec_inner_right, mul_zero, add_zero]
      · simp only [shortSphereArc, sphereNormalize_inner, inner_add_right, inner_smul_right,
          hna, mul_zero, zero_add]
        exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (mul_nonneg hr.1 hnb.le)
    · intro hh
      have hrep := contact_coplanar_representation a b y c ha hb hc hab hh.2.1
      have hnrep : inner ℝ n y = contactEdgeCoordinateB a b c y * inner ℝ n b := by
        conv_lhs => rw [hrep]
        simp only [inner_add_right, inner_smul_right, hna, mul_zero, zero_add]
      have hB : 0 ≤ contactEdgeCoordinateB a b c y := by
        have hn := hh.2.2
        rw [hnrep] at hn
        exact nonneg_of_mul_nonneg_left hn hnb
      exact closedShortSphereArc_mem_of_positive_combination a b y _ _ hy.le hB
        (add_pos_of_pos_of_nonneg hy hB) hh.1 hrep

namespace SimpleContactCycle

/-- Locally at a cycle vertex, only its two incident closed arcs occur.
This uses finiteness and contact-arc embedding, not separation. -/
theorem trace_local_incident {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (k : Fin (C.size + 2)) :
    ∃ U : Set ℝ³, IsOpen U ∧ Y (C.vertex k) ∈ U ∧ ∀ y ∈ U,
      y ∈ cycleArcTrace C.next (Y ∘ C.vertex) ↔
        y ∈ closedShortSphereArc (Y (C.vertex k)) (Y (C.vertex (C.next k))) ∨
        y ∈ closedShortSphereArc (Y (C.vertex (C.next.symm k))) (Y (C.vertex k)) := by
  classical
  let T : Set ℝ³ := ⋃ j : {j : Fin (C.size + 2) // j ≠ k ∧ C.next j ≠ k},
    closedShortSphereArc (Y (C.vertex j.val)) (Y (C.vertex (C.next j.val)))
  have hT : IsCompact T := by
    apply isCompact_iUnion
    intro j
    exact closedShortSphereArc_compact _ _ (hY.1 _) (hY.1 _)
      (contact_endpoints_nonantipodal _ _ (hY.1 _) c hc.1 (C.adjacent j.val).2)
  have hkT : Y (C.vertex k) ∉ T := by
    intro hh
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
    rcases closedShortSphereArc_cases _ _ _ (hY.1 _) (hY.1 _) hj with h | h | h
    · exact j.property.1 (C.injective (hY.2 h)).symm
    · exact j.property.2 (C.injective (hY.2 h)).symm
    · exact contact_arc_avoids_vertices Y c hY hc hbound _ _
        (C.adjacent j.val).1 (C.adjacent j.val).2 _ h
  refine ⟨Tᶜ, hT.isClosed.isOpen_compl, hkT, ?_⟩
  intro y hy
  constructor
  · intro hh
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
    by_cases hjk : j = k
    · subst j
      exact Or.inl hj
    by_cases hnext : C.next j = k
    · have hjprev : j = C.next.symm k := (C.next.eq_symm_apply).mpr hnext
      exact Or.inr (by simpa only [Function.comp_apply, hjprev, C.next.apply_symm_apply] using hj)
    · exact False.elim (hy (Set.mem_iUnion.mpr ⟨⟨j, hjk, hnext⟩, hj⟩))
  · rintro (h | h)
    · exact Set.mem_iUnion.mpr ⟨k, h⟩
    · exact Set.mem_iUnion.mpr ⟨C.next.symm k, by simpa only [Function.comp_apply, C.next.apply_symm_apply] using h⟩

/-- A strictly turning cycle has exactly the two boundary rays of its
convex tangent wedge in a neighborhood of the vertex. This is a statement
about the embedded trace, not yet about which complementary component lies
on each side. -/
theorem trace_local_wedge {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (k : Fin (C.size + 2))
    (hturn : 0 < inner ℝ (crossVec (Y (C.vertex k)) (Y (C.vertex (C.next k))))
      (Y (C.vertex (C.next.symm k)))) :
    let n₁ := crossVec (Y (C.vertex k)) (Y (C.vertex (C.next k)))
    let n₂ := crossVec (Y (C.vertex (C.next.symm k))) (Y (C.vertex k))
    ∃ U : Set ℝ³, IsOpen U ∧ Y (C.vertex k) ∈ U ∧ ∀ y ∈ U,
      y ∈ cycleArcTrace C.next (Y ∘ C.vertex) ↔
        ‖y‖ = 1 ∧ ((inner ℝ n₁ y = 0 ∧ 0 ≤ inner ℝ n₂ y) ∨
          (inner ℝ n₂ y = 0 ∧ 0 ≤ inner ℝ n₁ y)) := by
  dsimp only
  let v := Y (C.vertex k)
  let a := Y (C.vertex (C.next k))
  let b := Y (C.vertex (C.next.symm k))
  have hva : inner ℝ v a = c := (C.adjacent k).2
  have hbv : inner ℝ b v = c := by
    have hh : inner ℝ b (Y (C.vertex (C.next (C.next.symm k)))) = c :=
      (C.adjacent (C.next.symm k)).2
    simpa only [C.next.apply_symm_apply] using hh
  have hvb : inner ℝ v b = c := (real_inner_comm b v).trans hbv
  have hturn' : 0 < inner ℝ (crossVec b v) a := by
    rw [triple_cyclic b v a]
    exact hturn
  obtain ⟨U₀, hU₀, hv₀, hmodel₀⟩ := C.trace_local_incident hY hc hbound k
  obtain ⟨U₁, hU₁, hv₁, hmodel₁⟩ := contact_arc_endpoint_halfplane v a (crossVec b v) c
    (hY.1 _) (hY.1 _) hc hva (crossVec_inner_right b v) hturn'
  obtain ⟨U₂, hU₂, hv₂, hmodel₂⟩ := contact_arc_endpoint_halfplane v b (crossVec v a) c
    (hY.1 _) (hY.1 _) hc hvb (crossVec_inner_left v a) hturn
  refine ⟨U₀ ∩ U₁ ∩ U₂, (hU₀.inter hU₁).inter hU₂, ⟨⟨hv₀, hv₁⟩, hv₂⟩, ?_⟩
  intro y hy
  rw [hmodel₀ y hy.1.1]
  change (y ∈ closedShortSphereArc v a ∨ y ∈ closedShortSphereArc b v) ↔ _
  rw [closedShortSphereArc_comm b v, hmodel₁ y hy.1.2, hmodel₂ y hy.2]
  have hflip : inner ℝ (crossVec v b) y = 0 ↔ inner ℝ (crossVec b v) y = 0 := by
    rw [crossVec_swap v b, inner_neg_left]
    simp
  rw [hflip]
  tauto

end SimpleContactCycle
end SquareAntiprismVerification
