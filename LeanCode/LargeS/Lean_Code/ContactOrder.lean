import Lean_Code.CircleOrder
import Lean_Code.TangentCircle
import Lean_Code.ContactSeparation

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The actual contact neighbors, enumerated in increasing tangent phase. -/
structure ContactOrderData (Y : Fin 8 → ℝ³) (c : ℝ) (i : Fin 8) where
  size : ℕ
  label : Fin (size + 1) → Fin 8
  contact : ∀ k, label k ≠ i ∧ inner ℝ (Y i) (Y (label k)) = c
  increasing : StrictMono (fun k => contactPhase (Y i) (Y (label k)))
  covers : ∀ j, j ≠ i → inner ℝ (Y i) (Y j) = c → ∃ k, label k = j

theorem contact_order_exists (Y : Fin 8 → ℝ³) (c : ℝ) (i : Fin 8)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    Nonempty (ContactOrderData Y c i) := by
  classical
  let V := contactNeighborsWithin Y c Finset.univ i
  let phase := fun j => contactPhase (Y i) (Y j)
  let T := V.image phase
  have hTne : T.Nonempty := by
    obtain ⟨j, hji, hij⟩ := hne
    exact ⟨phase j, Finset.mem_image.mpr ⟨j, by simp [V, hji, hij], rfl⟩⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hTne)
  let θ : Fin (n + 1) ↪o ℝ := T.orderEmbOfFin hn
  have hchoose : ∀ k, ∃ j, j ∈ V ∧ phase j = θ k := by
    intro k
    exact Finset.mem_image.mp (T.orderEmbOfFin_mem hn k)
  choose label hmem hphase using hchoose
  have hcontact : ∀ k, label k ≠ i ∧ inner ℝ (Y i) (Y (label k)) = c := by
    intro k
    exact ((mem_contactNeighborsWithin Y c Finset.univ i (label k)).mp (hmem k)).2
  refine ⟨⟨n, label, hcontact, ?_, ?_⟩⟩
  · change StrictMono (fun k => phase (label k))
    simpa only [hphase] using θ.strictMono
  · intro j hji hij
    have hjV : j ∈ V := by simp [V, hji, hij]
    have hjT : phase j ∈ T := Finset.mem_image.mpr ⟨j, hjV, rfl⟩
    have hjrange : phase j ∈ Set.range θ := by
      rw [show Set.range θ = (T : Set ℝ) from T.range_orderEmbOfFin hn]
      exact hjT
    obtain ⟨k, hk⟩ := hjrange
    refine ⟨k, hY.2 ?_⟩
    apply contactPhase_injective (Y i) (Y (label k)) (Y j) c
      (hY.1 i) (hY.1 (label k)) (hY.1 j) hc (hcontact k).2 hij
    exact (hphase k).trans hk

namespace ContactOrderData

variable {Y : Fin 8 → ℝ³} {c : ℝ} {i : Fin 8}

def phase (D : ContactOrderData Y c i) (k : Fin (D.size + 1)) : ℝ :=
  contactPhase (Y i) (Y (D.label k))

def gap (D : ContactOrderData Y c i) (k : Fin (D.size + 1)) : ℝ := circleGap D.phase k

lemma label_injective (D : ContactOrderData Y c i) : Function.Injective D.label := by
  intro j k hjk
  apply D.increasing.injective
  simp only [hjk]

lemma neighbor_card (D : ContactOrderData Y c i) :
    (contactNeighborsWithin Y c Finset.univ i).card = D.size + 1 := by
  classical
  have hrange : Finset.univ.image D.label = contactNeighborsWithin Y c Finset.univ i := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_contactNeighborsWithin]
    constructor
    · rintro ⟨k, rfl⟩
      exact D.contact k
    · rintro ⟨hji, hij⟩
      exact D.covers j hji hij
  rw [← hrange, Finset.card_image_of_injective _ D.label_injective,
    Finset.card_univ, Fintype.card_fin]

def labelEquiv (D : ContactOrderData Y c i) :
    Fin (D.size + 1) ≃ {j : Fin 8 // j ≠ i ∧ inner ℝ (Y i) (Y j) = c} :=
  Equiv.ofBijective (fun k => ⟨D.label k, D.contact k⟩) ⟨
    fun j k h => D.label_injective (congrArg Subtype.val h),
    fun j => by
      obtain ⟨k, hk⟩ := D.covers j j.property.1 j.property.2
      exact ⟨k, Subtype.ext hk⟩⟩

@[simp] lemma labelEquiv_val (D : ContactOrderData Y c i) (k : Fin (D.size + 1)) :
    (D.labelEquiv k).val = D.label k := rfl

def successor (D : ContactOrderData Y c i) :
    Equiv.Perm {j : Fin 8 // j ≠ i ∧ inner ℝ (Y i) (Y j) = c} :=
  (D.labelEquiv.symm.trans (Equiv.addRight 1)).trans D.labelEquiv

@[simp] lemma successor_label (D : ContactOrderData Y c i) (k : Fin (D.size + 1)) :
    D.successor (D.labelEquiv k) = D.labelEquiv (k + 1) := by
  simp [successor]

lemma phase_range (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (k : Fin (D.size + 1)) :
    D.phase k ∈ Set.Ioc (-Real.pi) Real.pi :=
  contactPhase_range (Y i) (Y (D.label k)) c (hY i) (hY (D.label k)) hc (D.contact k).2

lemma gap_pos (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (k : Fin (D.size + 1)) : 0 < D.gap k :=
  circleGap_pos D.phase D.increasing (D.phase_range hY hc) k

lemma gap_sum (D : ContactOrderData Y c i) : ∑ k, D.gap k = 2 * Real.pi :=
  circleGap_sum D.phase

theorem gap_lt_pi (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (k : Fin (D.size + 1)) : D.gap k < Real.pi := by
  by_contra h
  obtain ⟨t, ht⟩ := large_circleGap_semicircle D.phase D.increasing
    (D.phase_range hY hc) k (le_of_not_gt h)
  apply hirr i ⟨D.label 0, D.contact 0⟩
  refine ⟨tangentAtPhase (Y i) t, tangentAtPhase_unit _ _, tangentAtPhase_perp _ _ (hY i), ?_⟩
  intro j hji hij
  obtain ⟨l, rfl⟩ := D.covers j hji hij
  rw [tangent_contact_inner (Y i) (Y (D.label l)) _ c (hY i) (hY (D.label l))
    hc hij (tangentAtPhase_perp _ _ (hY i))]
  apply mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
  rw [tangentAtPhase_inner (Y i) _ t (hY i)
    (contact_sphereTangent_unit _ _ c (hY i) (hY (D.label l)) hc hij)
    (sphereTangent_perp _ _ (hY i))]
  exact ht l

theorem gap_eq_contactAngle (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (k : Fin (D.size + 1)) :
    D.gap k = contactAngle c (Y (D.label k)) (Y (D.label (k + 1))) := by
  rw [contactPhase_angle (Y i) _ _ c (hY i) (hY _) (hY _) hc
    (D.contact k).2 (D.contact (k + 1)).2]
  change circleGap D.phase k = Real.arccos (Real.cos (D.phase k - D.phase (k + 1)))
  rw [← circleGap_cos]
  exact (Real.arccos_cos (D.gap_pos hY hc k).le (D.gap_lt_pi hY hc hirr k).le).symm

theorem adjacent_triple_pos (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (k : Fin (D.size + 1)) :
    0 < inner ℝ (crossVec (Y (D.label k)) (Y (D.label (k + 1)))) (Y i) := by
  rw [contactPhase_triple (Y i) _ _ c (hY i) (hY _) (hY _) hc
    (D.contact k).2 (D.contact (k + 1)).2]
  have hsin : Real.sin (D.phase (k + 1) - D.phase k) = Real.sin (D.gap k) :=
    (circleGap_sin D.phase k).symm
  change 0 < ‖crossVec (Y i) (Y (D.label k))‖ *
    ‖crossVec (Y i) (Y (D.label (k + 1)))‖ * Real.sin (D.phase (k + 1) - D.phase k)
  rw [hsin]
  exact mul_pos
    (mul_pos (contact_cross_norm_pos _ _ c (hY i) (hY _) hc (D.contact k).2)
      (contact_cross_norm_pos _ _ c (hY i) (hY _) hc (D.contact (k + 1)).2))
    (Real.sin_pos_of_pos_of_lt_pi (D.gap_pos hY hc k) (D.gap_lt_pi hY hc hirr k))

theorem successor_triple_pos (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (j : {j : Fin 8 // j ≠ i ∧ inner ℝ (Y i) (Y j) = c}) :
    0 < inner ℝ (crossVec (Y j) (Y (D.successor j))) (Y i) := by
  obtain ⟨k, rfl⟩ := D.labelEquiv.surjective j
  simpa only [D.successor_label, D.labelEquiv_val] using D.adjacent_triple_pos hY hc hirr k

lemma adjacent_labels_ne (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (k : Fin (D.size + 1)) : D.label k ≠ D.label (k + 1) := by
  intro heq
  have hphase : D.phase k = D.phase (k + 1) := by simp only [phase, heq]
  have hpos := D.gap_pos hY hc k
  have hlt := D.gap_lt_pi hY hc hirr k
  simp only [gap, circleGap, ← hphase, sub_self, zero_add] at hpos hlt
  split_ifs at hpos hlt <;> linarith [Real.pi_pos]

theorem gap_lower_bound (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (k : Fin (D.size + 1)) :
    Real.arccos (c / (1 + c)) ≤ D.gap k := by
  rw [D.gap_eq_contactAngle hY hc hirr k]
  exact contact_angle_lower_bound (Y i) _ _ c (hY i) (hY _) (hY _) hc
    (D.contact k).2 (D.contact (k + 1)).2
    (hbound _ _ (D.adjacent_labels_ne hY hc hirr k))

theorem degree_le_four (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : 0 < c) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) :
    (contactNeighborsWithin Y c Finset.univ i).card ≤ 4 := by
  rw [D.neighbor_card]
  exact angle_sum_at_most_four (D.size + 1) (Real.arccos (c / (1 + c)))
    (packing_equilateral_angle_range c hc hcupper).1 D.gap
    (D.gap_lower_bound hY ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩ hirr hbound)
    D.gap_sum

end ContactOrderData

theorem irreducible_contact_degree_le_four (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0 < c) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y) (i : Fin 8) :
    (contactNeighborsWithin Y c Finset.univ i).card ≤ 4 := by
  classical
  by_cases hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c
  · obtain ⟨D⟩ := contact_order_exists Y c i hY ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩ hne
    exact D.degree_le_four hY.1 hc hcupper hirr hbound
  · have hempty : contactNeighborsWithin Y c Finset.univ i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact hne ⟨j, ((mem_contactNeighborsWithin Y c Finset.univ i j).mp hj).2⟩
    rw [hempty, Finset.card_empty]
    omega

end SquareAntiprismVerification
