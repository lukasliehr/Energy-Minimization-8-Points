import Thomson8.MinorantSigns
import Thomson8.Bump

namespace Thomson8

theorem gap_A : minorantGap nodeA.eval=0 := by simpa [nodes] using gap_contact ⟨0,by decide⟩
theorem gap_B : minorantGap nodeB.eval=0 := by simpa [nodes] using gap_contact ⟨1,by decide⟩
theorem gap_C : minorantGap nodeC.eval=0 := by simpa [nodes] using gap_contact ⟨2,by decide⟩
theorem gap_D : minorantGap nodeD.eval=0 := by simpa [nodes] using gap_contact ⟨3,by decide⟩

theorem gap_positive_0 {x : ℝ} (hx : -1 < x ∧ x < nodeD.eval) : 0 < minorantGap x := by
  let r := minorantRoots
  have hb : nodeD.eval < 1 := by linarith [contact_order]
  exact positive_bump r.interval0.1 r.interval0.2 (gap_continuousOn hb _)
    (fun y hy => hasDerivAt_gap (hy.2.trans hb))
    (fun y hy => gap_sign_0 r hy) (fun y hy => gap_sign_1 r hy)
    gap_minus_one gap_D hx

theorem gap_positive_1 {x : ℝ} (hx : nodeD.eval < x ∧ x < nodeB.eval) : 0 < minorantGap x := by
  let r := minorantRoots
  have hb : nodeB.eval < 1 := by linarith [contact_order]
  exact positive_bump r.interval1.1 r.interval1.2 (gap_continuousOn hb _)
    (fun y hy => hasDerivAt_gap (hy.2.trans hb))
    (fun y hy => gap_sign_2 r hy) (fun y hy => gap_sign_3 r hy)
    gap_D gap_B hx

theorem gap_positive_2 {x : ℝ} (hx : nodeB.eval < x ∧ x < nodeC.eval) : 0 < minorantGap x := by
  let r := minorantRoots
  have hb : nodeC.eval < 1 := by linarith [contact_order]
  exact positive_bump r.interval2.1 r.interval2.2 (gap_continuousOn hb _)
    (fun y hy => hasDerivAt_gap (hy.2.trans hb))
    (fun y hy => gap_sign_4 r hy) (fun y hy => gap_sign_5 r hy)
    gap_B gap_C hx

theorem gap_positive_3 {x : ℝ} (hx : nodeC.eval < x ∧ x < nodeA.eval) : 0 < minorantGap x := by
  let r := minorantRoots
  have hb : nodeA.eval < 1 := contact_order.2.2.2.2
  exact positive_bump r.interval3.1 r.interval3.2 (gap_continuousOn hb _)
    (fun y hy => hasDerivAt_gap (hy.2.trans hb))
    (fun y hy => gap_sign_6 r hy) (fun y hy => gap_sign_7 r hy)
    gap_C gap_A hx

theorem gap_positive_4 {x : ℝ} (hx : nodeA.eval < x ∧ x < 1) : 0 < minorantGap x := by
  have hm : StrictMonoOn minorantGap (Set.Icc nodeA.eval x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (gap_continuousOn hx.2 _)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_gap (hy.2.trans hx.2)).deriv]
    exact gap_sign_8 minorantRoots ⟨hy.1,hy.2.trans hx.2⟩
  simpa only [gap_A] using hm ⟨le_rfl,hx.1.le⟩ ⟨hx.1.le,le_rfl⟩ hx.1

theorem gap_positive {x : ℝ} (hx : -1 < x ∧ x < 1)
    (hne : x ≠ nodeA.eval ∧ x ≠ nodeB.eval ∧ x ≠ nodeC.eval ∧ x ≠ nodeD.eval) :
    0 < minorantGap x := by
  rcases lt_or_gt_of_ne hne.2.2.2 with hD | hD
  · exact gap_positive_0 ⟨hx.1,hD⟩
  rcases lt_or_gt_of_ne hne.2.1 with hB | hB
  · exact gap_positive_1 ⟨hD,hB⟩
  rcases lt_or_gt_of_ne hne.2.2.1 with hC | hC
  · exact gap_positive_2 ⟨hB,hC⟩
  rcases lt_or_gt_of_ne hne.1 with hA | hA
  · exact gap_positive_3 ⟨hC,hA⟩
  exact gap_positive_4 ⟨hA,hx.2⟩

theorem H_strict_minorant {x : ℝ} (hx : -1 < x ∧ x < 1)
    (hne : x ≠ nodeA.eval ∧ x ≠ nodeB.eval ∧ x ≠ nodeC.eval ∧ x ≠ nodeD.eval) :
    H x < phi x := sub_pos.mp (gap_positive hx hne)

theorem H_minorant {x : ℝ} (hx : -1 ≤ x ∧ x < 1) : H x ≤ phi x := by
  by_cases hm : x = -1
  · rw [hm,H_minus_one]
  by_cases hA : x=nodeA.eval
  · have h := gap_A; rw [minorantGap] at h; rw [hA]; linarith
  by_cases hB : x=nodeB.eval
  · have h := gap_B; rw [minorantGap] at h; rw [hB]; linarith
  by_cases hC : x=nodeC.eval
  · have h := gap_C; rw [minorantGap] at h; rw [hC]; linarith
  by_cases hD : x=nodeD.eval
  · have h := gap_D; rw [minorantGap] at h; rw [hD]; linarith
  exact (H_strict_minorant ⟨lt_of_le_of_ne hx.1 (Ne.symm hm),hx.2⟩ ⟨hA,hB,hC,hD⟩).le

theorem H_minorant_equality {x : ℝ} (hx : -1 ≤ x ∧ x < 1) :
    H x = phi x ↔ x = -1 ∨ x=nodeA.eval ∨ x=nodeB.eval ∨ x=nodeC.eval ∨ x=nodeD.eval := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hs := H_strict_minorant ⟨lt_of_le_of_ne hx.1 (Ne.symm hn.1),hx.2⟩ hn.2
    linarith
  · rintro (rfl|rfl|rfl|rfl|rfl)
    · exact H_minus_one
    all_goals
      apply Eq.symm
      apply sub_eq_zero.mp
      first | exact gap_A | exact gap_B | exact gap_C | exact gap_D

#print axioms H_minorant
#print axioms H_minorant_equality

end Thomson8
