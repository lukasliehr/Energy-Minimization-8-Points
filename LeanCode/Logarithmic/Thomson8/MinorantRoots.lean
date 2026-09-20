import Thomson8.MinorantArithmetic
import Thomson8.ContactOrder

namespace Thomson8

theorem root_between_of_pos_neg (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (ha : 0 < f a) (hb : f b < 0) :
    ∃ r, a < r ∧ r < b ∧ f r=0 := by
  obtain ⟨r,hr0,hr1,hr⟩ := root_between_of_sign_change (fun x => -f x) hab hf.neg
    (by linarith) (by linarith)
  exact ⟨r,hr0,hr1,by linarith⟩

theorem minorantQ_continuous : Continuous minorantQ := by
  unfold minorantQ quartic
  fun_prop

structure MinorantRoots where
  r0 : ℝ
  r1 : ℝ
  r2 : ℝ
  r3 : ℝ
  interval0 : -1 < r0 ∧ r0 < nodeD.eval
  interval1 : nodeD.eval < r1 ∧ r1 < nodeB.eval
  interval2 : nodeB.eval < r2 ∧ r2 < nodeC.eval
  interval3 : nodeC.eval < r3 ∧ r3 < nodeA.eval
  zero0 : minorantQ r0=0
  zero1 : minorantQ r1=0
  zero2 : minorantQ r2=0
  zero3 : minorantQ r3=0

noncomputable def minorantRoots : MinorantRoots := by
  apply Classical.choice
  have hc (s : Set ℝ) : ContinuousOn minorantQ s := minorantQ_continuous.continuousOn
  obtain ⟨r0,h00,h01,h0⟩ := root_between_of_pos_neg minorantQ contact_order.1 (hc _)
    minorantQ_minus_one_pos minorantQ_D_neg
  obtain ⟨r1,h10,h11,h1⟩ := root_between_of_sign_change minorantQ contact_order.2.1 (hc _)
    minorantQ_D_neg minorantQ_B_pos
  obtain ⟨r2,h20,h21,h2⟩ := root_between_of_pos_neg minorantQ contact_order.2.2.1 (hc _)
    minorantQ_B_pos minorantQ_C_neg
  obtain ⟨r3,h30,h31,h3⟩ := root_between_of_sign_change minorantQ contact_order.2.2.2.1 (hc _)
    minorantQ_C_neg minorantQ_A_pos
  exact ⟨⟨r0,r1,r2,r3,⟨h00,h01⟩,⟨h10,h11⟩,⟨h20,h21⟩,⟨h30,h31⟩,h0,h1,h2,h3⟩⟩

theorem MinorantRoots.factor (r : MinorantRoots) (x : ℝ) :
    minorantQ x = qRealCoeff 4*(x-r.r0)*(x-r.r1)*(x-r.r2)*(x-r.r3) := by
  apply quartic_factor
  · exact r.interval0.2.trans r.interval1.1
  · exact r.interval1.2.trans r.interval2.1
  · exact r.interval2.2.trans r.interval3.1
  · exact r.zero0
  · exact r.zero1
  · exact r.zero2
  · exact r.zero3

#print axioms minorantRoots
#print axioms MinorantRoots.factor

end Thomson8
