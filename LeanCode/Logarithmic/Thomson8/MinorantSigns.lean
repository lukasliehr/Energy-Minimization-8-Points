import Thomson8.MinorantCalculus
import Thomson8.MinorantRoots

namespace Thomson8

noncomputable def gapWeight (x : ℝ) : ℝ := (x+1)^4*qRealCoeff 4/(2*(1-x))

theorem gapWeight_pos {x : ℝ} (hx : -1 < x ∧ x < 1) : 0 < gapWeight x := by
  unfold gapWeight
  apply div_pos
  · exact mul_pos (pow_pos (by linarith) 4) minorantQ_leading_pos
  · linarith

theorem gapDerivative_pairs (r : MinorantRoots) (x : ℝ) :
    gapDerivative x = gapWeight x * ((x-r.r0)*(x-nodeD.eval)) *
      ((x-r.r1)*(x-nodeB.eval)) * ((x-r.r2)*(x-nodeC.eval)) *
      ((x-r.r3)*(x-nodeA.eval)) := by
  rw [gapDerivative,r.factor]
  unfold gapWeight
  ring

theorem gap_sign_0 (r : MinorantRoots) {x : ℝ}
    (hx : (-1) < x ∧ x < r.r0) : 0 < gapDerivative x := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_pos (mul_pos (mul_pos (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_1 (r : MinorantRoots) {x : ℝ}
    (hx : r.r0 < x ∧ x < nodeD.eval) : gapDerivative x < 0 := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : (x-r.r0)*(x-nodeD.eval) < 0 := mul_neg_of_pos_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hw h0) h1) h2) h3)

theorem gap_sign_2 (r : MinorantRoots) {x : ℝ}
    (hx : nodeD.eval < x ∧ x < r.r1) : 0 < gapDerivative x := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_pos (mul_pos (mul_pos (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_3 (r : MinorantRoots) {x : ℝ}
    (hx : r.r1 < x ∧ x < nodeB.eval) : gapDerivative x < 0 := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : (x-r.r1)*(x-nodeB.eval) < 0 := mul_neg_of_pos_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_4 (r : MinorantRoots) {x : ℝ}
    (hx : nodeB.eval < x ∧ x < r.r2) : 0 < gapDerivative x := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_pos (mul_pos (mul_pos (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_5 (r : MinorantRoots) {x : ℝ}
    (hx : r.r2 < x ∧ x < nodeC.eval) : gapDerivative x < 0 := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : (x-r.r2)*(x-nodeC.eval) < 0 := mul_neg_of_pos_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_6 (r : MinorantRoots) {x : ℝ}
    (hx : nodeC.eval < x ∧ x < r.r3) : 0 < gapDerivative x := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos_of_neg_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_pos (mul_pos (mul_pos (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_7 (r : MinorantRoots) {x : ℝ}
    (hx : r.r3 < x ∧ x < nodeA.eval) : gapDerivative x < 0 := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : (x-r.r3)*(x-nodeA.eval) < 0 := mul_neg_of_pos_of_neg (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_neg_of_pos_of_neg (mul_pos (mul_pos (mul_pos hw h0) h1) h2) h3)

theorem gap_sign_8 (r : MinorantRoots) {x : ℝ}
    (hx : nodeA.eval < x ∧ x < 1) : 0 < gapDerivative x := by
  have hchain := And.intro hx.1 hx.2
  have hw : 0 < gapWeight x := gapWeight_pos ⟨by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2],by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]⟩
  have h0 : 0 < (x-r.r0)*(x-nodeD.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h1 : 0 < (x-r.r1)*(x-nodeB.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h2 : 0 < (x-r.r2)*(x-nodeC.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  have h3 : 0 < (x-r.r3)*(x-nodeA.eval) := mul_pos (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2]) (by linarith [r.interval0.1, r.interval0.2, r.interval1.1, r.interval1.2, r.interval2.1, r.interval2.2, r.interval3.1, r.interval3.2, contact_order.2.2.2.2])
  rw [gapDerivative_pairs r]
  exact (mul_pos (mul_pos (mul_pos (mul_pos hw h0) h1) h2) h3)

#print axioms gap_sign_8

end Thomson8
