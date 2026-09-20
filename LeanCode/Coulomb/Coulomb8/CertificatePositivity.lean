import Coulomb8.CertificateColumnsData
import Coulomb8.MomentPositivity
import Coulomb8.SOSPositivity
import Coulomb8.EnergySums
import Coulomb8.PSDBounds.F0
import Coulomb8.PSDBounds.F1
import Coulomb8.PSDBounds.F2
import Coulomb8.PSDBounds.F3
import Coulomb8.PSDBounds.F4
import Coulomb8.PSDBounds.F5
import Coulomb8.PSDBounds.S6_trivial
import Coulomb8.PSDBounds.S7_even
import Coulomb8.PSDBounds.S7_odd

namespace Coulomb8
open scoped InnerProductSpace
open Thomson8 (distinctSum onTriples distinctSum_add distinctSum_nonneg inner_unit_bounds)

theorem certificateValue_total_nonneg (w : Fin 192 → ℝ)
    (hw : ∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ))
    (x : Configuration) (hx : ∀ i, ‖x i‖=1) :
    0 ≤ distinctSum (onTriples x (certificateValue w)) := by
  have h0 := Block.moment_total_nonneg Data.F0 w (by rfl)
    (PSDBounds.F0.positive w hw).posSemidef x hx
  have h1 := Block.moment_total_nonneg Data.F1 w (by rfl)
    (PSDBounds.F1.positive w hw).posSemidef x hx
  have h2 := Block.moment_total_nonneg Data.F2 w (by rfl)
    (PSDBounds.F2.positive w hw).posSemidef x hx
  have h3 := Block.moment_total_nonneg Data.F3 w (by rfl)
    (PSDBounds.F3.positive w hw).posSemidef x hx
  have h4 := Block.moment_total_nonneg Data.F4 w (by rfl)
    (PSDBounds.F4.positive w hw).posSemidef x hx
  have h5 := Block.moment_total_nonneg Data.F5 w (by rfl)
    (PSDBounds.F5.positive w hw).posSemidef x hx
  have h6 : 0 ≤ distinctSum (onTriples x (Data.S6_trivial.value w)) := by
    apply distinctSum_nonneg
    intro i j k
    exact Block.sos_value_nonneg Data.S6_trivial w (by rfl)
      (PSDBounds.S6_trivial.positive w hw).posSemidef _ _ _
      (inner_unit_bounds _ _ (hx i) (hx j)) (inner_unit_bounds _ _ (hx i) (hx k))
      (inner_unit_bounds _ _ (hx j) (hx k))
  have h7 : 0 ≤ distinctSum (onTriples x (Data.S7_even.value w)) := by
    apply distinctSum_nonneg
    intro i j k
    exact Block.sos_value_nonneg Data.S7_even w (by rfl)
      (PSDBounds.S7_even.positive w hw).posSemidef _ _ _
      (inner_unit_bounds _ _ (hx i) (hx j)) (inner_unit_bounds _ _ (hx i) (hx k))
      (inner_unit_bounds _ _ (hx j) (hx k))
  have h8 : 0 ≤ distinctSum (onTriples x (Data.S7_odd.value w)) := by
    apply distinctSum_nonneg
    intro i j k
    exact Block.sos_value_nonneg Data.S7_odd w (by rfl)
      (PSDBounds.S7_odd.positive w hw).posSemidef _ _ _
      (inner_unit_bounds _ _ (hx i) (hx j)) (inner_unit_bounds _ _ (hx i) (hx k))
      (inner_unit_bounds _ _ (hx j) (hx k))
  unfold certificateValue onTriples
  simp only [distinctSum_add]
  have hz : distinctSum (fun _ _ _ => (0 : ℝ))=0 := by simp [Thomson8.distinctSum]
  rw [hz]
  exact add_nonneg h0 (add_nonneg h1 (add_nonneg h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5 (add_nonneg h6 (add_nonneg h7 (add_nonneg h8 (le_rfl)))))))))

end Coulomb8

#print axioms Coulomb8.certificateValue_total_nonneg
