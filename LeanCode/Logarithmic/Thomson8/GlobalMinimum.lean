import Thomson8.RealIdentity
import Thomson8.EnergySums
import Thomson8.MomentPositivity
import Thomson8.SOSPositivity
import Thomson8.Candidate
import Thomson8.Positive.F0
import Thomson8.Positive.F1
import Thomson8.Positive.F2
import Thomson8.Positive.F4
import Thomson8.Positive.F5
import Thomson8.Positive.S6_trivial
import Thomson8.Positive.S7_even

namespace Thomson8

open scoped InnerProductSpace

theorem certificate_lower_bound (x : Configuration) (hx : ∀ i, ‖x i‖=1) :
    optimalEnergy ≤ hermiteEnergy x := by
  have h0 := Block.moment_total_nonneg Data.F0 (by rfl) Positive.F0_positive.posSemidef x hx
  have h1 := Block.moment_total_nonneg Data.F1 (by rfl) Positive.F1_positive.posSemidef x hx
  have h2 := Block.moment_total_nonneg Data.F2 (by rfl) Positive.F2_positive.posSemidef x hx
  have h4 := Block.moment_total_nonneg Data.F4 (by rfl) Positive.F4_positive.posSemidef x hx
  have h5 := Block.moment_total_nonneg Data.F5 (by rfl) Positive.F5_positive.posSemidef x hx
  have hW : 0 ≤ distinctSum (onTriples x Data.S6_trivial.value) := by
    apply distinctSum_nonneg
    intro i j k
    exact Block.sos_value_nonneg Data.S6_trivial (by rfl) Positive.S6_trivial_positive.posSemidef _ _ _
      (inner_unit_bounds _ _ (hx i) (hx j)) (inner_unit_bounds _ _ (hx i) (hx k))
      (inner_unit_bounds _ _ (hx j) (hx k))
  have hV : 0 ≤ distinctSum (onTriples x Data.S7_even.value) := by
    apply distinctSum_nonneg
    intro i j k
    exact Block.sos_value_nonneg Data.S7_even (by rfl) Positive.S7_even_positive.posSemidef _ _ _
      (inner_unit_bounds _ _ (hx i) (hx j)) (inner_unit_bounds _ _ (hx i) (hx k))
      (inner_unit_bounds _ _ (hx j) (hx k))
  have heq : onTriples x (fun u v t => (H u+H v+H t)/3-optimalEnergy/28) =
      fun i j k => onTriples x Data.F0.value i j k+onTriples x Data.F1.value i j k+
        onTriples x Data.F2.value i j k+onTriples x Data.F4.value i j k+
        onTriples x Data.F5.value i j k+onTriples x Data.S6_trivial.value i j k+
        onTriples x Data.S7_even.value i j k := by
    funext i j k
    exact real_certificate_identity _ _ _
  have hsum := distinctSum_energy x optimalEnergy
  rw [heq,distinctSum_add,distinctSum_add,distinctSum_add,distinctSum_add,distinctSum_add,
    distinctSum_add] at hsum
  linarith

theorem global_minimum (x : Configuration) (hx : Admissible x) : optimalEnergy ≤ logEnergy x :=
  (certificate_lower_bound x hx.1).trans (hermiteEnergy_le_logEnergy x hx)

theorem antiprism_is_global_minimizer (x : Configuration) (hx : Admissible x) :
    logEnergy antiprism ≤ logEnergy x := by
  rw [antiprism_energy]
  exact global_minimum x hx

#print axioms global_minimum
#print axioms antiprism_is_global_minimizer

end Thomson8
