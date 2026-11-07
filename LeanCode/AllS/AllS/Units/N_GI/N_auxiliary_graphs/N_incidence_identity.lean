import AllS.Units.N_GI.N_auxiliary_graphs.N_diagonal_degrees
import AllS.Units.N_GI.N_sphere_euler.N_assemble

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

/-- Double counting triangular corners, with every finite vertex condition explicit. -/
theorem triangle_incidence_balance (degree t : Fin 8 → ℕ)
    (hd : ∀ v, degree v=3 ∨ degree v=4)
    (ht3 : ∀ v, degree v=3 → t v≤1) (ht4 : ∀ v, degree v=4 → t v≤3)
    (hsum : (∑ v, t v) = 3*(Finset.univ.filter (fun v => degree v=4)).card) :
    (∑ v, if degree v=4 then 3-t v else 0) =
      (Finset.univ.filter (fun v => degree v=3 ∧ t v=1)).card := by
  classical
  have hv (v : Fin 8) : t v+(if degree v=4 then 3-t v else 0) =
      (if degree v=4 then 3 else 0) + (if degree v=3 ∧ t v=1 then 1 else 0) := by
    rcases hd v with h | h
    · have ht := ht3 v h
      by_cases ht1 : t v=1
      · simp [h,ht1]
      · have ht0 : t v=0 := by omega
        simp [h,ht0]
    · have ht := ht4 v h
      simp only [h, ↓reduceIte, show ¬ (4:ℕ)=3 by decide, false_and, add_zero]
      omega
  have h := congrArg (fun f : Fin 8 → ℕ => ∑ v, f v) (funext hv)
  have hfour : (∑ v : Fin 8, if degree v=4 then 3 else 0) =
      3*(Finset.univ.filter (fun v => degree v=4)).card := by
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  simp only [Finset.sum_add_distrib, hfour] at h
  rw [hsum] at h
  simpa only [Finset.card_filter] using Nat.add_left_cancel h

theorem auxiliary_graphs_incidence_identity (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    let d := fun v => Fintype.card (ContactNeighbor Y c v)
    let t := faceCornerCount (boundaryArray Y c hY hc 3)
    (∑ v, if d v=4 then 3-t v else 0) =
      (Finset.univ.filter (fun v => d v=3 ∧ t v=1)).card := by
  classical
  let d := fun v => Fintype.card (ContactNeighbor Y c v)
  let t := faceCornerCount (boundaryArray Y c hY hc 3)
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : d v=3 ∨ d v=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [← contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4
    omega
  have ht := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1
  apply triangle_incidence_balance d t hd (fun v => (ht v).1) (fun v => (ht v).2)
  have heuler := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hc4 : (Finset.univ.filter (fun v : Fin 8 => d v=4)).card =
      8-(degreeThreeVertices Y c).card := by
    have hv (v : Fin 8) : (if d v=4 then 1 else 0)+(if d v=3 then 1 else 0) = (1:ℕ) := by
      rcases hd v with h | h <;> simp [h]
    have h := congrArg (fun f : Fin 8 → ℕ => ∑ v, f v) (funext hv)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one] at h
    simp only [Finset.card_filter,degreeThreeVertices]
    change (∑ v : Fin 8, if d v=4 then 1 else 0) =
      8-(∑ v : Fin 8, if d v=3 then 1 else 0)
    omega
  rw [hc4,← heuler.2.2.1]
  have h := sum_faceCornerCount (boundaryArray Y c hY hc 3)
  exact_mod_cast h

#print axioms triangle_incidence_balance
#print axioms auxiliary_graphs_incidence_identity
end Blueprint.Thomson.Tail.Implementation
