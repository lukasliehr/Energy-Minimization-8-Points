import AllS.Units.N_GI.N_tiling_data.N_partition_by_length

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem tiling_data_counts (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    Fintype.card (BoundaryOfLength Y c hY hc 3) + Fintype.card (BoundaryOfLength Y c hY hc 4) =
      Fintype.card (ContactBoundaryOrbit Y c hY hc) ∧
    3 * Fintype.card (BoundaryOfLength Y c hY hc 3) + 4 * Fintype.card (BoundaryOfLength Y c hY hc 4) =
      Fintype.card (ContactDart Y c) := by
  classical
  constructor
  · simpa using tiling_data_partition_by_length Y c hY hc hcupper hirr hsupport (fun _ => (1 : ℕ))
  · have h := tiling_data_partition_by_length Y c hY hc hcupper hirr hsupport
      (fun f => (boundaryOrbitCycle Y c hY hc f).size + 1)
    have h3 : ∀ f : BoundaryOfLength Y c hY hc 3, (boundaryOrbitCycle Y c hY hc f.val).size + 1 = 3 :=
      fun f => f.property
    have h4 : ∀ f : BoundaryOfLength Y c hY hc 4, (boundaryOrbitCycle Y c hY hc f.val).size + 1 = 4 :=
      fun f => f.property
    simp only [h3, h4, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    simpa only [mul_comm] using h.trans (boundary_cycles_count_darts Y c hY hc)

#print axioms tiling_data_counts

end Blueprint.Thomson.Tail.Implementation
