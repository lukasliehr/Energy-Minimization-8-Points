import AllS.Units.N_G.N_rank_positive
import AllS.Units.N_G.N_push
import AllS.Units.N_GI.N_cube_endgame.N_local_descent

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def packingUnitSet : Set (Fin 8 → Point) := {Y | ∀i,‖Y i‖=1}
def packingExterior (H : (Fin 8 → Point) → ℝ) (η : ℝ) : Set (Fin 8 → Point) :=
  {Y | Y∈packingUnitSet ∧ H Y≤η}
def ExteriorMinimizer (H : (Fin 8 → Point) → ℝ) (η : ℝ) (Y : Fin 8 → Point) : Prop :=
  Y∈packingExterior H η ∧ IsMinOn packingMaxInner (packingExterior H η) Y

theorem packingUnitSet_compact : IsCompact packingUnitSet := by
  simpa [packingUnitSet,Set.pi,Metric.mem_sphere,dist_zero_right] using
    (isCompact_univ_pi (fun _ : Fin 8=>isCompact_sphere (0:Point) 1))

theorem packingExterior_compact (H : (Fin 8 → Point) → ℝ) (η : ℝ)
    (hH : ContinuousOn H packingUnitSet) : IsCompact (packingExterior H η) := by
  exact hH.lowerSemicontinuousOn.isCompact_inter_preimage_Iic packingUnitSet_compact η

theorem exterior_irreducible_compact_minimum (H : (Fin 8 → Point) → ℝ) (η cstar : ℝ)
    (hH : ContinuousOn H packingUnitSet)
    (hstart : ∃Y,Y∈packingExterior H η ∧ packingMaxInner Y≤cstar) :
    ∃Y,ExteriorMinimizer H η Y ∧ 0<packingMaxInner Y ∧ packingMaxInner Y≤cstar := by
  obtain ⟨Z,hZ,hZb⟩ := hstart
  obtain ⟨Y,hY,hmin⟩ := (packingExterior_compact H η hH).exists_isMinOn ⟨Z,hZ⟩
    packingMaxInner_continuous.continuousOn
  exact ⟨Y,⟨hY,hmin⟩,rank_positive Y hY.1,(hmin hZ).trans hZb⟩

#print axioms exterior_irreducible_compact_minimum
end Blueprint.Thomson.Tail.Implementation
