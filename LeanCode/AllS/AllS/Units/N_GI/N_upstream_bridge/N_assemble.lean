import AllS.Units.N_GI.N_upstream_bridge.N_coordinates
import AllS.Units.N_GI.N_upstream_bridge.N_energy
import AllS.Units.N_GI.N_upstream_bridge.N_congruence
import AllS.Units.N_GI.N_upstream_bridge.N_euclidean_coordinates

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem upstream_bridge_assemble (s : ℝ) (hs : 0<s) (Y Z : Fin 8 → Point) :
    E s Y = squaredEnergy (s/2) Y ∧
    E s Y = SquareAntiprismVerification.E s Y ∧
    (Thomson.Congruent Y Z ↔ SquareAntiprismVerification.Congruent Y Z) :=
  ⟨(upstream_bridge_energy s hs Y).1, (upstream_bridge_energy s hs Y).2,
   (upstream_bridge_congruence Y Z).2⟩

end Blueprint.Thomson.Tail.Implementation
