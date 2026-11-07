import AllS.Units.N_GI.N_rank_positive.N_positive_max

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

lemma rank_positive_assemble (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖ = 1) :
    0 < packingMaxInner Y :=
  rank_positive_positive_max Y hY

end Blueprint.Thomson.Tail.Implementation
