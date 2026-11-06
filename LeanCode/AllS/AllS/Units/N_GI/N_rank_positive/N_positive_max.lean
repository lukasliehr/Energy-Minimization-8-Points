import AllS.Units.N_G.N_setup
import Lean_Code.PackingMaximum

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

lemma rank_positive_positive_max (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖ = 1) :
    0 < packingMaxInner Y :=
  packingMaxInner_pos Y hY

#print axioms rank_positive_positive_max

end Blueprint.Thomson.Tail.Implementation
