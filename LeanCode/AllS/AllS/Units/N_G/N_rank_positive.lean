import AllS.Units.N_GI.N_rank_positive.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail

lemma rank_positive (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖ = 1) :
    0 < packingMaxInner Y :=
  Implementation.rank_positive_assemble Y hY

end Blueprint.Thomson.Tail
