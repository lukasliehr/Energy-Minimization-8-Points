import AllS.Units.N_GI.N_upstream_bridge.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail

theorem upstream_bridge (s : ℝ) (hs : 0<s) (Y Z : Fin 8 → Point) :
    E s Y = squaredEnergy (s/2) Y ∧
    E s Y = SquareAntiprismVerification.E s Y ∧
    (Thomson.Congruent Y Z ↔ SquareAntiprismVerification.Congruent Y Z) :=
  Implementation.upstream_bridge_assemble s hs Y Z

end Blueprint.Thomson.Tail
