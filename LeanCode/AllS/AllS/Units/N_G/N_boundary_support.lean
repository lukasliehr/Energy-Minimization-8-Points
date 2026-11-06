import AllS.Units.N_GI.N_boundary_support.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail

theorem boundary_support {Y : Fin 8 → Point} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) : C.StrictSupport :=
  Implementation.boundary_support_assemble C hcupper hbound hirr

#print axioms boundary_support
end Blueprint.Thomson.Tail
