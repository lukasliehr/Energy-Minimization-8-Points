import AllS.Units.N_GI.N_exterior_irreducible.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem exterior_irreducible (H : (Fin 8 → Point) → ℝ) (η cstar : ℝ)
    (hH : ContinuousOn H packingUnitSet) (hc : cstar<1)
    (hboundary : ¬∃Y,Y∈packingUnitSet ∧ H Y=η ∧ packingMaxInner Y≤cstar)
    (hstart : ∃Y,Y∈packingExterior H η ∧ packingMaxInner Y≤cstar) :
    ∃Y,IsConfiguration Y ∧ H Y<η ∧ 0<packingMaxInner Y ∧ packingMaxInner Y≤cstar ∧
      PackingLocalMinimum Y ∧ PackingIrreducible (packingMaxInner Y) Y ∧
      (packingContacts (packingMaxInner Y) Y).Nonempty := exterior_irreducible_assemble H η cstar hH hc hboundary hstart

#print axioms exterior_irreducible
end Blueprint.Thomson.Tail
