import AllS.Units.N_GI.N_exterior_irreducible.N_interior_and_push

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem exterior_irreducible_assemble (H : (Fin 8 → Point) → ℝ) (η cstar : ℝ)
    (hH : ContinuousOn H packingUnitSet) (hc : cstar<1)
    (hboundary : ¬∃Y,Y∈packingUnitSet ∧ H Y=η ∧ packingMaxInner Y≤cstar)
    (hstart : ∃Y,Y∈packingExterior H η ∧ packingMaxInner Y≤cstar) :
    ∃Y,IsConfiguration Y ∧ H Y<η ∧ 0<packingMaxInner Y ∧ packingMaxInner Y≤cstar ∧
      PackingLocalMinimum Y ∧ PackingIrreducible (packingMaxInner Y) Y ∧
      (packingContacts (packingMaxInner Y) Y).Nonempty := by
  obtain ⟨Y,hmin,hp,hb⟩ := exterior_irreducible_contact_count_minimum H η cstar hH hstart
  obtain ⟨hy,hlocal,hirr⟩ := exterior_irreducible_interior_and_push H η cstar hH hboundary Y hmin hp hb
  have hconfig : IsConfiguration Y := packingInnerBound_configuration Y (packingMaxInner Y)
    hmin.1.1.1 (hb.trans_lt hc) ((packingMaxInner_le_iff Y _).mp le_rfl)
  obtain ⟨i,j,hij,he⟩ := packingMaxInner_attained Y
  exact ⟨Y,hconfig,hy,hp,hb,hlocal,hirr,(i,j),(mem_packingContacts _ _ _).mpr ⟨hij,he⟩⟩

#print axioms exterior_irreducible_assemble
end Blueprint.Thomson.Tail.Implementation
