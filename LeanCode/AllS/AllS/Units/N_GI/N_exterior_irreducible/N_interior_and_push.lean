import AllS.Units.N_GI.N_exterior_irreducible.N_contact_count_minimum

noncomputable section
open SquareAntiprismVerification
open Filter
open scoped Topology
namespace Blueprint.Thomson.Tail.Implementation

theorem exterior_sublevel_neighborhood (H : (Fin 8 → Point) → ℝ) (η : ℝ)
    (hH : ContinuousOn H packingUnitSet) (Y : Fin 8 → Point) (hYu : Y∈packingUnitSet) (hY : H Y<η) :
    ∃ε>0,∀Z,Z∈packingUnitSet → dist Z Y<ε → H Z<η := by
  have he : ∀ᶠZ in 𝓝[packingUnitSet] Y,H Z<η :=
    (hH.continuousWithinAt hYu).eventually (gt_mem_nhds hY)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  exact ⟨ε,hε,fun Z hZu hdist=>hball ⟨hdist,hZu⟩⟩

theorem exterior_minimizer_local (H : (Fin 8 → Point) → ℝ) (η : ℝ)
    (hH : ContinuousOn H packingUnitSet) (Y : Fin 8 → Point)
    (hmin : ExteriorMinimizer H η Y) (hY : H Y<η) : PackingLocalMinimum Y := by
  have he : ∀ᶠZ in 𝓝[packingUnitSet] Y,H Z<η :=
    (hH.continuousWithinAt hmin.1.1).eventually (gt_mem_nhds hY)
  change ∀ᶠZ in 𝓝[packingUnitSet] Y,packingMaxInner Y≤packingMaxInner Z
  filter_upwards [he,self_mem_nhdsWithin] with Z hZ hZu
  exact hmin.2 ⟨hZu,hZ.le⟩

theorem exterior_irreducible_interior_and_push (H : (Fin 8 → Point) → ℝ) (η cstar : ℝ)
    (hH : ContinuousOn H packingUnitSet)
    (hboundary : ¬∃Y,Y∈packingUnitSet ∧ H Y=η ∧ packingMaxInner Y≤cstar)
    (Y : Fin 8 → Point) (hmin : ExteriorCountMinimum H η Y) (hp : 0<packingMaxInner Y)
    (hb : packingMaxInner Y≤cstar) :
    H Y<η ∧ PackingLocalMinimum Y ∧ PackingIrreducible (packingMaxInner Y) Y := by
  have hY : H Y<η := lt_of_le_of_ne hmin.1.1.2 (by
    intro heq
    exact hboundary ⟨Y,hmin.1.1.1,heq,hb⟩)
  refine ⟨hY,exterior_minimizer_local H η hH Y hmin.1 hY,?_⟩
  obtain ⟨ε,hε,hball⟩ := exterior_sublevel_neighborhood H η hH Y hmin.1.1.1 hY
  intro i hneighbor hpush
  obtain ⟨v,hv,horth,hcontact⟩ := hpush
  obtain ⟨Z,hZu,hZb,hZd,hZcontact⟩ := push Y i (packingMaxInner Y) hmin.1.1.1 hp
    ((packingMaxInner_le_iff Y _).mp le_rfl) hneighbor v hv horth hcontact ε hε
  have hZe : Z∈packingExterior H η := ⟨hZu,(hball Z hZu hZd).le⟩
  have he : packingMaxInner Z=packingMaxInner Y :=
    le_antisymm ((packingMaxInner_le_iff Z _).mpr hZb) (hmin.1.2 hZe)
  have hZm : ExteriorMinimizer H η Z := ⟨hZe,fun W hW=>by rw [he];exact hmin.1.2 hW⟩
  have hcard := hmin.2 Z hZm
  rw [he] at hcard
  have hstrict := Finset.card_lt_card hZcontact
  exact (not_lt_of_ge hcard) hstrict

#print axioms exterior_irreducible_interior_and_push
end Blueprint.Thomson.Tail.Implementation
