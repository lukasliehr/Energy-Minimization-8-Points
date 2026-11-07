import AllS.Units.N_GI.N_cube_k2.N_all_quads_contain_u

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem fin4_distinct_positions (i j : Fin 4) (h : i≠j) : j=i+1 ∨ j=i+2 ∨ j=i+3 := by
  fin_cases i <;> fin_cases j <;> simp_all

theorem quadFace_oriented_pair_unique {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : QuadFace Y c hY hc) (u v : Fin 8)
    (hf : ∃ i, quadFaceVertex f i=u ∧ quadFaceVertex f (i+1)=v)
    (hg : ∃ j, quadFaceVertex g j=u ∧ quadFaceVertex g (j+1)=v) : f=g := by
  obtain ⟨i,hi,hii⟩ := hf
  obtain ⟨j,hj,hjj⟩ := hg
  have hd : quadFaceDart f i=quadFaceDart g j := by
    apply actual_contactDart_ext
    · exact hi.trans hj.symm
    · exact (quadFaceDart_tip f i).trans (hii.trans (hjj.symm.trans (quadFaceDart_tip g j).symm))
  apply Subtype.ext
  exact (quadFaceDart_class f i).symm.trans
    ((congrArg (Quotient.mk (permutationOrbitSetoid (contactFaceNext Y c hY hc))) hd).trans
      (quadFaceDart_class g j))

theorem quadFace_contains_contact_pair {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (u v : Fin 8) (huv : u≠v) (hcontact : inner ℝ (Y u) (Y v)=c)
    (hu : ∃ i, quadFaceVertex f i=u) (hv : ∃ j, quadFaceVertex f j=v) :
    (∃ i, quadFaceVertex f i=u ∧ quadFaceVertex f (i+1)=v) ∨
    (∃ i, quadFaceVertex f i=v ∧ quadFaceVertex f (i+1)=u) := by
  obtain ⟨i,hi⟩ := hu
  obtain ⟨j,hj⟩ := hv
  have hij : i≠j := fun h => huv (hi.symm.trans ((congrArg (quadFaceVertex f) h).trans hj))
  rcases fin4_distinct_positions i j hij with h | h | h
  · exact Or.inl ⟨i,hi,(congrArg (quadFaceVertex f) h.symm).trans hj⟩
  · have hl := auxiliary_graphs_diagonal_noncontact f hirr hbound hsupport i
    have h0 : inner ℝ (Y (quadFaceVertex f i)) (Y (quadFaceVertex f (i+2)))=c :=
      (congrArg₂ (fun x y => inner ℝ (Y x) (Y y)) hi
        ((congrArg (quadFaceVertex f) h.symm).trans hj)).trans hcontact
    linarith
  · right
    refine ⟨j,hj,?_⟩
    have hh : j+1=i := by rw [h]; fin_cases i <;> decide
    exact (congrArg (quadFaceVertex f) hh).trans hi

theorem quadFace_contains_noncontact_pair {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc)
    (u v : Fin 8) (huv : u≠v) (hcontact : inner ℝ (Y u) (Y v)≠c)
    (hu : ∃ i, quadFaceVertex f i=u) (hv : ∃ j, quadFaceVertex f j=v) :
    ∃ i, quadFaceVertex f i=u ∧ quadFaceVertex f (i+2)=v := by
  obtain ⟨i,hi⟩ := hu
  obtain ⟨j,hj⟩ := hv
  have hij : i≠j := fun h => huv (hi.symm.trans ((congrArg (quadFaceVertex f) h).trans hj))
  rcases fin4_distinct_positions i j hij with h | h | h
  · have hh := quadFaceVertex_side f i
    have ht : inner ℝ (Y u) (Y v)=c :=
      (congrArg₂ (fun x y => inner ℝ (Y x) (Y y)) hi
        ((congrArg (quadFaceVertex f) h.symm).trans hj)).symm.trans hh
    exact (hcontact ht).elim
  · exact ⟨i,hi,(congrArg (quadFaceVertex f) h.symm).trans hj⟩
  · have hji : j+1=i := by rw [h]; fin_cases i <;> decide
    have hh := quadFaceVertex_side f j
    have ht : inner ℝ (Y v) (Y u)=c :=
      (congrArg₂ (fun x y => inner ℝ (Y x) (Y y)) hj
        ((congrArg (quadFaceVertex f) hji).trans hi)).symm.trans hh
    exact (hcontact ((real_inner_comm _ _).trans ht)).elim

theorem quadFace_three_common_pair_impossible {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (F : Fin 3 → QuadFace Y c hY hc) (hinj : Function.Injective F) (u v : Fin 8) (huv : u≠v)
    (hu : ∀ k, ∃ i, quadFaceVertex (F k) i=u) (hv : ∀ k, ∃ i, quadFaceVertex (F k) i=v) : False := by
  have h01 : F 0≠F 1 := fun h => (by decide : (0:Fin 3)≠1) (hinj h)
  have h02 : F 0≠F 2 := fun h => (by decide : (0:Fin 3)≠2) (hinj h)
  have h12 : F 1≠F 2 := fun h => (by decide : (1:Fin 3)≠2) (hinj h)
  by_cases hcontact : inner ℝ (Y u) (Y v)=c
  · have ha := quadFace_contains_contact_pair (F 0) hirr hbound hsupport u v huv hcontact (hu 0) (hv 0)
    have hb := quadFace_contains_contact_pair (F 1) hirr hbound hsupport u v huv hcontact (hu 1) (hv 1)
    have hc' := quadFace_contains_contact_pair (F 2) hirr hbound hsupport u v huv hcontact (hu 2) (hv 2)
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc' with hc' | hc'
    all_goals first
      | exact h01 (quadFace_oriented_pair_unique (F 0) (F 1) _ _ ha hb)
      | exact h02 (quadFace_oriented_pair_unique (F 0) (F 2) _ _ ha hc')
      | exact h12 (quadFace_oriented_pair_unique (F 1) (F 2) _ _ hb hc')
  · obtain ⟨i,hi,hii⟩ := quadFace_contains_noncontact_pair (F 0) u v huv hcontact (hu 0) (hv 0)
    obtain ⟨j,hj,hjj⟩ := quadFace_contains_noncontact_pair (F 1) u v huv hcontact (hu 1) (hv 1)
    exact h01 (auxiliary_graphs_diagonal_simple (F 0) (F 1) hsupport i j
      (hi.trans hj.symm) (hii.trans hjj.symm)).1

theorem cube_k2_impossible (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=2) : False := by
  obtain ⟨u,v,huv,hset⟩ := Finset.card_eq_two.mp hk
  have hu : Fintype.card (ContactNeighbor Y c u)=3 := by
    have hh : u ∈ degreeThreeVertices Y c := by rw [hset]; simp
    exact (Finset.mem_filter.mp hh).2
  have hv : Fintype.card (ContactNeighbor Y c v)=3 := by
    have hh : v ∈ degreeThreeVertices Y c := by rw [hset]; simp
    exact (Finset.mem_filter.mp hh).2
  have heuler := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hQ : Fintype.card (QuadFace Y c hY hc)=3 := by
    have hh := heuler.2.2.2.1
    rw [hk] at hh
    change 2*Fintype.card (QuadFace Y c hY hc)=4+2 at hh
    omega
  let e : Fin 3 ≃ QuadFace Y c hY hc :=
    (finIndexEquiv hQ.symm).trans (Fintype.equivFin (QuadFace Y c hY hc)).symm
  exact quadFace_three_common_pair_impossible hirr hbound hsupport e e.injective u v huv
    (fun k => cube_k2_all_quads_contain_u Y c hY hc hcupper hirr hbound hne hsupport hk u hu (e k))
    (fun k => cube_k2_all_quads_contain_u Y c hY hc hcupper hirr hbound hne hsupport hk v hv (e k))

#print axioms quadFace_three_common_pair_impossible
#print axioms cube_k2_impossible
end Blueprint.Thomson.Tail.Implementation
