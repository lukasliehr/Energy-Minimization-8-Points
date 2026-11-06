import AllS.Units.N_GI.N_cube_k6.N_one_shared_vertex_impossible

set_option maxHeartbeats 300000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k6_shared_edge (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) (f g : TriFace Y c hY hc) (hfg : f≠g) :
    ∃ v w : Fin 8,v≠w ∧ triFaceVertices f∩triFaceVertices g={v,w} ∧ ContactAdj Y c v w := by
  let A := triFaceVertices f
  let B := triFaceVertices g
  have hA : A.card=3 := triFaceVertices_card f hsupport
  have hB : B.card=3 := triFaceVertices_card g hsupport
  have hle : (A∩B).card≤3 := by
    have hh := Finset.card_le_card (Finset.inter_subset_left (s₁:=A) (s₂:=B))
    omega
  have hne0 : (A∩B).card≠0 := by
    intro hh
    have he := Finset.card_eq_zero.mp hh
    have hd : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr he
    exact cube_k6_disjoint_triangles_impossible Y c hY hc hcupper hirr hbound hne hsupport hk f g hfg hd
  have hne1 : (A∩B).card≠1 := by
    intro hh
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hh
    exact cube_k6_one_shared_vertex_impossible Y c hY hc hcupper hirr hbound hne hsupport hk f g hfg v hv
  have hne3 : (A∩B).card≠3 := by
    intro hh
    have hIA : A∩B=A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hIB : A∩B=B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hfg (triFaceVertices_injective hirr hsupport (hIA.symm.trans hIB))
  have htwo : (A∩B).card=2 := by omega
  obtain ⟨v,w,hvw,hset⟩ := Finset.card_eq_two.mp htwo
  refine ⟨v,w,hvw,hset,?_⟩
  have hv : v∈A := Finset.mem_of_mem_inter_left (hset ▸ Finset.mem_insert_self _ _)
  have hw : w∈A := Finset.mem_of_mem_inter_left (hset ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
  refine ⟨hvw,?_⟩
  have hij : i≠j := by intro h;exact hvw (hi.symm.trans ((congrArg (triFaceVertex f) h).trans hj))
  exact (congrArg₂ (fun a b => inner ℝ (Y a) (Y b)) hi hj).symm.trans (triFaceVertex_contact f i j hij)

#print axioms cube_k6_shared_edge
end Blueprint.Thomson.Tail.Implementation
