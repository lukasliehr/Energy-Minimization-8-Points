import AllS.Units.N_GI.N_cube_k4_noE.N_four_graphs

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k4_noE_s_components (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (hE : ∃v,Fintype.card (ContactNeighbor Y c v)=4 ∧ faceCornerCount (boundaryArray Y c hY hc 3) v=3) :
    ∃p : Fin 4,∃v : Fin 4 → Fin 8,Function.Injective v ∧
      (∀z,Fintype.card (ContactNeighbor Y c z)=4 ↔ ∃i,v i=z) ∧
      ∀i j,(sharedTriangleGraph hY hc).Adj (v i) (v j) ↔ fourGraphAdj (fourPatternBits p) i j := by
  let S := sharedTriangleGraph hY hc
  let d := fun z => Fintype.card (ContactNeighbor Y c z)
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (z : Fin 8) : d z=3 ∨ d z=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound z (ha z)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c z)=3 ∨ Fintype.card (ContactNeighbor Y c z)=4
    omega
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have hcard : Fintype.card {z : Fin 8 // d z=4}=4 := by
    have hh := degree_three_four_count d hd
    have h3 : (Finset.univ.filter (fun z => d z=3)).card=4 := hk
    rw [Fintype.card_subtype]
    omega
  let e0 : Fin 4 ≃ {z : Fin 8 // d z=4} := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin 4 → Fin 8 := fun i => (e0 i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e0.injective
  have hf4 (i : Fin 4) : d (f i)=4 := (e0 i).property
  have hfull (z : Fin 8) : d z=4 ↔ ∃i,f i=z := by
    constructor
    · intro hz
      exact ⟨e0.symm ⟨z,hz⟩,congrArg Subtype.val (e0.apply_symm_apply ⟨z,hz⟩)⟩
    · rintro ⟨i,rfl⟩
      exact hf4 i
  let b : Fin 6 → Bool := ![decide (S.Adj (f 0) (f 1)),decide (S.Adj (f 0) (f 2)),
    decide (S.Adj (f 0) (f 3)),decide (S.Adj (f 1) (f 2)),
    decide (S.Adj (f 1) (f 3)),decide (S.Adj (f 2) (f 3))]
  have hb (i j : Fin 4) : fourGraphAdj b i j ↔ S.Adj (f i) (f j) := by
    fin_cases i <;> fin_cases j
    all_goals simp only [fourGraphAdj,b,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.reduceEq,decide_eq_true_eq,false_and,true_and,and_false,and_true,false_or,or_false,true_or,or_true]
    all_goals try exact Iff.rfl
    all_goals try exact ⟨fun h => S.adj_symm h,fun h => S.adj_symm h⟩
    all_goals simp
    all_goals exact ⟨fun h => S.adj_symm h,fun h => S.adj_symm h⟩
  have hdeg (i : Fin 4) : fourGraphDegree b i=S.degree (f i) := by
    have hset : S.neighborFinset (f i)=(Finset.univ.filter (fourGraphAdj b i)).image f := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        have hadj := (S.mem_neighborFinset _ _).mp hz
        obtain ⟨j,rfl⟩ := (hfull z).mp ((hs.2.1 _ _ hadj).2)
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hb i j).mpr hadj⟩,rfl⟩
      · rintro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        exact (S.mem_neighborFinset _ _).mpr ((hb i j).mp (Finset.mem_filter.mp hj).2)
    rw [←S.card_neighborFinset_eq_degree,hset,Finset.card_image_of_injective _ hf]
  obtain ⟨p,e,he⟩ := fourGraph_classification b (fun i => (hdeg i).trans_le (hs.1 (f i)).1) (by
    obtain ⟨z,hz4,hz3⟩ := hE
    obtain ⟨i,rfl⟩ := (hfull z).mp hz4
    exact ⟨i,(hdeg i).trans ((hs.1 (f i)).2.1.mpr ⟨hz4,hz3⟩)⟩)
  refine ⟨p,f ∘ e,hf.comp e.injective,?_,?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := (hfull z).mp hz
      exact ⟨e.symm i,(congrArg f (e.apply_symm_apply i)).trans hi⟩
    · rintro ⟨i,hi⟩
      exact (hfull z).mpr ⟨e i,hi⟩
  · intro i j
    exact (hb (e i) (e j)).symm.trans (he i j)

#print axioms cube_k4_noE_s_components
end Blueprint.Thomson.Tail.Implementation
