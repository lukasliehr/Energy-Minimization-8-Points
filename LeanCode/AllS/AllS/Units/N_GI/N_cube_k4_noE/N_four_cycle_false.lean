import AllS.Units.N_GI.N_matching_delete.N_shared_edges

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k4_noE_four_cycle_false (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v : Fin 4 → Fin 8) (hinj : Function.Injective v)
    (hcycle : ∀ i : Fin 4,(sharedTriangleGraph hY hc).Adj (v i) (v (i+1))) : False := by
  let S := sharedTriangleGraph hY hc
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have h02 : inner ℝ (Y (v 0)) (Y (v 2))=c := hs.2.2 (v 1) (v 0) (v 2)
    (fun h => (by decide : (0:Fin 4)≠2) (hinj h)) (S.adj_symm (hcycle 0)) (hcycle 1)
  have h13 : inner ℝ (Y (v 1)) (Y (v 3))=c := hs.2.2 (v 2) (v 1) (v 3)
    (fun h => (by decide : (1:Fin 4)≠3) (hinj h)) (S.adj_symm (hcycle 1)) (hcycle 2)
  have hside (i : Fin 4) := (sharedTriangleGraph_subgraph hY hc (hcycle i)).2
  have h01 := hside 0
  have h12 := hside 1
  have h23 := hside 2
  have h30 := hside 3
  apply no_four_contact_clique_of_card (by simp) (Y ∘ v) c (fun i => hY.1 _) hc.1.le (by linarith)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Fin.ext_iff] at hij
  all_goals dsimp only [Function.comp_apply]
  all_goals first
    | exact h01 | exact h12 | exact h23 | exact h30 | exact h02 | exact h13
    | exact (real_inner_comm _ _).trans h01 | exact (real_inner_comm _ _).trans h12
    | exact (real_inner_comm _ _).trans h23 | exact (real_inner_comm _ _).trans h30
    | exact (real_inner_comm _ _).trans h02 | exact (real_inner_comm _ _).trans h13

#print axioms cube_k4_noE_four_cycle_false
end Blueprint.Thomson.Tail.Implementation
