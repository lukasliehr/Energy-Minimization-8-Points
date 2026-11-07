import AllS.Units.N_GI.N_cube_k6.N_disjoint_arithmetic
import AllS.Units.N_GI.N_cube_k6.N_triangle_face_pair
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem actualContactGraph_degree (Y : Fin 8 → Point) (c : ℝ) (v : Fin 8) :
    (actualContactGraph Y c).degree v=Fintype.card (ContactNeighbor Y c v) := by
  have hh := Fintype.card_congr (actualNeighborEquiv Y c v)
  exact ((actualContactGraph Y c).card_neighborSet_eq_degree v).symm.trans hh.symm

theorem adjacencyMatrix_row_degree (G : SimpleGraph (Fin 8)) (v : Fin 8) :
    (∑ j,G.adjMatrix ℕ v j)=G.degree v := by
  simp only [SimpleGraph.adjMatrix_apply,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]

theorem cube_k6_disjoint_given_label (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) (e : Equiv.Perm (Fin 8))
    (htLabel : ∀i,faceCornerCount (boundaryArray Y c hY hc 3) (e i)=if i.val<6 then 1 else 0)
    (htriLabel : ∀i j,i≠j → sameTriangleIndex i j → inner ℝ (Y (e i)) (Y (e j))=c) : False := by
  let d := fun i => Fintype.card (ContactNeighbor Y c (e i))
  let G := actualContactGraph Y c
  let D := diagonalGraph hsupport
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    omega
  have hcard4 : (Finset.univ.filter (fun i => d i=4)).card=2 := by
    have hh := degree_three_four_count (fun v => Fintype.card (ContactNeighbor Y c v)) hd
    have h3 : (Finset.univ.filter (fun v => Fintype.card (ContactNeighbor Y c v)=3)).card=6 := hk
    have hr := Equiv.sum_comp e (fun v => if Fintype.card (ContactNeighbor Y c v)=4 then (1:ℕ) else 0)
    simp only [Finset.card_filter] at hh h3 ⊢
    change (∑ i,if Fintype.card (ContactNeighbor Y c (e i))=4 then 1 else 0)=2
    omega
  obtain ⟨x,y,hxy,hpair⟩ := Finset.card_eq_two.mp hcard4
  have hfour (i : Fin 8) : d i=4 ↔ i=x ∨ i=y := by
    have hm : i∈Finset.univ.filter (fun i => d i=4) ↔ i∈({x,y} : Finset (Fin 8)) := by rw [hpair]
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton] using hm
  have hdval (i : Fin 8) : d i=if i=x ∨ i=y then 4 else 3 := by
    rcases hd (e i) with h3 | h4
    · have hn : ¬(i=x ∨ i=y) := by intro h;have hh := (hfour i).mpr h;change Fintype.card (ContactNeighbor Y c (e i))=4 at hh;omega
      simp only [if_neg hn]
      exact h3
    · rw [if_pos ((hfour i).mp h4)]
      exact h4
  have hDval (i : Fin 8) : D.degree (e i)=if i=x ∨ i=y then (if i.val<6 then 3 else 4)
      else (if i.val<6 then 2 else 3) := by
    have hh := auxiliary_graphs_diagonal_degrees Y c hY hc hcupper hirr hsupport (e i)
    change D.degree (e i)+faceCornerCount (boundaryArray Y c hY hc 3) (e i)=d i at hh
    rw [htLabel i,hdval i] at hh
    split_ifs at hh ⊢ <;> omega
  apply disjoint_triangles_incidence_impossible
    (fun i j => G.adjMatrix ℕ (e i) (e j)) (fun i j => D.adjMatrix ℕ (e i) (e j)) x y hxy
  · intro i;simp
  · intro i;simp
  · intro i j;simp [SimpleGraph.adj_comm]
  · intro i j;simp [SimpleGraph.adj_comm]
  · intro i j
    by_cases hg : G.Adj (e i) (e j)
    · have hn : ¬D.Adj (e i) (e j) := fun h =>
        (diagonalGraph_noncontact hirr hbound hsupport _ _ h).ne hg.2
      simp [SimpleGraph.adjMatrix_apply,hg,hn]
    · simp only [SimpleGraph.adjMatrix_apply,if_neg hg,zero_add]
      split_ifs <;> omega
  · intro i
    rw [Equiv.sum_comp e (G.adjMatrix ℕ (e i)),adjacencyMatrix_row_degree]
    exact (actualContactGraph_degree Y c (e i)).trans (hdval i)
  · intro i
    rw [Equiv.sum_comp e (D.adjMatrix ℕ (e i)),adjacencyMatrix_row_degree]
    exact hDval i
  · intro i j hij ht
    have hadj : G.Adj (e i) (e j) := ⟨e.injective.ne hij,htriLabel i j hij ht⟩
    simp [SimpleGraph.adjMatrix_apply,hadj]
  · intro i j hi hjx hjy hj
    have hi4 := (hfour i).mpr hi
    have hj3 : d j=3 := by rw [hdval j,if_neg (fun h => h.elim hjx hjy)]
    have hti : faceCornerCount (boundaryArray Y c hY hc 3) (e i)≤2 := by rw [htLabel];split_ifs <;> omega
    have htj : faceCornerCount (boundaryArray Y c hY hc 3) (e j)=1 := by rw [htLabel,if_pos hj]
    have hn : ¬D.Adj (e i) (e j) := by
      intro h
      exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (e i) (e j) h).2.2
        ⟨hi4,hti,hj3,htj⟩
    simp [SimpleGraph.adjMatrix_apply,hn]

theorem cube_k6_disjoint_triangles_impossible (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) (f g : TriFace Y c hY hc)
    (hfg : f≠g) : ¬Disjoint (triFaceVertices f) (triFaceVertices g) := by
  intro hdis
  obtain ⟨e,h0,h1,h2,h3,h4,h5⟩ := disjoint_triangles_labeling f g hsupport hdis
  have he := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hT : Fintype.card (TriFace Y c hY hc)=2 := by
    have hh := he.2.2.1
    rw [hk] at hh
    exact hh
  have hpair : ({f,g} : Finset (TriFace Y c hY hc))=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,hT,Finset.card_pair hfg]
  have hfaces (h : TriFace Y c hY hc) : h=f ∨ h=g := by
    have hm : h∈({f,g} : Finset (TriFace Y c hY hc)) := hpair ▸ Finset.mem_univ h
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hfset : triFaceVertices f={e 0,e 1,e 2} := by
    rw [triFaceVertices,show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
    simp only [Finset.image_insert,Finset.image_singleton,h0,h1,h2]
  have hgset : triFaceVertices g={e 3,e 4,e 5} := by
    rw [triFaceVertices,show (Finset.univ : Finset (Fin 3))={0,1,2} by decide]
    simp only [Finset.image_insert,Finset.image_singleton,h3,h4,h5]
  have hfmem (i : Fin 8) : e i∈triFaceVertices f ↔ i.val<3 := by
    rw [hfset]
    simp only [Finset.mem_insert,Finset.mem_singleton,e.injective.eq_iff]
    fin_cases i <;> decide
  have hgmem (i : Fin 8) : e i∈triFaceVertices g ↔ (3 : ℕ) ≤ i.val ∧ i.val < 6 := by
    rw [hgset]
    simp only [Finset.mem_insert,Finset.mem_singleton,e.injective.eq_iff]
    fin_cases i <;> decide
  apply cube_k6_disjoint_given_label Y c hY hc hcupper hirr hbound hne hsupport hk e
  · intro i
    rw [triFace_pair_indicator f g hfg hfaces hsupport (e i)]
    simp only [hfmem i,hgmem i]
    fin_cases i <;> norm_num
  · intro i j hij ht
    fin_cases i <;> fin_cases j
    all_goals try norm_num [Fin.ext_iff] at hij
    all_goals try norm_num [sameTriangleIndex,Fin.ext_iff] at ht
    all_goals first
      | (convert (triFaceVertex_contact f 0 1 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact f 0 2 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact f 1 0 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact f 1 2 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact f 2 0 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact f 2 1 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact g 0 1 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact g 0 2 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact g 1 0 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact g 1 2 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact g 2 0 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)
      | (convert (triFaceVertex_contact g 2 1 (by decide)) using 1 <;> simp only [←h0,←h1,←h2,←h3,←h4,←h5] <;> congr 2 <;> decide)

#print axioms cube_k6_disjoint_triangles_impossible
#print axioms cube_k6_disjoint_given_label
end Blueprint.Thomson.Tail.Implementation
