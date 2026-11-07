import AllS.Units.N_GI.N_cubic_quads.N_cube_labeling

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cubic_spanningCube_exact (G : SimpleGraph (Fin 8)) (hdegree : ∀ v, G.degree v=3)
    (e : CubeVertex ≃ Fin 8)
    (hcontact : ∀ i j : Fin 4, i≠j → G.Adj (e (0,i)) (e (1,j))) :
    ∀ u v : CubeVertex, G.Adj (e u) (e v) ↔ u.1≠v.1 ∧ u.2≠v.2 := by
  rintro ⟨t,i⟩ ⟨t',i'⟩
  let S := (Finset.univ.erase i).image (fun j => e (t+1,j))
  have hinj : Function.Injective (fun j : Fin 4 => e (t+1,j)) :=
    fun j k h => congrArg Prod.snd (e.injective h)
  have hScard : S.card=3 := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin]
  have hSsub : S ⊆ G.neighborFinset (e (t,i)) := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    have hji : j≠i := (Finset.mem_erase.mp hj).1
    apply (G.mem_neighborFinset _ _).mpr
    fin_cases t
    · exact hcontact i j hji.symm
    · exact (hcontact j i hji).symm
  have hneighbors : G.neighborFinset (e (t,i))=S := by
    symm
    apply Finset.eq_of_subset_of_card_le hSsub
    rw [G.card_neighborFinset_eq_degree,hdegree,hScard]
  constructor
  · intro hadj
    have hm := (G.mem_neighborFinset _ _).mpr hadj
    rw [hneighbors] at hm
    obtain ⟨j,hj,hjv⟩ := Finset.mem_image.mp hm
    have he := e.injective hjv
    have hfirst : t+1=t' := congrArg Prod.fst he
    have hsecond : j=i' := congrArg Prod.snd he
    have hji : j≠i := (Finset.mem_erase.mp hj).1
    refine ⟨?_,fun hii => hji (hsecond.trans hii.symm)⟩
    intro htt
    have hh : t+1=t := hfirst.trans htt.symm
    have hn : ∀ t : Fin 2, t+1≠t := by decide
    exact hn t hh
  · rintro ⟨htt,hii⟩
    fin_cases t <;> fin_cases t'
    · exact (htt rfl).elim
    · exact hcontact i i' hii
    · exact (hcontact i' i hii.symm).symm
    · exact (htt rfl).elim

theorem cubic_quads_assemble (Q : CubicQuadData) :
    ∃ e : CubeVertex ≃ Fin 8, ∀ u v : CubeVertex,
      Q.graph.Adj (e u) (e v) ↔ u.1≠v.1 ∧ u.2≠v.2 := by
  obtain ⟨e,he⟩ := cubic_quads_cube_labeling Q
  exact ⟨e,cubic_spanningCube_exact Q.graph Q.degree e he⟩

#print axioms cubic_spanningCube_exact
#print axioms cubic_quads_assemble
end Blueprint.Thomson.Tail.Implementation
