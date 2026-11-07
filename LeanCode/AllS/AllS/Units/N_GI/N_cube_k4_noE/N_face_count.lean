import AllS.Units.N_GI.N_cube_k4_noE.N_shared_faces

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem triangle_incidence_avoid_three {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hT : Fintype.card (TriFace Y c hY hc)=4)
    (f g h : TriFace Y c hY hc) (hfg : f≠g) (hfh : f≠h) (hgh : g≠h)
    (z : Fin 8) (hzf : z∉triFaceVertices f) (hzg : z∉triFaceVertices g) (hzh : z∉triFaceVertices h) :
    faceCornerCount (boundaryArray Y c hY hc 3) z≤1 := by
  have hsub : triFacesAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) z⊆Finset.univ\{f,g,h} := by
    intro a ha
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2
    have hmem : z∈triFaceVertices a := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨fun he => hzf (he ▸ hmem),fun he => hzg (he ▸ hmem),fun he => hzh (he ▸ hmem)⟩
  have hh := Finset.card_le_card hsub
  rw [triFacesAt_card hsupport] at hh
  have h3 : ({f,g,h} : Finset (TriFace Y c hY hc)).card=3 := by simp [hfg,hfh,hgh]
  have h4 : (Finset.univ : Finset (TriFace Y c hY hc)).card=4 := Finset.card_univ.trans hT
  have hs := Finset.card_sdiff_of_subset (Finset.subset_univ ({f,g,h} : Finset (TriFace Y c hY hc)))
  omega

theorem triFace_ne_of_member {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : TriFace Y c hY hc) (z : Fin 8)
    (hf : z∈triFaceVertices f) (hg : z∉triFaceVertices g) : f≠g := fun he => hg (he ▸ hf)

#print axioms triangle_incidence_avoid_three
end Blueprint.Thomson.Tail.Implementation
