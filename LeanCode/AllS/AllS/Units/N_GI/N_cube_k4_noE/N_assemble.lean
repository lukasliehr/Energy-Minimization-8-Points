import AllS.Units.N_GI.N_cube_k4_noE.N_triangle_false
import AllS.Units.N_GI.N_cube_k4_noE.N_three_path_false
import AllS.Units.N_GI.N_cube_k4_noE.N_four_path_false

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_k4_noE_assemble (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4) :
    ∀z,Fintype.card (ContactNeighbor Y c z)=4 → faceCornerCount (boundaryArray Y c hY hc 3) z≠3 := by
  intro z hz ht
  obtain ⟨p,v,hinj,hfull,hpat⟩ := cube_k4_noE_s_components Y c hY hc hcupper hirr hbound hne hsupport hk ⟨z,hz,ht⟩
  fin_cases p
  · exact cube_k4_noE_three_path_false Y c hY hc hcupper hirr hbound hne hsupport hk v hinj hfull hpat
  · exact cube_k4_noE_four_path_false Y c hY hc hcupper hirr hbound hne hsupport v hinj hfull hpat
  · exact cube_k4_noE_triangle_false Y c hY hc hcupper hirr hbound hne hsupport hk v hinj hfull hpat
  · apply cube_k4_noE_four_cycle_false Y c hY hc hcupper hirr hbound hne hsupport v hinj
    intro i
    apply (hpat i (i+1)).mpr
    exact (by decide +kernel : ∀i : Fin 4,fourGraphAdj (fourPatternBits 3) i (i+1)) i

#print axioms cube_k4_noE_assemble
end Blueprint.Thomson.Tail.Implementation
