import AllS.Units.N_GI.N_matching_delete.N_shared_edges

set_option maxHeartbeats 600000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem quadFace_side_not_shared {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    ¬(sharedTriangleGraph hY hc).Adj (quadFaceVertex f i) (quadFaceVertex f (i+1)) := by
  intro hs
  have hh := sharedTriangleGraph_flag hY hc (quadFaceDart f i)
  rw [quadFaceDart_tip] at hh
  exact (Bool.false_ne_true) ((quadFaceDart_flag_false f i).symm.trans (hh hs))

theorem contact_not_shared_has_quad {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v w : Fin 8) (hadj : ContactAdj Y c v w)
    (hnot : ¬(sharedTriangleGraph hY hc).Adj v w) :
    ∃ f : QuadFace Y c hY hc, ∃ i : Fin 4,
      quadFaceVertex f i=v ∧ (quadFaceVertex f (i+1)=w ∨ quadFaceVertex f (i+3)=w) := by
  let q : ContactNeighbor Y c v := ⟨w,hadj.1.symm,hadj.2⟩
  let d : ContactDart Y c := ⟨v,q⟩
  by_cases h1 : contactTriangleFlag hY hc d=true
  · have h2 : contactTriangleFlag hY hc (contactReverse Y c d)≠true := fun h => hnot ⟨q,rfl,h1,h⟩
    obtain ⟨f,j,hj⟩ := nontriangle_contactDart_quad hY hc hcupper hirr hsupport _ h2
    have hb : quadFaceVertex f j=w := congrArg Sigma.fst hj
    have ht : quadFaceVertex f (j+1)=v := by
      rw [←quadFaceDart_tip]
      exact congrArg (fun e : ContactDart Y c => e.2.val) hj
    refine ⟨f,j+1,ht,Or.inr ?_⟩
    simpa only [show j+1+3=j by fin_cases j <;> decide] using hb
  · obtain ⟨f,j,hj⟩ := nontriangle_contactDart_quad hY hc hcupper hirr hsupport d h1
    refine ⟨f,j,congrArg Sigma.fst hj,Or.inl ?_⟩
    rw [←quadFaceDart_tip]
    exact congrArg (fun e : ContactDart Y c => e.2.val) hj

/-- The other side of a quadrilateral corner is an unshared contact edge. -/
theorem unshared_contact_opposite {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v w : Fin 8) (hadj : ContactAdj Y c v w)
    (hnot : ¬(sharedTriangleGraph hY hc).Adj v w) :
    ∃ z : Fin 8,z≠w ∧ ContactAdj Y c v z ∧
      ¬(sharedTriangleGraph hY hc).Adj v z ∧ (diagonalGraph hsupport).Adj w z := by
  obtain ⟨f,i,hv,hw⟩ := contact_not_shared_has_quad hY hc hcupper hirr hsupport v w hadj hnot
  have hinj := quadFaceVertex_injective f hsupport
  rcases hw with hw | hw
  · let z := quadFaceVertex f (i+3)
    refine ⟨z,?_,?_,?_,?_⟩
    · intro hz
      exact (show i+3≠i+1 by fin_cases i <;> decide) (hinj (hz.trans hw.symm))
    · refine ⟨?_,?_⟩
      · intro hz
        exact (show i≠i+3 by fin_cases i <;> decide) (hinj (hv.trans hz))
      · rw [←hv,real_inner_comm]
        simpa only [show i+3+1=i by fin_cases i <;> decide] using quadFaceVertex_side f (i+3)
    · intro hs
      have hh := quadFace_side_not_shared f (i+3)
      rw [show i+3+1=i by fin_cases i <;> decide,hv] at hh
      exact hh ((sharedTriangleGraph hY hc).adj_symm hs)
    · refine ⟨f,i+1,hw,?_⟩
      congr 1
      fin_cases i <;> decide
  · let z := quadFaceVertex f (i+1)
    refine ⟨z,?_,?_,?_,?_⟩
    · intro hz
      exact (show i+1≠i+3 by fin_cases i <;> decide) (hinj (hz.trans hw.symm))
    · refine ⟨?_,?_⟩
      · intro hz
        exact (show i≠i+1 by fin_cases i <;> decide) (hinj (hv.trans hz))
      · rw [←hv]
        exact quadFaceVertex_side f i
    · intro hs
      have hh := quadFace_side_not_shared f i
      rw [hv] at hh
      exact hh hs
    · refine ⟨f,i+3,hw,?_⟩
      congr 1
      fin_cases i <;> decide

#print axioms unshared_contact_opposite
end Blueprint.Thomson.Tail.Implementation
