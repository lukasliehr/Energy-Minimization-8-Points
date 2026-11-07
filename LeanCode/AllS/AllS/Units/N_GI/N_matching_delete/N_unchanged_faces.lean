import AllS.Units.N_GI.N_matching_delete.N_merged_faces

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem quadFaceDart_flag_false {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    contactTriangleFlag hY hc (quadFaceDart f i)=false := by
  have hh := contactTriangleFlag_orbit_point hY hc f.val (Fin.cast f.property.symm i)
  have hn : decide ((boundaryOrbitCycle Y c hY hc f.val).size+1=3)=false := by
    rw [f.property]
    rfl
  exact hh.trans hn

theorem quadFaceDart_retained {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (M : SimpleGraph (Fin 8))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (f : QuadFace Y c hY hc) (i : Fin 4) :
    ¬M.Adj (quadFaceDart f i).1 (quadFaceDart f i).2.val := by
  intro hm
  have hh := hMtri (quadFaceDart f i) hm
  rw [quadFaceDart_flag_false] at hh
  cases hh

def quadRetainedDart {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (M : SimpleGraph (Fin 8))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (f : QuadFace Y c hY hc) : Fin 4 → (graphWithout (actualContactGraph Y c) M).Dart :=
  fun i => retainedDartOfContact M (quadFaceDart f i) (quadFaceDart_retained M hMtri f i)

theorem quadRetainedDart_step {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (f : QuadFace Y c hY hc) (i : Fin 4) :
    (deletedActualRotation hY hc M hM hd hMdegree).faceNext (quadRetainedDart M hMtri f i)=
      quadRetainedDart M hMtri f (i+1) := by
  apply retainedDartToContact_injective M
  rw [deletedActualRotation_next]
  change (if M.Adj (contactFaceNext Y c hY hc (quadFaceDart f i)).1
      (contactFaceNext Y c hY hc (quadFaceDart f i)).2.val then _ else _)=quadFaceDart f (i+1)
  rw [quadFaceDart_next,if_neg (quadFaceDart_retained M hMtri f (i+1))]
  exact quadFaceDart_next f i

theorem quadRetainedDart_opposite {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : ∀C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (M : SimpleGraph (Fin 8))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (f : QuadFace Y c hY hc) (i : Fin 4) :
    (quadRetainedDart M hMtri f i).fst≠(quadRetainedDart M hMtri f (i+1)).snd ∧
      ¬(graphWithout (actualContactGraph Y c) M).Adj (quadRetainedDart M hMtri f i).fst
        (quadRetainedDart M hMtri f (i+1)).snd := by
  change (quadFaceDart f i).1≠(quadFaceDart f (i+1)).2.val ∧
    ¬(graphWithout (actualContactGraph Y c) M).Adj (quadFaceDart f i).1 (quadFaceDart f (i+1)).2.val
  rw [quadFaceDart_fst,quadFaceDart_tip,show i+1+1=i+2 by fin_cases i <;> decide]
  constructor
  · intro hh
    have hi := quadFaceVertex_injective f hsupport hh
    exact (show i≠i+2 by fin_cases i <;> decide) hi
  · intro h
    exact (auxiliary_graphs_diagonal_noncontact f hirr hbound hsupport i).ne h.1.2

#print axioms quadRetainedDart_step
#print axioms quadRetainedDart_opposite
end Blueprint.Thomson.Tail.Implementation
