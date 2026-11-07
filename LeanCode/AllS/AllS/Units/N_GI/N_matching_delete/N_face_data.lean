import AllS.Units.N_GI.N_matching_delete.N_actual_rotation

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem triFaceDart_next {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) :
    contactFaceNext Y c hY hc (triFaceDart f i)=triFaceDart f (i+1) := by
  let C := boundaryOrbitCycle Y c hY hc f.val
  change contactFaceNext Y c hY hc (C.point (Fin.cast f.property.symm i))=
    C.point (Fin.cast f.property.symm (i+1))
  rw [fin_cast_add_one]
  exact C.step _

theorem triangle_contactDart_face {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c)
    (hflag : contactTriangleFlag hY hc d=true) :
    ∃ f : TriFace Y c hY hc, ∃ i : Fin 3,triFaceDart f i=d := by
  obtain ⟨⟨g,j⟩,heq⟩ := (cyclePartitionMap_bijective (contactFaceNext Y c hY hc)).2 d
  let C := boundaryOrbitCycle Y c hY hc g
  have hp : C.point j=d := heq
  have hlen : C.size+1=3 := by
    have hh := contactTriangleFlag_orbit_point hY hc g j
    rw [hp,hflag] at hh
    exact of_decide_eq_true hh.symm
  let f : TriFace Y c hY hc := ⟨g,hlen⟩
  refine ⟨f,Fin.cast hlen j,?_⟩
  change C.point (Fin.cast hlen.symm (Fin.cast hlen j))=d
  have hcast : Fin.cast hlen.symm (Fin.cast hlen j)=j := Fin.ext rfl
  rw [hcast]
  exact hp

theorem contactTriangleFlag_three {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c)
    (hflag : contactTriangleFlag hY hc d=true) :
    let F := contactFaceNext Y c hY hc
    F (F (F d))=d := by
  obtain ⟨f,i,rfl⟩ := triangle_contactDart_face hY hc d hflag
  dsimp only
  rw [triFaceDart_next,triFaceDart_next,triFaceDart_next]
  congr 1
  fin_cases i <;> decide

theorem contactTriangleFlag_turn {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y) (d : ContactDart Y c)
    (hflag : contactTriangleFlag hY hc d=true) :
    0 < inner ℝ (crossVec (Y d.1) (Y d.2.val)) (Y (contactFaceNext Y c hY hc d).2.val) := by
  obtain ⟨f,i,rfl⟩ := triangle_contactDart_face hY hc d hflag
  rw [triFaceDart_next,triFaceDart_tip,triFaceDart_tip]
  change 0 < inner ℝ (crossVec (Y (triFaceVertex f i)) (Y (triFaceVertex f (i+1))))
    (Y (triFaceVertex f (i+1+1)))
  simpa only [show i+1+1=i+2 by fin_cases i <;> decide] using triFaceVertex_turn f hirr i

theorem sharedTriangle_thirds_distinct {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y) (d : ContactDart Y c)
    (hflag : contactTriangleFlag hY hc d=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c d)=true) :
    (contactFaceNext Y c hY hc d).2.val≠
      (contactFaceNext Y c hY hc (contactReverse Y c d)).2.val := by
  intro hh
  have hp := contactTriangleFlag_turn hY hc hirr d hflag
  have hn := contactTriangleFlag_turn hY hc hirr (contactReverse Y c d) hrev
  change 0 < inner ℝ (crossVec (Y d.2.val) (Y d.1))
    (Y (contactFaceNext Y c hY hc (contactReverse Y c d)).2.val) at hn
  rw [←hh,crossVec_swap,inner_neg_left] at hn
  linarith

theorem contactTriangleFlag_second_tip {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c)
    (hflag : contactTriangleFlag hY hc d=true) :
    (contactFaceNext Y c hY hc (contactFaceNext Y c hY hc d)).2.val=d.1 :=
  congrArg Sigma.fst (contactTriangleFlag_three hY hc d hflag)

theorem sharedTriangle_thirds_noncontact {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (d : ContactDart Y c) (hflag : contactTriangleFlag hY hc d=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c d)=true) :
    inner ℝ (Y (contactFaceNext Y c hY hc d).2.val)
      (Y (contactFaceNext Y c hY hc (contactReverse Y c d)).2.val)≠c := by
  intro hxy
  let u := d.1
  let v := d.2.val
  let x := (contactFaceNext Y c hY hc d).2.val
  let y := (contactFaceNext Y c hY hc (contactReverse Y c d)).2.val
  have huv : inner ℝ (Y u) (Y v)=c := d.2.property.2
  have hvx : inner ℝ (Y v) (Y x)=c := (contactFaceNext Y c hY hc d).2.property.2
  have huy : inner ℝ (Y u) (Y y)=c := (contactFaceNext Y c hY hc (contactReverse Y c d)).2.property.2
  have hux : inner ℝ (Y u) (Y x)=c := contactTriangleFlag_closing_contact hY hc hirr d hflag
  have hvy : inner ℝ (Y v) (Y y)=c := contactTriangleFlag_closing_contact hY hc hirr (contactReverse Y c d) hrev
  apply no_four_contact_clique_of_card (by simp) (fun i : Fin 4 => Y (![u,v,x,y] i)) c
    (fun i => hY.1 _) hc.1.le (by linarith)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try norm_num [Fin.ext_iff] at hij
  all_goals dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ]
  all_goals first
    | exact huv | exact hvx | exact huy | exact hux | exact hvy | exact hxy
    | exact (real_inner_comm _ _).trans huv | exact (real_inner_comm _ _).trans hvx
    | exact (real_inner_comm _ _).trans huy | exact (real_inner_comm _ _).trans hux
    | exact (real_inner_comm _ _).trans hvy | exact (real_inner_comm _ _).trans hxy

#print axioms sharedTriangle_thirds_noncontact

#print axioms contactTriangleFlag_three
#print axioms sharedTriangle_thirds_distinct
end Blueprint.Thomson.Tail.Implementation
