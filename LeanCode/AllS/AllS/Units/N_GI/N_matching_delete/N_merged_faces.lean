import AllS.Units.N_GI.N_matching_delete.N_face_data

set_option maxHeartbeats 600000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem degree_le_one_neighbor_unique (M : SimpleGraph (Fin 8)) (hd : ∀v,M.degree v≤1)
    (v w z : Fin 8) (hw : M.Adj v w) (hz : M.Adj v z) : w=z := by
  have hh : (M.neighborFinset v).card≤1 := hd v
  exact Finset.card_le_one.mp hh w ((M.mem_neighborFinset _ _).mpr hw) z ((M.mem_neighborFinset _ _).mpr hz)

theorem removed_triangle_next_retained {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (M : SimpleGraph (Fin 8)) (hdeg : ∀v,M.degree v≤1) (r : ContactDart Y c)
    (hr : M.Adj r.1 r.2.val) :
    ¬M.Adj (contactFaceNext Y c hY hc r).1 (contactFaceNext Y c hY hc r).2.val := by
  intro hm
  have hh := degree_le_one_neighbor_unique M hdeg r.2.val (contactFaceNext Y c hY hc r).2.val r.1 hm (M.adj_symm hr)
  exact contactFaceNext_no_backtrack Y c hY hc hirr r hh

theorem removed_triangle_second_retained {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8)) (hdeg : ∀v,M.degree v≤1)
    (r : ContactDart Y c) (hr : M.Adj r.1 r.2.val) (hflag : contactTriangleFlag hY hc r=true) :
    ¬M.Adj (contactFaceNext Y c hY hc (contactFaceNext Y c hY hc r)).1
      (contactFaceNext Y c hY hc (contactFaceNext Y c hY hc r)).2.val := by
  intro hm
  change M.Adj (contactFaceNext Y c hY hc r).2.val (contactFaceNext Y c hY hc (contactFaceNext Y c hY hc r)).2.val at hm
  rw [contactTriangleFlag_second_tip hY hc r hflag] at hm
  have hh := degree_le_one_neighbor_unique M hdeg r.1 (contactFaceNext Y c hY hc r).2.val r.2.val (M.adj_symm hm) hr
  exact (contactFaceNext Y c hY hc r).2.property.1 hh

def mergedTriangleDart {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (r : ContactDart Y c) : Fin 4 → ContactDart Y c :=
  let F := contactFaceNext Y c hY hc
  ![F r,F (F r),F (contactReverse Y c r),F (F (contactReverse Y c r))]

theorem mergedTriangleDart_retained {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (M : SimpleGraph (Fin 8)) (hdeg : ∀v,M.degree v≤1) (r : ContactDart Y c)
    (hr : M.Adj r.1 r.2.val) (hflag : contactTriangleFlag hY hc r=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c r)=true) (i : Fin 4) :
    ¬M.Adj (mergedTriangleDart hY hc r i).1 (mergedTriangleDart hY hc r i).2.val := by
  fin_cases i
  · exact removed_triangle_next_retained hY hc hirr M hdeg r hr
  · exact removed_triangle_second_retained hY hc M hdeg r hr hflag
  · exact removed_triangle_next_retained hY hc hirr M hdeg (contactReverse Y c r) (M.adj_symm hr)
  · exact removed_triangle_second_retained hY hc M hdeg (contactReverse Y c r) (M.adj_symm hr) hrev

def retainedDartOfContact {Y : Fin 8 → Point} {c : ℝ} (M : SimpleGraph (Fin 8))
    (r : ContactDart Y c) (hkeep : ¬M.Adj r.1 r.2.val) :
    (graphWithout (actualContactGraph Y c) M).Dart :=
  (graphWithout (actualContactGraph Y c) M).dartOfNeighborSet r.1
    ⟨r.2.val,⟨r.2.property.1.symm,r.2.property.2⟩,hkeep⟩

@[simp] theorem retainedDartOfContact_toContact {Y : Fin 8 → Point} {c : ℝ}
    (M : SimpleGraph (Fin 8)) (r : ContactDart Y c) (hkeep : ¬M.Adj r.1 r.2.val) :
    retainedDartToContact M (retainedDartOfContact M r hkeep)=r := rfl

theorem mergedTriangleDart_splice {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (M : SimpleGraph (Fin 8)) (hdeg : ∀v,M.degree v≤1) (r : ContactDart Y c)
    (hr : M.Adj r.1 r.2.val) (hflag : contactTriangleFlag hY hc r=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c r)=true) (i : Fin 4) :
    let F := contactFaceNext Y c hY hc
    let d := F (mergedTriangleDart hY hc r i)
    (if M.Adj d.1 d.2.val then F (contactReverse Y c d) else d)=mergedTriangleDart hY hc r (i+1) := by
  let F := contactFaceNext Y c hY hc
  let t := contactReverse Y c
  have h3 : F (F (F r))=r := contactTriangleFlag_three hY hc r hflag
  have h3rev : F (F (F (t r)))=t r := contactTriangleFlag_three hY hc (t r) hrev
  have hrrev : M.Adj (t r).1 (t r).2.val := M.adj_symm hr
  dsimp only
  fin_cases i
  · change (if M.Adj (F (F r)).1 (F (F r)).2.val then F (t (F (F r))) else F (F r))=F (F r)
    rw [if_neg (removed_triangle_second_retained hY hc M hdeg r hr hflag)]
  · change (if M.Adj (F (F (F r))).1 (F (F (F r))).2.val then F (t (F (F (F r)))) else F (F (F r)))=F (t r)
    rw [h3,if_pos hr]
  · change (if M.Adj (F (F (t r))).1 (F (F (t r))).2.val then F (t (F (F (t r)))) else F (F (t r)))=F (F (t r))
    rw [if_neg (removed_triangle_second_retained hY hc M hdeg (t r) hrrev hrev)]
  · change (if M.Adj (F (F (F (t r)))).1 (F (F (F (t r)))).2.val then F (t (F (F (F (t r))))) else F (F (F (t r))))=F r
    rw [h3rev,if_pos hrrev]
    rfl

theorem mergedTriangleDart_opposite {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (M : SimpleGraph (Fin 8)) (r : ContactDart Y c) (hr : M.Adj r.1 r.2.val)
    (hflag : contactTriangleFlag hY hc r=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c r)=true) (i : Fin 4) :
    (mergedTriangleDart hY hc r i).1≠(mergedTriangleDart hY hc r (i+1)).2.val ∧
      ¬(graphWithout (actualContactGraph Y c) M).Adj (mergedTriangleDart hY hc r i).1
        (mergedTriangleDart hY hc r (i+1)).2.val := by
  let F := contactFaceNext Y c hY hc
  let t := contactReverse Y c
  have hx := sharedTriangle_thirds_distinct hY hc hirr r hflag hrev
  have hn := sharedTriangle_thirds_noncontact hY hc hcupper hirr r hflag hrev
  have hs := contactTriangleFlag_second_tip hY hc r hflag
  have hsrev := contactTriangleFlag_second_tip hY hc (t r) hrev
  fin_cases i
  · change r.2.val≠(F (F r)).2.val ∧ ¬(graphWithout (actualContactGraph Y c) M).Adj r.2.val (F (F r)).2.val
    rw [hs]
    exact ⟨r.2.property.1,fun h => h.2 (M.adj_symm hr)⟩
  · change (F r).2.val≠(F (t r)).2.val ∧ ¬(graphWithout (actualContactGraph Y c) M).Adj (F r).2.val (F (t r)).2.val
    exact ⟨hx,fun h => hn h.1.2⟩
  · change r.1≠(F (F (t r))).2.val ∧ ¬(graphWithout (actualContactGraph Y c) M).Adj r.1 (F (F (t r))).2.val
    rw [hsrev]
    exact ⟨r.2.property.1.symm,fun h => h.2 hr⟩
  · change (F (t r)).2.val≠(F r).2.val ∧ ¬(graphWithout (actualContactGraph Y c) M).Adj (F (t r)).2.val (F r).2.val
    exact ⟨hx.symm,fun h => hn ((real_inner_comm _ _).trans h.1.2)⟩

def mergedRetainedDart {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (M : SimpleGraph (Fin 8)) (hdeg : ∀v,M.degree v≤1) (r : ContactDart Y c)
    (hr : M.Adj r.1 r.2.val) (hflag : contactTriangleFlag hY hc r=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c r)=true) :
    Fin 4 → (graphWithout (actualContactGraph Y c) M).Dart :=
  fun i => retainedDartOfContact M (mergedTriangleDart hY hc r i)
    (mergedTriangleDart_retained hY hc hirr M hdeg r hr hflag hrev i)

theorem mergedRetainedDart_step {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (hdeg : ∀v,M.degree v≤1) (r : ContactDart Y c)
    (hr : M.Adj r.1 r.2.val) (hflag : contactTriangleFlag hY hc r=true)
    (hrev : contactTriangleFlag hY hc (contactReverse Y c r)=true) (i : Fin 4) :
    (deletedActualRotation hY hc M hM hd hMdegree).faceNext (mergedRetainedDart hY hc hirr M hdeg r hr hflag hrev i)=
      mergedRetainedDart hY hc hirr M hdeg r hr hflag hrev (i+1) := by
  apply retainedDartToContact_injective M
  rw [deletedActualRotation_next]
  exact mergedTriangleDart_splice hY hc hirr M hdeg r hr hflag hrev i

#print axioms mergedTriangleDart_opposite
#print axioms mergedRetainedDart_step

#print axioms mergedTriangleDart_splice
end Blueprint.Thomson.Tail.Implementation
