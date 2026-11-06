import AllS.Units.N_GI.N_cubic_quads.N_root_faces

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem CubicQuadData.rootNeighbor_injective (Q : CubicQuadData) (o : Fin 8) :
    Function.Injective (Q.rootNeighbor o) := by
  intro i j hij
  exact (Q.order o).injective (Subtype.ext hij)

@[simp] theorem CubicQuadData.rootNeighbor_ne_root (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.rootNeighbor o i≠o := ((Q.graph.ne_of_adj ((cubic_quads_root_faces Q o i).1))).symm

@[simp] theorem CubicQuadData.rootOpposite_ne_root (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.rootOpposite o i≠o := (Q.opposite_distinct (Q.rootDart o i)).symm

@[simp] theorem CubicQuadData.rootOpposite_ne_neighbor (Q : CubicQuadData) (o : Fin 8) (i j : Fin 3) :
    Q.rootOpposite o i≠Q.rootNeighbor o j := by
  intro h
  have hn := Q.opposite_nonadjacent (Q.rootDart o i)
  change ¬ Q.graph.Adj o (Q.rootOpposite o i) at hn
  rw [h] at hn
  exact hn (Q.order o j).property

theorem CubicQuadData.root_rotate_opposite_to_root (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.rotateAt (Q.rootNeighbor o i)
      ⟨Q.rootOpposite o i,(cubic_quads_root_faces Q o i).2.1⟩ =
      ⟨o,(cubic_quads_root_faces Q o i).1.symm⟩ :=
  Q.faceNext_rotate (Q.rootDart o i)

theorem CubicQuadData.root_rotate_root_to_opposite (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.rotateAt (Q.rootNeighbor o (i+1))
      ⟨o,(cubic_quads_root_faces Q o i).2.2.2.1⟩ =
      ⟨Q.rootOpposite o i,(cubic_quads_root_faces Q o i).2.2.1.symm⟩ := by
  let d : Q.graph.Dart := ⟨(Q.rootOpposite o i,Q.rootNeighbor o (i+1)),
    (cubic_quads_root_faces Q o i).2.2.1⟩
  have hd : Q.faceNext (Q.faceNext (Q.rootDart o i))=d := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext rfl (Q.root_second_tip o i)
  have hf : Q.faceNext d=(Q.rootDart o (i+1)).symm := by
    rw [←hd]
    exact Q.root_third_dart o i
  have hrot := Q.faceNext_rotate d
  have harg : (⟨(Q.faceNext d).snd,(Q.faceNext d).adj⟩ : Q.graph.neighborSet d.snd)=
      ⟨o,(cubic_quads_root_faces Q o i).2.2.2.1⟩ :=
    Subtype.ext (congrArg (fun e : Q.graph.Dart => e.snd) hf)
  exact (congrArg (Q.rotateAt d.snd) harg).symm.trans hrot

theorem CubicQuadData.rootOpposite_ne_next (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.rootOpposite o i≠Q.rootOpposite o (i+1) := by
  intro heq
  let v := Q.rootNeighbor o (i+1)
  let q : Q.graph.neighborSet v := ⟨o,(cubic_quads_root_faces Q o i).2.2.2.1⟩
  let p : Q.graph.neighborSet v := ⟨Q.rootOpposite o i,(cubic_quads_root_faces Q o i).2.2.1.symm⟩
  have h1 : Q.rotateAt v q=p := Q.root_rotate_root_to_opposite o i
  have hp : p=⟨Q.rootOpposite o (i+1),(cubic_quads_root_faces Q o (i+1)).2.1⟩ :=
    Subtype.ext heq
  have h2 : Q.rotateAt v p=q :=
    (congrArg (Q.rotateAt v) hp).trans (Q.root_rotate_opposite_to_root o (i+1))
  exact Q.rotateAt_no_two_cycle v q ((congrArg (Q.rotateAt v) h1).trans h2)

theorem CubicQuadData.rootOpposite_injective (Q : CubicQuadData) (o : Fin 8) :
    Function.Injective (Q.rootOpposite o) := by
  intro i j hij
  by_contra hne
  have hcases : ∀ i j : Fin 3, i≠j → j=i+1 ∨ i=j+1 := by decide
  rcases hcases i j hne with h | h
  · exact Q.rootOpposite_ne_next o i ((h ▸ hij))
  · exact Q.rootOpposite_ne_next o j ((h ▸ hij).symm)

def CubicQuadData.rootSeven (Q : CubicQuadData) (o : Fin 8) : Fin 7 → Fin 8 :=
  ![o,Q.rootNeighbor o 0,Q.rootNeighbor o 1,Q.rootNeighbor o 2,
    Q.rootOpposite o 0,Q.rootOpposite o 1,Q.rootOpposite o 2]

theorem cubic_quads_seven_distinct (Q : CubicQuadData) (o : Fin 8) :
    Function.Injective (Q.rootSeven o) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals dsimp [CubicQuadData.rootSeven] at hij
  all_goals first
    | exact ((Q.rootNeighbor_ne_root o _) hij).elim
    | exact ((Q.rootNeighbor_ne_root o _) hij.symm).elim
    | exact ((Q.rootOpposite_ne_root o _) hij).elim
    | exact ((Q.rootOpposite_ne_root o _) hij.symm).elim
    | exact ((Q.rootOpposite_ne_neighbor o _ _) hij).elim
    | exact ((Q.rootOpposite_ne_neighbor o _ _) hij.symm).elim
    | have hh := Q.rootNeighbor_injective o hij; have hn := congrArg Fin.val hh; norm_num at hn
    | have hh := Q.rootOpposite_injective o hij; have hn := congrArg Fin.val hh; norm_num at hn

#print axioms CubicQuadData.rootOpposite_ne_next
#print axioms CubicQuadData.rootOpposite_injective
#print axioms cubic_quads_seven_distinct
end Blueprint.Thomson.Tail.Implementation
