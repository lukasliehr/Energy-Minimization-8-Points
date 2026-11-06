import AllS.Units.N_GI.N_cube_k2.N_impossible
import Mathlib.Combinatorics.SimpleGraph.Dart

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

/-- A cyclic order on exactly three neighbors; all darts and graphs use Mathlib. -/
structure CubicRotationData where
  graph : SimpleGraph (Fin 8)
  order : ∀ v, Fin 3 ≃ graph.neighborSet v

def CubicRotationData.rotateAt (R : CubicRotationData) (v : Fin 8) :
    Equiv.Perm (R.graph.neighborSet v) :=
  ((R.order v).symm.trans (Equiv.addRight 1)).trans (R.order v)

theorem CubicRotationData.rotateAt_order (R : CubicRotationData) (v : Fin 8) (i : Fin 3) :
    R.rotateAt v (R.order v i)=R.order v (i+1) := by simp [rotateAt]

def CubicRotationData.faceNext (R : CubicRotationData) (d : R.graph.Dart) : R.graph.Dart :=
  R.graph.dartOfNeighborSet d.snd ((R.rotateAt d.snd).symm ⟨d.fst,d.adj.symm⟩)

def CubicRotationData.facePrevious (R : CubicRotationData) (d : R.graph.Dart) : R.graph.Dart :=
  (R.graph.dartOfNeighborSet d.fst (R.rotateAt d.fst ⟨d.snd,d.adj⟩)).symm

theorem CubicRotationData.faceNext_previous (R : CubicRotationData) (d : R.graph.Dart) :
    R.faceNext (R.facePrevious d)=d := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change ((R.rotateAt d.fst).symm (R.rotateAt d.fst ⟨d.snd,d.adj⟩)).val=d.snd
    rw [Equiv.symm_apply_apply]

theorem CubicRotationData.facePrevious_next (R : CubicRotationData) (d : R.graph.Dart) :
    R.facePrevious (R.faceNext d)=d := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change ((R.rotateAt d.snd) ((R.rotateAt d.snd).symm ⟨d.fst,d.adj.symm⟩)).val=d.fst
    rw [Equiv.apply_symm_apply]
  · rfl

theorem CubicRotationData.faceNext_injective (R : CubicRotationData) : Function.Injective R.faceNext :=
  Function.LeftInverse.injective R.facePrevious_next

@[simp] theorem CubicRotationData.faceNext_base (R : CubicRotationData) (d : R.graph.Dart) :
    (R.faceNext d).fst=d.snd := rfl

theorem CubicRotationData.faceNext_rotate (R : CubicRotationData) (d : R.graph.Dart) :
    R.rotateAt d.snd ⟨(R.faceNext d).snd,(R.faceNext d).adj⟩=⟨d.fst,d.adj.symm⟩ :=
  (R.rotateAt d.snd).apply_symm_apply _

theorem CubicRotationData.rotateAt_no_two_cycle (R : CubicRotationData) (v : Fin 8)
    (q : R.graph.neighborSet v) : R.rotateAt v (R.rotateAt v q)≠q := by
  obtain ⟨i,rfl⟩ := (R.order v).surjective q
  rw [R.rotateAt_order,R.rotateAt_order]
  intro hh
  have hi := (R.order v).injective hh
  fin_cases i <;> simp_all

theorem CubicRotationData.degree (R : CubicRotationData) (v : Fin 8) : R.graph.degree v=3 := by
  have h := Fintype.card_congr (R.order v)
  rw [Fintype.card_fin] at h
  exact (R.graph.card_neighborSet_eq_degree v).symm.trans h.symm

/-- The only face facts needed by the finite cubic construction. -/
structure CubicQuadData extends CubicRotationData where
  face_four : ∀ d : graph.Dart, toCubicRotationData.faceNext (toCubicRotationData.faceNext
    (toCubicRotationData.faceNext (toCubicRotationData.faceNext d)))=d
  opposite_distinct : ∀ d : graph.Dart, d.fst≠(toCubicRotationData.faceNext d).snd
  opposite_nonadjacent : ∀ d : graph.Dart, ¬ graph.Adj d.fst (toCubicRotationData.faceNext d).snd

def CubicQuadData.rootDart (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) : Q.graph.Dart :=
  Q.graph.dartOfNeighborSet o (Q.order o i)

def CubicQuadData.rootNeighbor (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) : Fin 8 :=
  (Q.order o i).val

def CubicQuadData.rootOpposite (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) : Fin 8 :=
  (Q.faceNext (Q.rootDart o i)).snd

theorem CubicQuadData.face_third_previous (Q : CubicQuadData) (d : Q.graph.Dart) :
    Q.faceNext (Q.faceNext (Q.faceNext d))=Q.facePrevious d := by
  apply Q.faceNext_injective
  rw [Q.face_four,Q.faceNext_previous]

theorem CubicQuadData.root_third_dart (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.faceNext (Q.faceNext (Q.faceNext (Q.rootDart o i)))=
      (Q.rootDart o (i+1)).symm := by
  rw [Q.face_third_previous]
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change (Q.rotateAt o (Q.order o i)).val=(Q.order o (i+1)).val
    rw [Q.rotateAt_order]
  · rfl

theorem CubicQuadData.root_second_tip (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    (Q.faceNext (Q.faceNext (Q.rootDart o i))).snd=Q.rootNeighbor o (i+1) :=
  congrArg (fun d : Q.graph.Dart => d.fst) (Q.root_third_dart o i)

theorem cubic_quads_root_faces (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.graph.Adj o (Q.rootNeighbor o i) ∧
    Q.graph.Adj (Q.rootNeighbor o i) (Q.rootOpposite o i) ∧
    Q.graph.Adj (Q.rootOpposite o i) (Q.rootNeighbor o (i+1)) ∧
    Q.graph.Adj (Q.rootNeighbor o (i+1)) o ∧
    o≠Q.rootOpposite o i ∧ ¬Q.graph.Adj o (Q.rootOpposite o i) := by
  refine ⟨(Q.order o i).property,(Q.faceNext (Q.rootDart o i)).adj,?_,
    (Q.order o (i+1)).property.symm,Q.opposite_distinct (Q.rootDart o i),Q.opposite_nonadjacent (Q.rootDart o i)⟩
  have h := (Q.faceNext (Q.faceNext (Q.rootDart o i))).adj
  exact (Q.root_second_tip o i) ▸ h

#print axioms CubicRotationData.rotateAt_no_two_cycle
#print axioms CubicRotationData.degree
#print axioms cubic_quads_root_faces
end Blueprint.Thomson.Tail.Implementation
