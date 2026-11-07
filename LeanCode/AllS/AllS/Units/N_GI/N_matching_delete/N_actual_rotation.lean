import AllS.Units.N_GI.N_matching_delete.N_rotation

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def contactGraphRotation {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) :
    Equiv.Perm ((actualContactGraph Y c).neighborSet v) :=
  ((actualNeighborEquiv Y c v).symm.trans (contactRotateAt Y c hY hc v)).trans
    (actualNeighborEquiv Y c v)

theorem contactGraphRotation_cyclic {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8) (n : ℕ) [NeZero n]
    (hn : Fintype.card (ContactNeighbor Y c v)=n) :
    ∃ e : Fin n ≃ (actualContactGraph Y c).neighborSet v,
      ∀i,contactGraphRotation hY hc v (e i)=e (i+1) := by
  obtain ⟨e,he⟩ := contactRotateAt_fin_cycle hY hc v n hn
  refine ⟨e.trans (actualNeighborEquiv Y c v),fun i => ?_⟩
  change actualNeighborEquiv Y c v (contactRotateAt Y c hY hc v (e i))=
    actualNeighborEquiv Y c v (e (i+1))
  exact congrArg (actualNeighborEquiv Y c v) (he i)

theorem deleted_actual_order_exists {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v)) (v : Fin 8) :
    ∃ e : Fin 3 ≃ (graphWithout (actualContactGraph Y c) M).neighborSet v,∀i,
      (e (i+2)).val=
        if M.Adj v ((contactGraphRotation hY hc v).symm
            (retainedToOriginal (actualContactGraph Y c) M v (e i))).val then
          ((contactGraphRotation hY hc v).symm ((contactGraphRotation hY hc v).symm
            (retainedToOriginal (actualContactGraph Y c) M v (e i)))).val
        else ((contactGraphRotation hY hc v).symm
            (retainedToOriginal (actualContactGraph Y c) M v (e i))).val := by
  have hm := hMdegree v
  rcases hd v with h3 | h4
  · obtain ⟨e,he⟩ := contactGraphRotation_cyclic hY hc v 3 h3
    exact deleted_order_three _ _ v (by omega) (contactGraphRotation hY hc v) e he
  · obtain ⟨e,he⟩ := contactGraphRotation_cyclic hY hc v 4 h4
    exact deleted_order_four _ _ hM v (by omega) (contactGraphRotation hY hc v) e he

def deletedActualRotation {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v)) : CubicRotationData where
  graph := graphWithout (actualContactGraph Y c) M
  order v := Classical.choose (deleted_actual_order_exists hY hc M hM hd hMdegree v)

theorem CubicRotationData.rotateAt_symm_order (R : CubicRotationData) (v : Fin 8) (i : Fin 3) :
    (R.rotateAt v).symm (R.order v i)=R.order v (i+2) := by
  apply (R.rotateAt v).injective
  rw [Equiv.apply_symm_apply,R.rotateAt_order]
  congr 1
  fin_cases i <;> decide

theorem deletedActualRotation_previous {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (v : Fin 8) (q : (graphWithout (actualContactGraph Y c) M).neighborSet v) :
    (((deletedActualRotation hY hc M hM hd hMdegree).rotateAt v).symm q).val=
      if M.Adj v ((contactGraphRotation hY hc v).symm
          (retainedToOriginal (actualContactGraph Y c) M v q)).val then
        ((contactGraphRotation hY hc v).symm ((contactGraphRotation hY hc v).symm
          (retainedToOriginal (actualContactGraph Y c) M v q))).val
      else ((contactGraphRotation hY hc v).symm
          (retainedToOriginal (actualContactGraph Y c) M v q)).val := by
  let R := deletedActualRotation hY hc M hM hd hMdegree
  obtain ⟨i,rfl⟩ := (R.order v).surjective q
  rw [CubicRotationData.rotateAt_symm_order]
  exact Classical.choose_spec (deleted_actual_order_exists hY hc M hM hd hMdegree v) i

def retainedDartToContact {Y : Fin 8 → Point} {c : ℝ} (M : SimpleGraph (Fin 8))
    (d : (graphWithout (actualContactGraph Y c) M).Dart) : ContactDart Y c :=
  ⟨d.fst,⟨d.snd,d.adj.1.1.symm,d.adj.1.2⟩⟩

theorem retainedDartToContact_injective {Y : Fin 8 → Point} {c : ℝ} (M : SimpleGraph (Fin 8)) :
    Function.Injective (retainedDartToContact (Y:=Y) (c:=c) M) := by
  intro d e he
  apply SimpleGraph.Dart.ext
  exact Prod.ext (congrArg Sigma.fst he) (congrArg (fun r : ContactDart Y c => r.2.val) he)

theorem deletedActualRotation_next {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (d : (graphWithout (actualContactGraph Y c) M).Dart) :
    let F := contactFaceNext Y c hY hc
    let r := F (retainedDartToContact M d)
    retainedDartToContact M ((deletedActualRotation hY hc M hM hd hMdegree).faceNext d)=
      if M.Adj r.1 r.2.val then F (contactReverse Y c r) else r := by
  dsimp only
  have hh := deletedActualRotation_previous hY hc M hM hd hMdegree d.snd
    ⟨d.fst,(graphWithout (actualContactGraph Y c) M).adj_symm d.adj⟩
  change (retainedDartToContact M ((deletedActualRotation hY hc M hM hd hMdegree).faceNext d)).2.val=
    if M.Adj (contactFaceNext Y c hY hc (retainedDartToContact M d)).1
        (contactFaceNext Y c hY hc (retainedDartToContact M d)).2.val then
      (contactFaceNext Y c hY hc (contactReverse Y c (contactFaceNext Y c hY hc (retainedDartToContact M d)))).2.val
    else (contactFaceNext Y c hY hc (retainedDartToContact M d)).2.val at hh
  by_cases hm : M.Adj (contactFaceNext Y c hY hc (retainedDartToContact M d)).1
      (contactFaceNext Y c hY hc (retainedDartToContact M d)).2.val
  · rw [if_pos hm] at hh ⊢
    exact contactDart_ext rfl hh
  · rw [if_neg hm] at hh ⊢
    exact contactDart_ext rfl hh

#print axioms deletedActualRotation_next
end Blueprint.Thomson.Tail.Implementation
