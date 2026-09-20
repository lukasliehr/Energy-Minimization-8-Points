import Thomson8.RootBounds

namespace Thomson8

theorem eval_lt_of_boxes (x y : K) (h : (encloseK x).hi < (encloseK y).lo) :
    x.eval < y.eval :=
  (encloseK_contains x).2.trans_lt
    ((Rat.cast_lt.mpr h).trans_le (encloseK_contains y).1)

theorem contact_order : -1 < nodeD.eval ∧ nodeD.eval < nodeB.eval ∧
    nodeB.eval < nodeC.eval ∧ nodeC.eval < nodeA.eval ∧ nodeA.eval < 1 := by
  refine ⟨?_,eval_lt_of_boxes _ _ (by decide +kernel),
    eval_lt_of_boxes _ _ (by decide +kernel),
    eval_lt_of_boxes _ _ (by decide +kernel),?_⟩
  · simpa [nodes] using (nodes_interior ⟨3,by decide⟩).1
  · simpa [nodes] using (nodes_interior ⟨0,by decide⟩).2

end Thomson8
