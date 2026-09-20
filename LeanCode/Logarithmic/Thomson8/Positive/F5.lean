import Thomson8.MatrixBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Positive.F5Cache

def W : Matrix (Fin 1) (Fin 1) Box := fun i j =>
  (([[⟨(894691303700166601990184453577704476/340282366920938463463374607431768211456),(894691308473682535810176667458619202/340282366920938463463374607431768211456)⟩]] : List (List Box)).getD i []).getD j (Box.exact 0)

theorem W_row_0 : ∀ j : Fin 1,
    (Data.F5.matrixBox) ⟨0,by decide⟩ j = W ⟨0,by decide⟩ j := by
  unfold Block.matrixBox; decide +kernel

theorem W_eq : (Data.F5.matrixBox) = W := by
  funext i j
  fin_cases i
  · exact W_row_0 j

def PW : Matrix (Fin 1) (Fin 1) Box := fun i j =>
  (([[⟨(17448428974487591648489430575700178689/340282366920938463463374607431768211456),(17448429067581548620441426435800699740/340282366920938463463374607431768211456)⟩]] : List (List Box)).getD i []).getD j (Box.exact 0)

theorem PW_row_0 : ∀ j : Fin 1,
    (Box.matmul 1 Data.F5.PBox W) ⟨0,by decide⟩ j = PW ⟨0,by decide⟩ j := by
  decide +kernel

theorem PW_eq : (Box.matmul 1 Data.F5.PBox W) = PW := by
  funext i j
  fin_cases i
  · exact PW_row_0 j

def C : Matrix (Fin 1) (Fin 1) Box := fun i j =>
  (([[⟨(340282366016788878117717957533946484042/340282366920938463463374607431768211456),(340282367832323788830861926273619403743/340282366920938463463374607431768211456)⟩]] : List (List Box)).getD i []).getD j (Box.exact 0)

theorem C_row_0 : ∀ j : Fin 1,
    (Box.matmul 1 PW Data.F5.PBox.transpose) ⟨0,by decide⟩ j = C ⟨0,by decide⟩ j := by
  decide +kernel

theorem C_eq : (Box.matmul 1 PW Data.F5.PBox.transpose) = C := by
  funext i j
  fin_cases i
  · exact C_row_0 j

theorem W_contains : ∀ i j, (W i j).Contains (Data.F5.matrix i j) := by
  intro i j
  rw [← W_eq]
  exact Data.F5.matrixBox_contains i j

theorem PW_contains : ∀ i j, (PW i j).Contains ((Data.F5.P*Data.F5.matrix) i j) := by
  intro i j
  rw [← PW_eq]
  exact Box.contains_matmul _ _ _ _ _ Data.F5.PBox_contains W_contains i j

theorem C_contains : ∀ i j, (C i j).Contains ((Data.F5.P*Data.F5.matrix*Data.F5.P.transpose) i j) := by
  intro i j
  rw [← C_eq]
  exact Box.contains_matmul _ _ _ _ _ PW_contains (fun i j => Data.F5.PBox_contains j i) i j

theorem rows_checked : ∀ i : Fin 1, Box.rowError 1 C i ≤ 1/2 := by
  decide +kernel

end Thomson8.Positive.F5Cache

namespace Thomson8.Positive
theorem F5_positive : Data.F5.matrix.PosDef :=
  Data.F5.positive_of_enclosure F5Cache.C F5Cache.C_contains F5Cache.rows_checked

#print axioms F5_positive

end Thomson8.Positive
