import Thomson8.MatrixBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Positive.F4Cache

def W : Matrix (Fin 2) (Fin 2) Box := fun i j =>
  (([[⟨(1021623244733184124650029198480540123/340282366920938463463374607431768211456),(1021623246669274618849296502414805470/340282366920938463463374607431768211456)⟩,⟨(1181446562722221544112008615367536547/340282366920938463463374607431768211456),(1181446562839324458213946207846575360/340282366920938463463374607431768211456)⟩],
[⟨(1181446562722221544112008615367536547/340282366920938463463374607431768211456),(1181446562839324458213946207846575360/340282366920938463463374607431768211456)⟩,⟨(3917845079378630548679584030595376570/340282366920938463463374607431768211456),(3917845087413190337261611707036378183/340282366920938463463374607431768211456)⟩]] : List (List Box)).getD i []).getD j (Box.exact 0)

theorem W_row_0 : ∀ j : Fin 2,
    (Data.F4.matrixBox) ⟨0,by decide⟩ j = W ⟨0,by decide⟩ j := by
  unfold Block.matrixBox; decide +kernel

theorem W_row_1 : ∀ j : Fin 2,
    (Data.F4.matrixBox) ⟨1,by decide⟩ j = W ⟨1,by decide⟩ j := by
  unfold Block.matrixBox; decide +kernel

theorem W_eq : (Data.F4.matrixBox) = W := by
  funext i j
  fin_cases i
  · exact W_row_0 j
  · exact W_row_1 j

def PW : Matrix (Fin 2) (Fin 2) Box := fun i j =>
  (([[⟨(18645116665994355276757048439574567269/340282366920938463463374607431768211456),(18645116701328940043077468843785437065/340282366920938463463374607431768211456)⟩,⟨(21561969258390272828747865904890360885/340282366920938463463374607431768211456),(21561969260527457457831728226832054423/340282366920938463463374607431768211456)⟩],
[⟨(-13555478458374811436284643374/340282366920938463463374607431768211456),(13653056990689123236411846075/340282366920938463463374607431768211456)⟩,⟨(29466168347564723253462353442826696246/340282366920938463463374607431768211456),(29466168441913635337148162586173986025/340282366920938463463374607431768211456)⟩]] : List (List Box)).getD i []).getD j (Box.exact 0)

theorem PW_row_0 : ∀ j : Fin 2,
    (Box.matmul 2 Data.F4.PBox W) ⟨0,by decide⟩ j = PW ⟨0,by decide⟩ j := by
  decide +kernel

theorem PW_row_1 : ∀ j : Fin 2,
    (Box.matmul 2 Data.F4.PBox W) ⟨1,by decide⟩ j = PW ⟨1,by decide⟩ j := by
  decide +kernel

theorem PW_eq : (Box.matmul 2 Data.F4.PBox W) = PW := by
  funext i j
  fin_cases i
  · exact PW_row_0 j
  · exact PW_row_1 j

def C : Matrix (Fin 2) (Fin 2) Box := fun i j =>
  (([[⟨(340282366597221659750873392418368981945/340282366920938463463374607431768211456),(340282367242094863947175269330091760147/340282366920938463463374607431768211456)⟩,⟨(-247394015966992135136404950828/340282366920938463463374607431768211456),(249174871217179795210166498890/340282366920938463463374607431768211456)⟩],
[⟨(-247394015966992135136404950851/340282366920938463463374607431768211456),(249174871217179795210166498906/340282366920938463463374607431768211456)⟩,⟨(340282366195993121041089484788413791114/340282366920938463463374607431768211456),(340282367648922922692521952057342333563/340282366920938463463374607431768211456)⟩]] : List (List Box)).getD i []).getD j (Box.exact 0)

theorem C_row_0 : ∀ j : Fin 2,
    (Box.matmul 2 PW Data.F4.PBox.transpose) ⟨0,by decide⟩ j = C ⟨0,by decide⟩ j := by
  decide +kernel

theorem C_row_1 : ∀ j : Fin 2,
    (Box.matmul 2 PW Data.F4.PBox.transpose) ⟨1,by decide⟩ j = C ⟨1,by decide⟩ j := by
  decide +kernel

theorem C_eq : (Box.matmul 2 PW Data.F4.PBox.transpose) = C := by
  funext i j
  fin_cases i
  · exact C_row_0 j
  · exact C_row_1 j

theorem W_contains : ∀ i j, (W i j).Contains (Data.F4.matrix i j) := by
  intro i j
  rw [← W_eq]
  exact Data.F4.matrixBox_contains i j

theorem PW_contains : ∀ i j, (PW i j).Contains ((Data.F4.P*Data.F4.matrix) i j) := by
  intro i j
  rw [← PW_eq]
  exact Box.contains_matmul _ _ _ _ _ Data.F4.PBox_contains W_contains i j

theorem C_contains : ∀ i j, (C i j).Contains ((Data.F4.P*Data.F4.matrix*Data.F4.P.transpose) i j) := by
  intro i j
  rw [← C_eq]
  exact Box.contains_matmul _ _ _ _ _ PW_contains (fun i j => Data.F4.PBox_contains j i) i j

theorem rows_checked : ∀ i : Fin 2, Box.rowError 2 C i ≤ 1/2 := by
  decide +kernel

end Thomson8.Positive.F4Cache

namespace Thomson8.Positive
theorem F4_positive : Data.F4.matrix.PosDef :=
  Data.F4.positive_of_enclosure F4Cache.C F4Cache.C_contains F4Cache.rows_checked

#print axioms F4_positive

end Thomson8.Positive
