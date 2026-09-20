import Thomson8.Components.S7_even_3_R0
import Thomson8.Components.S7_even_3_R1
import Thomson8.Components.S7_even_3_R2
import Thomson8.Components.S7_even_3_R3
import Thomson8.Components.S7_even_3_R4
import Thomson8.Components.S7_even_3_R5
import Thomson8.Components.S7_even_3_R6
import Thomson8.Components.S7_even_3_R7
import Thomson8.Components.S7_even_3_R8
import Thomson8.Components.S7_even_3_R9
import Thomson8.Components.S7_even_3_R10
import Thomson8.Components.S7_even_3_R11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Components

def value_S7_even_3 : Poly := []

def rowSum_S7_even_3 : Poly := Poly.sum [value_S7_even_3_R0, value_S7_even_3_R1, value_S7_even_3_R2, value_S7_even_3_R3, value_S7_even_3_R4, value_S7_even_3_R5, value_S7_even_3_R6, value_S7_even_3_R7, value_S7_even_3_R8, value_S7_even_3_R9, value_S7_even_3_R10, value_S7_even_3_R11]

theorem rows_check_S7_even_3 :
    (Poly.add rowSum_S7_even_3
      (Poly.scale (K.ofRat (-1)) value_S7_even_3)).isZero := by
  decide +kernel

theorem sound_S7_even_3 (u v t : ℝ) :
    (Data.S7_even.component 3).eval u v t = value_S7_even_3.eval u v t := by
  have hs : (Data.S7_even.component 3).eval u v t = rowSum_S7_even_3.eval u v t := by
    rw [Block.component_eval_rows]
    change ((List.range 12).map fun i => (Data.S7_even.rowComponent i 3).eval u v t).sum = _
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, rowSum_S7_even_3, Poly.eval_sum, sound_S7_even_3_R0, sound_S7_even_3_R1, sound_S7_even_3_R2, sound_S7_even_3_R3, sound_S7_even_3_R4, sound_S7_even_3_R5, sound_S7_even_3_R6, sound_S7_even_3_R7, sound_S7_even_3_R8, sound_S7_even_3_R9, sound_S7_even_3_R10, sound_S7_even_3_R11]
    <;> ring
  exact hs.trans (Poly.eval_eq_of_check _ _ rows_check_S7_even_3 u v t)

#print axioms sound_S7_even_3

end Thomson8.Components
