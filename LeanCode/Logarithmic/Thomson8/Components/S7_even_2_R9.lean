import Thomson8.FastRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Components

def value_S7_even_2_R9 : Poly := []

theorem check_S7_even_2_R9 :
    (Poly.add (Data.S7_even.fastRow 9 2)
      (Poly.scale (K.ofRat (-1)) value_S7_even_2_R9)).isZero := by
  decide +kernel

theorem sound_S7_even_2_R9 (u v t : ℝ) :
    (Data.S7_even.rowComponent 9 2).eval u v t = value_S7_even_2_R9.eval u v t :=
  by
    rw [Block.fastRow_eval _ (by rfl)]
    exact Poly.eval_eq_of_check _ _ check_S7_even_2_R9 u v t

#print axioms sound_S7_even_2_R9

end Thomson8.Components
