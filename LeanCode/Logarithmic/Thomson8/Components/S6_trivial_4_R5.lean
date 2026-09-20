import Thomson8.SymmetricRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Components

def value_S6_trivial_4_R5 : Poly := []

theorem check_S6_trivial_4_R5 :
    (Poly.add (s6PlainRow 5 4)
      (Poly.scale (K.ofRat (-1)) value_S6_trivial_4_R5)).isZero := by
  decide +kernel

theorem sound_S6_trivial_4_R5 (u v t : ℝ) :
    (Data.S6_trivial.rowComponent 5 4).eval u v t = value_S6_trivial_4_R5.eval u v t :=
  by
    rw [s6PlainRow_sound ⟨5,by decide⟩]
    exact Poly.eval_eq_of_check _ _ check_S6_trivial_4_R5 u v t

#print axioms sound_S6_trivial_4_R5

end Thomson8.Components
