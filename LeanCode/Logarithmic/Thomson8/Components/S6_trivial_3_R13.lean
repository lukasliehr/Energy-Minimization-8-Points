import Thomson8.SymmetricRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Components

def value_S6_trivial_3_R13 : Poly := []

theorem check_S6_trivial_3_R13 :
    (Poly.add (s6PlainRow 13 3)
      (Poly.scale (K.ofRat (-1)) value_S6_trivial_3_R13)).isZero := by
  decide +kernel

theorem sound_S6_trivial_3_R13 (u v t : ℝ) :
    (Data.S6_trivial.rowComponent 13 3).eval u v t = value_S6_trivial_3_R13.eval u v t :=
  by
    rw [s6PlainRow_sound ⟨13,by decide⟩]
    exact Poly.eval_eq_of_check _ _ check_S6_trivial_3_R13 u v t

#print axioms sound_S6_trivial_3_R13

end Thomson8.Components
