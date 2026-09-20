import Thomson8.SymmetricRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8.Components

def value_S6_trivial_1_R17 : Poly := []

theorem check_S6_trivial_1_R17 :
    (Poly.add (s6PlainRow 17 1)
      (Poly.scale (K.ofRat (-1)) value_S6_trivial_1_R17)).isZero := by
  decide +kernel

theorem sound_S6_trivial_1_R17 (u v t : ℝ) :
    (Data.S6_trivial.rowComponent 17 1).eval u v t = value_S6_trivial_1_R17.eval u v t :=
  by
    rw [s6PlainRow_sound ⟨17,by decide⟩]
    exact Poly.eval_eq_of_check _ _ check_S6_trivial_1_R17 u v t

#print axioms sound_S6_trivial_1_R17

end Thomson8.Components
