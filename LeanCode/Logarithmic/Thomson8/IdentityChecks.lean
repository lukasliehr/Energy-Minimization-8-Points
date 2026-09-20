import Thomson8.Components.F0_0
import Thomson8.Components.F0_1
import Thomson8.Components.F0_2
import Thomson8.Components.F0_3
import Thomson8.Components.F0_4
import Thomson8.Components.F1_0
import Thomson8.Components.F1_1
import Thomson8.Components.F1_2
import Thomson8.Components.F1_3
import Thomson8.Components.F1_4
import Thomson8.Components.F2_0
import Thomson8.Components.F2_1
import Thomson8.Components.F2_2
import Thomson8.Components.F2_3
import Thomson8.Components.F2_4
import Thomson8.Components.F4_0
import Thomson8.Components.F4_1
import Thomson8.Components.F4_2
import Thomson8.Components.F4_3
import Thomson8.Components.F4_4
import Thomson8.Components.F5_0
import Thomson8.Components.F5_1
import Thomson8.Components.F5_2
import Thomson8.Components.F5_3
import Thomson8.Components.F5_4
import Thomson8.Components.S6_trivial_0
import Thomson8.Components.S6_trivial_1
import Thomson8.Components.S6_trivial_2
import Thomson8.Components.S6_trivial_3
import Thomson8.Components.S6_trivial_4
import Thomson8.Components.S7_even_0
import Thomson8.Components.S7_even_1
import Thomson8.Components.S7_even_2
import Thomson8.Components.S7_even_3
import Thomson8.Components.S7_even_4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8
open Components

def reducedComponent (ell : ℕ) : Poly :=
  match ell with
  | 0 => Poly.sum [value_F0_0, value_F1_0, value_F2_0, value_F4_0, value_F5_0, value_S6_trivial_0, value_S7_even_0]
  | 1 => Poly.sum [value_F0_1, value_F1_1, value_F2_1, value_F4_1, value_F5_1, value_S6_trivial_1, value_S7_even_1]
  | 2 => Poly.sum [value_F0_2, value_F1_2, value_F2_2, value_F4_2, value_F5_2, value_S6_trivial_2, value_S7_even_2]
  | 3 => Poly.sum [value_F0_3, value_F1_3, value_F2_3, value_F4_3, value_F5_3, value_S6_trivial_3, value_S7_even_3]
  | 4 => Poly.sum [value_F0_4, value_F1_4, value_F2_4, value_F4_4, value_F5_4, value_S6_trivial_4, value_S7_even_4]
  | _ => []

theorem reduced_identity_0 :
    (Poly.add (targetComponent Data.hermite 0)
      (Poly.scale (K.ofRat (-1)) (reducedComponent 0))).isZero := by
  decide +kernel
#print axioms reduced_identity_0

theorem reduced_identity_1 :
    (Poly.add (targetComponent Data.hermite 1)
      (Poly.scale (K.ofRat (-1)) (reducedComponent 1))).isZero := by
  decide +kernel
#print axioms reduced_identity_1

theorem reduced_identity_2 :
    (Poly.add (targetComponent Data.hermite 2)
      (Poly.scale (K.ofRat (-1)) (reducedComponent 2))).isZero := by
  decide +kernel
#print axioms reduced_identity_2

theorem reduced_identity_3 :
    (Poly.add (targetComponent Data.hermite 3)
      (Poly.scale (K.ofRat (-1)) (reducedComponent 3))).isZero := by
  decide +kernel
#print axioms reduced_identity_3

theorem reduced_identity_4 :
    (Poly.add (targetComponent Data.hermite 4)
      (Poly.scale (K.ofRat (-1)) (reducedComponent 4))).isZero := by
  decide +kernel
#print axioms reduced_identity_4

theorem rhs_reduced (ell : Fin 5) (u v t : ℝ) :
    (rhsComponent Data.blocks ell).eval u v t = (reducedComponent ell).eval u v t := by
  fin_cases ell
  · simp only [rhsComponent, Data.blocks, reducedComponent, List.map_cons, List.map_nil,
      Poly.eval_sum, List.sum_cons, List.sum_nil, sound_F0_0, sound_F1_0, sound_F2_0, sound_F4_0, sound_F5_0, sound_S6_trivial_0, sound_S7_even_0]
  · simp only [rhsComponent, Data.blocks, reducedComponent, List.map_cons, List.map_nil,
      Poly.eval_sum, List.sum_cons, List.sum_nil, sound_F0_1, sound_F1_1, sound_F2_1, sound_F4_1, sound_F5_1, sound_S6_trivial_1, sound_S7_even_1]
  · simp only [rhsComponent, Data.blocks, reducedComponent, List.map_cons, List.map_nil,
      Poly.eval_sum, List.sum_cons, List.sum_nil, sound_F0_2, sound_F1_2, sound_F2_2, sound_F4_2, sound_F5_2, sound_S6_trivial_2, sound_S7_even_2]
  · simp only [rhsComponent, Data.blocks, reducedComponent, List.map_cons, List.map_nil,
      Poly.eval_sum, List.sum_cons, List.sum_nil, sound_F0_3, sound_F1_3, sound_F2_3, sound_F4_3, sound_F5_3, sound_S6_trivial_3, sound_S7_even_3]
  · simp only [rhsComponent, Data.blocks, reducedComponent, List.map_cons, List.map_nil,
      Poly.eval_sum, List.sum_cons, List.sum_nil, sound_F0_4, sound_F1_4, sound_F2_4, sound_F4_4, sound_F5_4, sound_S6_trivial_4, sound_S7_even_4]

theorem certificate_identity (u v t : ℝ) (logs : Fin 5 → ℝ) :
    (∑ ell : Fin 5, logs ell * (targetComponent Data.hermite ell).eval u v t) =
    (∑ ell : Fin 5, logs ell * (rhsComponent Data.blocks ell).eval u v t) := by
  apply Finset.sum_congr rfl
  intro ell _
  rw [rhs_reduced ell]
  congr 1
  apply Poly.eval_eq_of_check
  fin_cases ell
  · exact reduced_identity_0
  · exact reduced_identity_1
  · exact reduced_identity_2
  · exact reduced_identity_3
  · exact reduced_identity_4

#print axioms certificate_identity

end Thomson8
