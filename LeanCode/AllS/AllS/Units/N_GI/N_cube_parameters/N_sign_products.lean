import AllS.Units.N_GI.N_cube_parameters.N_definitions

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cubeSign_weighted_dot (q : Fin 3 → ℝ) (i j : Fin 4) (hij : i≠j) :
    (∑k,cubeSign i k*cubeSign j k*q k)=2*q (cubePairAxis i j)-∑k,q k := by
  rw [Fin.sum_univ_three,Fin.sum_univ_three]
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · change 1*1*q 0+1*(-1)*q 1+1*(-1)*q 2=2*q 0-(q 0+q 1+q 2)
    ring
  · change 1*(-1)*q 0+1*1*q 1+1*(-1)*q 2=2*q 1-(q 0+q 1+q 2)
    ring
  · change 1*(-1)*q 0+1*(-1)*q 1+1*1*q 2=2*q 2-(q 0+q 1+q 2)
    ring
  · change 1*1*q 0+(-1)*1*q 1+(-1)*1*q 2=2*q 0-(q 0+q 1+q 2)
    ring
  · exact False.elim (hij rfl)
  · change 1*(-1)*q 0+(-1)*1*q 1+(-1)*(-1)*q 2=2*q 2-(q 0+q 1+q 2)
    ring
  · change 1*(-1)*q 0+(-1)*(-1)*q 1+(-1)*1*q 2=2*q 1-(q 0+q 1+q 2)
    ring
  · change (-1)*1*q 0+1*1*q 1+(-1)*1*q 2=2*q 1-(q 0+q 1+q 2)
    ring
  · change (-1)*1*q 0+1*(-1)*q 1+(-1)*(-1)*q 2=2*q 2-(q 0+q 1+q 2)
    ring
  · exact False.elim (hij rfl)
  · change (-1)*(-1)*q 0+1*(-1)*q 1+(-1)*1*q 2=2*q 0-(q 0+q 1+q 2)
    ring
  · change (-1)*1*q 0+(-1)*1*q 1+1*1*q 2=2*q 2-(q 0+q 1+q 2)
    ring
  · change (-1)*1*q 0+(-1)*(-1)*q 1+1*(-1)*q 2=2*q 1-(q 0+q 1+q 2)
    ring
  · change (-1)*(-1)*q 0+(-1)*1*q 1+1*(-1)*q 2=2*q 0-(q 0+q 1+q 2)
    ring
  · exact False.elim (hij rfl)

#print axioms cubeSign_weighted_dot
end Blueprint.Thomson.Tail.Implementation
