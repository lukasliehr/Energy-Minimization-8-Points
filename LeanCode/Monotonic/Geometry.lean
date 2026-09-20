import LeanCode.Monotonic.Basic

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
open Real Set
open scoped BigOperators ContDiff
namespace SquareAntiprismCounterexample

/-- The type of each unordered edge in the upstream vertex ordering. -/
def edgeType (i j : Fin 8) : Fin 4 :=
  ![![0,0,1,0,2,3,3,2], ![0,0,0,1,2,2,3,3],
    ![1,0,0,0,3,2,2,3], ![0,1,0,0,3,3,2,2],
    ![2,2,3,3,0,0,1,0], ![3,2,2,3,0,0,0,1],
    ![3,3,2,2,1,0,0,0], ![2,3,3,2,0,1,0,0]] i j

def edgeDistance (a : ℝ) (k : Fin 4) : ℝ := ![dA a,dB a,dC a,dD a] k

lemma X_sq_distance {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1)
    (i j : Fin 8) (hij : i ≠ j) :
    ‖X a i - X a j‖ ^ 2 = edgeDistance a (edgeType i j) := by
  have hr : (√(1-a))^2 = 1-a := Real.sq_sqrt (by linarith [ha.2])
  have hb : (√a)^2 = a := Real.sq_sqrt (le_of_lt ha.1)
  rw [norm_sq_coordinates]
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | skip
  all_goals simp only [X, edgeDistance, edgeType, dA, dB, dC, dD, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons]
  all_goals try simp only [div_eq_mul_inv, inv_sqrt_two]
  all_goals ring_nf
  all_goals try simp only [hr, hb, sqrt_two_sq]
  all_goals ring

lemma energy_X (v : ℝ → ℝ) {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) :
    Ef v (X a) = G v a := by
  unfold Ef
  have h : ∀ i j : Fin 8, i < j →
      v (‖X a i - X a j‖^2) = v (edgeDistance a (edgeType i j)) := by
    intro i j hij
    rw [X_sq_distance ha i j (ne_of_lt hij)]
  simp only [Finset.sum_filter]
  simp_rw [show ∀ i j : Fin 8, (if i < j then v (‖X a i-X a j‖^2) else 0) =
      (if i < j then v (edgeDistance a (edgeType i j)) else 0) from fun i j => by
        split_ifs with hij
        · exact h i j hij
        · rfl]
  simp only [Fin.sum_univ_eight]
  change (0 + v (dA a) + v (dB a) + v (dA a) + v (dC a) + v (dD a) + v (dD a) + v (dC a)) +
    (0 + 0 + v (dA a) + v (dB a) + v (dC a) + v (dC a) + v (dD a) + v (dD a)) +
    (0 + 0 + 0 + v (dA a) + v (dD a) + v (dC a) + v (dC a) + v (dD a)) +
    (0 + 0 + 0 + 0 + v (dD a) + v (dD a) + v (dC a) + v (dC a)) +
    (0 + 0 + 0 + 0 + 0 + v (dA a) + v (dB a) + v (dA a)) +
    (0 + 0 + 0 + 0 + 0 + 0 + v (dA a) + v (dB a)) +
    (0 + 0 + 0 + 0 + 0 + 0 + 0 + v (dA a)) +
    (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) = G v a
  unfold G
  ring

end SquareAntiprismCounterexample
