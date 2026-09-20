import LeanCode.Monotonic.Geometry
import LeanCode.Monotonic.Operators
import LeanCode.Monotonic.Calculus

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section
open Real Set Filter
open scoped BigOperators ContDiff Topology
namespace SquareAntiprismCounterexample

def curveC (u : ℝ) : ℝ := (1-u^2)/(1+u^2)
def curveS (u : ℝ) : ℝ := 2*u/(1+u^2)
def curveC1 (u : ℝ) : ℝ := -4*u/(1+u^2)^2
def curveS1 (u : ℝ) : ℝ := 2*(1-u^2)/(1+u^2)^2
def curveC2 (u : ℝ) : ℝ := (-4+12*u^2)/(1+u^2)^3
def curveS2 (u : ℝ) : ℝ := (-12*u+4*u^3)/(1+u^2)^3

lemma curve_denom_pos (u : ℝ) : 0 < 1+u^2 := by positivity
lemma curve_identity (u : ℝ) : curveC u ^ 2 + curveS u ^ 2 = 1 := by
  dsimp [curveC, curveS]
  field_simp [ne_of_gt (curve_denom_pos u)]
  ring

lemma curveC_deriv (u : ℝ) : HasDerivAt curveC (curveC1 u) u := by
  convert ((hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).pow 2)).div
    ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).pow 2))
    (ne_of_gt (curve_denom_pos u)) using 1
  all_goals try rfl
  all_goals norm_num [curveC, curveC1, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply]
  all_goals ring
lemma curveS_deriv (u : ℝ) : HasDerivAt curveS (curveS1 u) u := by
  convert ((hasDerivAt_id u).const_mul 2).div
    ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).pow 2))
    (ne_of_gt (curve_denom_pos u)) using 1
  all_goals try rfl
  all_goals norm_num [curveS, curveS1, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply]
  all_goals ring
lemma curveC1_deriv (u : ℝ) : HasDerivAt curveC1 (curveC2 u) u := by
  convert ((hasDerivAt_id u).const_mul (-4)).div
    (((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).pow 2)).pow 2)
    (pow_ne_zero 2 (ne_of_gt (curve_denom_pos u))) using 1
  all_goals try rfl
  all_goals try dsimp [curveC1, curveC2]
  all_goals field_simp [ne_of_gt (curve_denom_pos u)]
  all_goals ring
lemma curveS1_deriv (u : ℝ) : HasDerivAt curveS1 (curveS2 u) u := by
  convert (((hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).pow 2)).const_mul 2).div
    (((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).pow 2)).pow 2)
    (pow_ne_zero 2 (ne_of_gt (curve_denom_pos u))) using 1
  all_goals try rfl
  all_goals try dsimp [curveS1, curveS2]
  all_goals field_simp [ne_of_gt (curve_denom_pos u)]
  all_goals ring

lemma curve_continuous : Continuous curveC ∧ Continuous curveS ∧
    Continuous curveC1 ∧ Continuous curveS1 ∧ Continuous curveC2 ∧ Continuous curveS2 := by
  have hd : ∀ u : ℝ, 1+u^2 ≠ 0 := fun u => ne_of_gt (curve_denom_pos u)
  have hdp : ∀ u : ℝ, (1+u^2)^3 ≠ 0 := fun u => pow_ne_zero 3 (hd u)
  refine ⟨continuous_iff_continuousAt.mpr (fun u => (curveC_deriv u).continuousAt),
    continuous_iff_continuousAt.mpr (fun u => (curveS_deriv u).continuousAt),
    continuous_iff_continuousAt.mpr (fun u => (curveC1_deriv u).continuousAt),
    continuous_iff_continuousAt.mpr (fun u => (curveS1_deriv u).continuousAt), ?_, ?_⟩
  · unfold curveC2
    fun_prop
  · unfold curveS2
    fun_prop

def deform (a u : ℝ) : Fin 8 → Point :=
  let r := √(1-a)
  let b := √a
  let k := r/√2
  let c := curveC u
  let s := curveS u
  ![!₂[r*c-b*s,0,b*c+r*s], !₂[0,r*c+b*s,b*c-r*s],
    !₂[-r*c+b*s,0,b*c+r*s], !₂[0,-r*c-b*s,b*c-r*s],
    !₂[k,k,-b], !₂[-k,k,-b], !₂[-k,-k,-b], !₂[k,-k,-b]]

lemma deform_zero (a : ℝ) : deform a 0 = X a := by
  simp [deform, X, curveC, curveS]

/-- The seven changing squared distances, in the order A, B-, B+, C+, C-, D+, D-. -/
def deformZ (a u : ℝ) : Fin 7 → ℝ :=
  let c := curveC u
  let s := curveS u
  let q := √(1-a)*√a
  ![dA a+2*s^2,
    4*((1-a)*c^2+a*s^2-2*q*c*s),
    4*((1-a)*c^2+a*s^2+2*q*c*s),
    2-2*C a*c+2*q*kPlus*s,
    2-2*C a*c-2*q*kPlus*s,
    2-2*D a*c+2*q*kMinus*s,
    2-2*D a*c-2*q*kMinus*s]

def deformZ1 (a u : ℝ) : Fin 7 → ℝ :=
  let c := curveC u; let s := curveS u
  let c1 := curveC1 u; let s1 := curveS1 u
  let q := √(1-a)*√a
  ![4*s*s1,
    4*(2*(1-a)*c*c1+2*a*s*s1-2*q*(c1*s+c*s1)),
    4*(2*(1-a)*c*c1+2*a*s*s1+2*q*(c1*s+c*s1)),
    -2*C a*c1+2*q*kPlus*s1,
    -2*C a*c1-2*q*kPlus*s1,
    -2*D a*c1+2*q*kMinus*s1,
    -2*D a*c1-2*q*kMinus*s1]

def deformZ2 (a u : ℝ) : Fin 7 → ℝ :=
  let c := curveC u; let s := curveS u
  let c1 := curveC1 u; let s1 := curveS1 u
  let c2 := curveC2 u; let s2 := curveS2 u
  let q := √(1-a)*√a
  ![4*(s1^2+s*s2),
    4*(2*(1-a)*(c1^2+c*c2)+2*a*(s1^2+s*s2)-2*q*(c2*s+2*c1*s1+c*s2)),
    4*(2*(1-a)*(c1^2+c*c2)+2*a*(s1^2+s*s2)+2*q*(c2*s+2*c1*s1+c*s2)),
    -2*C a*c2+2*q*kPlus*s2,
    -2*C a*c2-2*q*kPlus*s2,
    -2*D a*c2+2*q*kMinus*s2,
    -2*D a*c2-2*q*kMinus*s2]

lemma deformZ_deriv (a u : ℝ) (k : Fin 7) :
    HasDerivAt (fun x => deformZ a x k) (deformZ1 a u k) u := by
  have hc := curveC_deriv u
  have hs := curveS_deriv u
  let q := √(1-a)*√a
  have hA := (hasDerivAt_const u (dA a)).add ((hs.pow 2).const_mul 2)
  have hB := ((hc.pow 2).const_mul (1-a)).add ((hs.pow 2).const_mul a)
  have hBs := (hc.mul hs).const_mul (2*q)
  have hC := (hasDerivAt_const u (2:ℝ)).sub (hc.const_mul (2*C a))
  have hCs := hs.const_mul (2*q*kPlus)
  have hD := (hasDerivAt_const u (2:ℝ)).sub (hc.const_mul (2*D a))
  have hDs := hs.const_mul (2*q*kMinus)
  fin_cases k
  · convert hA using 1 <;> (try rfl)
    simp [deformZ1]
    ring
  · convert ((hB.sub hBs).const_mul 4) using 1 <;> (try rfl)
    all_goals simp [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply,
      deformZ, deformZ1, q]
    all_goals first | (ext x; ring) | ring
  · convert ((hB.add hBs).const_mul 4) using 1 <;> (try rfl)
    all_goals simp [Pi.mul_apply, Pi.pow_apply, deformZ, deformZ1, q]
    all_goals first | (ext x; ring) | ring
  · convert (hC.add hCs) using 1 <;> (try rfl)
    simp [deformZ1, q]
  · convert (hC.sub hCs) using 1 <;> (try rfl)
    simp [deformZ1, q]
  · convert (hD.add hDs) using 1 <;> (try rfl)
    simp [deformZ1, q]
  · convert (hD.sub hDs) using 1 <;> (try rfl)
    simp [deformZ1, q]

lemma deformZ1_deriv (a u : ℝ) (k : Fin 7) :
    HasDerivAt (fun x => deformZ1 a x k) (deformZ2 a u k) u := by
  have hc := curveC_deriv u
  have hs := curveS_deriv u
  have hc1 := curveC1_deriv u
  have hs1 := curveS1_deriv u
  let q := √(1-a)*√a
  have hA := (hs.mul hs1).const_mul 4
  have hB := ((hc.mul hc1).const_mul (2*(1-a))).add ((hs.mul hs1).const_mul (2*a))
  have hBs := ((hc1.mul hs).add (hc.mul hs1)).const_mul (2*q)
  have hC := hc1.const_mul (-2*C a)
  have hCs := hs1.const_mul (2*q*kPlus)
  have hD := hc1.const_mul (-2*D a)
  have hDs := hs1.const_mul (2*q*kMinus)
  fin_cases k
  · convert hA using 1 <;> (try rfl)
    all_goals simp [Pi.mul_apply, deformZ1, deformZ2]
    all_goals first | (ext x; ring) | ring
  · convert ((hB.sub hBs).const_mul 4) using 1 <;> (try rfl)
    all_goals simp [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, deformZ1, deformZ2, q]
    all_goals first | (ext x; ring) | ring
  · convert ((hB.add hBs).const_mul 4) using 1 <;> (try rfl)
    all_goals simp [Pi.mul_apply, deformZ1, deformZ2, q]
    all_goals first | (ext x; ring) | ring
  · exact hC.add hCs
  · exact hC.sub hCs
  · exact hD.add hDs
  · exact hD.sub hDs

lemma deformZ_continuous (a : ℝ) (k : Fin 7) :
    Continuous (fun u => deformZ a u k) ∧
    Continuous (fun u => deformZ1 a u k) ∧
    Continuous (fun u => deformZ2 a u k) := by
  rcases curve_continuous with ⟨hc,hs,hc1,hs1,hc2,hs2⟩
  fin_cases k <;> dsimp only [deformZ, deformZ1, deformZ2]
  all_goals refine ⟨?_,?_,?_⟩ <;> fun_prop

lemma deform_norm {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (u : ℝ) (i : Fin 8) :
    ‖deform a u i‖ = 1 := by
  have hr : (√(1-a))^2 = 1-a := Real.sq_sqrt (by linarith [ha.2])
  have hb : (√a)^2 = a := Real.sq_sqrt ha.1.le
  have hc := curve_identity u
  have hnorm : ‖deform a u i‖^2 = 1 := by
    rw [norm_sq_coordinates]
    fin_cases i <;> simp only [deform, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp]
    all_goals try simp only [div_eq_mul_inv, inv_sqrt_two]
    all_goals ring_nf
    all_goals try simp only [hr,hb,sqrt_two_sq]
    all_goals nlinarith
  nlinarith [norm_nonneg (deform a u i)]

def deformEdgeType (i j : Fin 8) : Fin 9 :=
  ![![0,0,1,0,3,5,5,3], ![0,0,0,2,4,4,6,6],
    ![1,0,0,0,5,3,3,5], ![0,2,0,0,6,6,4,4],
    ![3,4,5,6,7,7,8,7], ![5,4,3,6,7,7,7,8],
    ![5,6,3,4,8,7,7,7], ![3,6,5,4,7,8,7,7]] i j

def deformEdgeDistance (a u : ℝ) (k : Fin 9) : ℝ :=
  ![deformZ a u 0,deformZ a u 1,deformZ a u 2,
    deformZ a u 3,deformZ a u 4,deformZ a u 5,deformZ a u 6,dA a,dB a] k

private lemma vec_cons_val_five {α : Type*} {m : ℕ} (x : α)
    (u : Fin (m+5) → α) : Matrix.vecCons x u 5 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := rfl

private lemma vec_cons_val_six {α : Type*} {m : ℕ} (x : α)
    (u : Fin (m+6) → α) : Matrix.vecCons x u 6 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) := rfl

private lemma vec_cons_val_seven {α : Type*} {m : ℕ} (x : α)
    (u : Fin (m+7) → α) : Matrix.vecCons x u 7 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))) := rfl

private lemma vec_cons_val_eight {α : Type*} {m : ℕ} (x : α)
    (u : Fin (m+8) → α) : Matrix.vecCons x u 8 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))))) := rfl

lemma deform_sq_distance {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1)
    (u : ℝ) (i j : Fin 8) (hij : i ≠ j) :
    ‖deform a u i-deform a u j‖^2 = deformEdgeDistance a u (deformEdgeType i j) := by
  have hr : (√(1-a))^2 = 1-a := Real.sq_sqrt (by linarith [ha.2])
  have hb : (√a)^2 = a := Real.sq_sqrt ha.1.le
  have hc : curveC u ^ 2 = 1 - curveS u ^ 2 := by linarith [curve_identity u]
  rw [norm_sq_coordinates]
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | skip
  all_goals simp only [deform, deformEdgeDistance, deformEdgeType, deformZ,
    dA, dB, C, D, kPlus, kMinus, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, vec_cons_val_five, vec_cons_val_six,
    vec_cons_val_seven, vec_cons_val_eight]
  all_goals try simp only [div_eq_mul_inv, inv_sqrt_two]
  all_goals ring_nf
  all_goals try simp only [hr,hb,sqrt_two_sq,hc]
  all_goals ring

def deformWeight : Fin 7 → ℝ := ![4,1,1,4,4,4,4]
def deformH (a : ℝ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  4*v (dA a)+2*v (dB a)+ ∑ k : Fin 7, deformWeight k * v (deformZ a u k)
def deformH1 (a : ℝ) (v1 : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ k : Fin 7, deformWeight k * (v1 (deformZ a u k)*deformZ1 a u k)
def deformH2 (a : ℝ) (v1 v2 : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ k : Fin 7, deformWeight k *
    (v2 (deformZ a u k)*deformZ1 a u k^2+v1 (deformZ a u k)*deformZ2 a u k)

lemma deform_energy (v : ℝ → ℝ) {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (u : ℝ) :
    Ef v (deform a u) = deformH a v u := by
  unfold Ef
  simp only [Finset.sum_filter]
  simp_rw [show ∀ i j : Fin 8, (if i < j then v (‖deform a u i-deform a u j‖^2) else 0) =
      (if i < j then v (deformEdgeDistance a u (deformEdgeType i j)) else 0) from fun i j => by
        split_ifs with hij
        · rw [deform_sq_distance ha u i j (ne_of_lt hij)]
        · rfl]
  unfold deformH
  simp only [Fin.sum_univ_eight, Fin.sum_univ_seven]
  change (0 + v (deformZ a u 0) + v (deformZ a u 1) + v (deformZ a u 0) + v (deformZ a u 3) + v (deformZ a u 5) + v (deformZ a u 5) + v (deformZ a u 3)) +
    (0 + 0 + v (deformZ a u 0) + v (deformZ a u 2) + v (deformZ a u 4) + v (deformZ a u 4) + v (deformZ a u 6) + v (deformZ a u 6)) +
    (0 + 0 + 0 + v (deformZ a u 0) + v (deformZ a u 5) + v (deformZ a u 3) + v (deformZ a u 3) + v (deformZ a u 5)) +
    (0 + 0 + 0 + 0 + v (deformZ a u 6) + v (deformZ a u 6) + v (deformZ a u 4) + v (deformZ a u 4)) +
    (0 + 0 + 0 + 0 + 0 + v (dA a) + v (dB a) + v (dA a)) +
    (0 + 0 + 0 + 0 + 0 + 0 + v (dA a) + v (dB a)) +
    (0 + 0 + 0 + 0 + 0 + 0 + 0 + v (dA a)) +
    (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) =
    4*v (dA a)+2*v (dB a)+ (4*v (deformZ a u 0) + 1*v (deformZ a u 1) + 1*v (deformZ a u 2) + 4*v (deformZ a u 3) + 4*v (deformZ a u 4) + 4*v (deformZ a u 5) + 4*v (deformZ a u 6))
  ring

end SquareAntiprismCounterexample
