import AllS.Units.N_G.N_pair_hessian
import AllS.Units.N_G.N_incident_bound
import AllS.Units.N_G.N_derivative_stability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Real Filter
namespace Blueprint.Thomson.Tail.Implementation

def energyFirst (p : ℝ) (q ξ : TangentCoordinates) : ℝ :=
  ∑ ij∈unorderedPairs, -p*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-1)*pairDerivative q ij.1 ij.2 ξ

def energySecond (p : ℝ) (q ξ : TangentCoordinates) : ℝ :=
  ∑ ij∈unorderedPairs, (p*(p+1)*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-2)*(pairDerivative q ij.1 ij.2 ξ)^2-
    p*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-1)*pairSecond q ξ ij.1 ij.2)

theorem small_chart_distance_pos (q : TangentCoordinates) (hq : ‖q‖≤3/10) (i j : Fin 8) (hij : i≠j) :
    0<squaredDistance (orthographicChart q) i j := by
  have h := (balanced_energy_distinct_chart q hq).2 i j hij
  unfold squaredDistance
  nlinarith

theorem pair_distance_line_hasDerivAt (q ξ : TangentCoordinates) (t : ℝ) (hq : ‖q+t • ξ‖<1) (i j : Fin 8) :
    HasDerivAt (fun u : ℝ=>squaredDistance (orthographicChart (q+u • ξ)) i j)
      (pairDerivative (q+t • ξ) i j ξ) t := by
  have hline : HasDerivAt (fun u : ℝ=>q+u • ξ) ξ t := by
    simpa using ((hasDerivAt_id t).smul_const ξ).const_add q
  exact (pair_hasFDerivAt (q+t • ξ) hq i j).comp_hasDerivAt t hline

theorem energy_line_hasDerivAt (p : ℝ) (q ξ : TangentCoordinates) (t : ℝ) (hq : ‖q+t • ξ‖≤3/10) :
    HasDerivAt (fun u : ℝ=>squaredEnergy p (orthographicChart (q+u • ξ)))
      (energyFirst p (q+t • ξ) ξ) t := by
  have hterm (ij : Fin 8×Fin 8) (hij : ij∈unorderedPairs) :
      HasDerivAt (fun u : ℝ=>(squaredDistance (orthographicChart (q+u • ξ)) ij.1 ij.2)^(-p))
        (-p*(squaredDistance (orthographicChart (q+t • ξ)) ij.1 ij.2)^(-p-1)*pairDerivative (q+t • ξ) ij.1 ij.2 ξ) t := by
    have hd := small_chart_distance_pos _ hq ij.1 ij.2 (ne_of_lt ((mem_unorderedPairs _ _).mp hij))
    have h := (pair_distance_line_hasDerivAt q ξ t (by linarith) ij.1 ij.2).rpow_const (Or.inl hd.ne') (p := -p)
    convert! h using 1 <;> ring
  convert! HasDerivAt.sum hterm using 1 <;> first | rfl | (funext u; simp [squaredEnergy_pairs,energyFirst,Finset.sum_apply])

theorem energyFirst_line_hasDerivAt (p : ℝ) (q ξ : TangentCoordinates) (hq : ‖q‖≤3/10) :
    HasDerivAt (fun t : ℝ=>energyFirst p (q+t • ξ) ξ) (energySecond p q ξ) 0 := by
  have hterm (ij : Fin 8×Fin 8) (hij : ij∈unorderedPairs) :
      HasDerivAt (fun t : ℝ=>-p*(squaredDistance (orthographicChart (q+t • ξ)) ij.1 ij.2)^(-p-1)*
        pairDerivative (q+t • ξ) ij.1 ij.2 ξ)
      (p*(p+1)*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-2)*(pairDerivative q ij.1 ij.2 ξ)^2-
        p*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-1)*pairSecond q ξ ij.1 ij.2) 0 := by
    have hd := small_chart_distance_pos q hq ij.1 ij.2 (ne_of_lt ((mem_unorderedPairs _ _).mp hij))
    have hD : HasDerivAt (fun t : ℝ=>squaredDistance (orthographicChart (q+t • ξ)) ij.1 ij.2)
        (pairDerivative q ij.1 ij.2 ξ) 0 := by
      simpa using pair_distance_line_hasDerivAt q ξ 0 (by simpa using (show ‖q‖<1 by linarith)) ij.1 ij.2
    have hr := hD.rpow_const (Or.inl (by simpa using hd.ne')) (p := -p-1)
    have h := (hr.const_mul (-p)).mul (pairDerivative_line_hasDerivAt q ξ (by linarith) ij.1 ij.2)
    convert! h using 1
    simp only [zero_smul,add_zero]
    have he : -p-1-1=-p-2 := by ring
    rw [he]
    ring
  convert! HasDerivAt.sum hterm using 1 <;> first | rfl | (funext u; simp [energyFirst,energySecond,Finset.sum_apply])

theorem energy_line_second_derivative (p : ℝ) (q ξ : TangentCoordinates) (hq : ‖q‖<3/10) :
    HasDerivAt (deriv (fun t : ℝ=>squaredEnergy p (orthographicChart (q+t • ξ)))) (energySecond p q ξ) 0 := by
  apply (energyFirst_line_hasDerivAt p q ξ hq.le).congr_of_eventuallyEq
  have hc : ContinuousAt (fun t : ℝ=>‖q+t • ξ‖) 0 := by fun_prop
  have hh : ‖q+(0:ℝ) • ξ‖<3/10 := by simpa using hq
  filter_upwards [hc.eventually (isOpen_Iio.mem_nhds hh)] with t ht
  exact (energy_line_hasDerivAt p q ξ t ht.le).deriv

def hessianPositiveSum (p : ℝ) (q ξ : TangentCoordinates) : ℝ :=
  ∑ ij∈unorderedPairs, (tau/squaredDistance (orthographicChart q) ij.1 ij.2)^(p+2)*(pairDerivative q ij.1 ij.2 ξ)^2

def hessianNegativeSum (p : ℝ) (q ξ : TangentCoordinates) : ℝ :=
  ∑ ij∈unorderedPairs, (tau/squaredDistance (orthographicChart q) ij.1 ij.2)^(p+1)*pairSecond q ξ ij.1 ij.2

theorem normalized_pair_powers (p d : ℝ) (hd : 0<d) :
    tau^(p+2)*d^(-p-2)=(tau/d)^(p+2) ∧
    tau^(p+2)*d^(-p-1)=tau*(tau/d)^(p+1) := by
  constructor
  · rw [Real.rpow_def_of_pos tau_pos,Real.rpow_def_of_pos hd,Real.rpow_def_of_pos (div_pos tau_pos hd),
      ←Real.exp_add,Real.log_div tau_pos.ne' hd.ne']
    congr 1
    ring
  · calc
      _ = exp (log tau*(p+2)+log d*(-p-1)) := by
        rw [Real.rpow_def_of_pos tau_pos,Real.rpow_def_of_pos hd,Real.exp_add]
      _ = exp (log tau+(log tau-log d)*(p+1)) := by congr 1 <;> ring
      _ = _ := by rw [Real.exp_add,Real.exp_log tau_pos,Real.rpow_def_of_pos (div_pos tau_pos hd),Real.log_div tau_pos.ne' hd.ne']

theorem full_hessian_exact_hessian (p : ℝ) (hp : 0<p) (q ξ : TangentCoordinates) (hq : ‖q‖≤3/10) :
    tau^(p+2)/p*energySecond p q ξ=(p+1)*hessianPositiveSum p q ξ-tau*hessianNegativeSum p q ξ := by
  dsimp [energySecond,hessianPositiveSum,hessianNegativeSum]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hd := small_chart_distance_pos q hq ij.1 ij.2 (ne_of_lt ((mem_unorderedPairs _ _).mp hij))
  obtain ⟨h1,h2⟩ := normalized_pair_powers p _ hd
  calc
    _ = (p+1)*(tau^(p+2)*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-2))*(pairDerivative q ij.1 ij.2 ξ)^2-
        (tau^(p+2)*(squaredDistance (orthographicChart q) ij.1 ij.2)^(-p-1))*pairSecond q ξ ij.1 ij.2 := by
      field_simp [hp.ne']
      <;> ring
    _ = _ := by rw [h1,h2];ring

#print axioms full_hessian_exact_hessian
#print axioms energy_line_second_derivative
end Blueprint.Thomson.Tail.Implementation
