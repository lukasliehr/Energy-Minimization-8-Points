import AllS.Units.N_GI.N_balanced_energy.N_reference_data
import AllS.Units.N_GI.N_balanced_energy.N_distinct_chart
import AllS.Units.N_GI.N_minimizer_exists.N_separation_threshold

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def balancedX (p : ℝ) (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  (p/tau)*contactDelta q e.1 (contactNext e)-balancedZ e

def balancedMean (p : ℝ) (q : TangentCoordinates) : ℝ :=
  (∑ e : ContactIndex, contactWeight e*balancedX p q e)/contactTotalWeight

theorem rpow_exp_linear_lower (p d : ℝ) (hp : 0<p) (hd : 0<d) :
    exp (-(p/tau)*(d-tau)) ≤ tau^p*d^(-p) := by
  have ht := tau_pos
  have hratio : 0<d/tau := div_pos hd ht
  have hl := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hd.ne' ht.ne'] at hl
  rw [Real.rpow_def_of_pos ht,Real.rpow_def_of_pos hd,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  calc
    _ = -p*(d/tau-1) := by field_simp <;> ring
    _ ≤ _ := by nlinarith

theorem contactPair_injective : Function.Injective contactPair := by decide

theorem contactPair_distance (Y : Fin 8 → Point) (e : ContactIndex) :
    squaredDistance Y (contactPair e).1 (contactPair e).2=squaredDistance Y e.1 (contactNext e) := by
  unfold contactPair
  by_cases h : e.1 ≤ contactNext e
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h),squaredDistance_symm]

theorem contact_sum_le_energy (p : ℝ) (Y : Fin 8 → Point) :
    (∑ e : ContactIndex, (squaredDistance Y e.1 (contactNext e))^(-p)) ≤ squaredEnergy p Y := by
  have hi : (∑ ij ∈ cyclicContactPairs, (squaredDistance Y ij.1 ij.2)^(-p))=
      ∑ e : ContactIndex, (squaredDistance Y e.1 (contactNext e))^(-p) := by
    rw [cyclicContactPairs,Finset.sum_image]
    · simp only [contactPair_distance]
    · exact fun a _ b _ h=>contactPair_injective h
  rw [←hi,squaredEnergy_pairs]
  apply Finset.sum_le_sum_of_subset_of_nonneg cyclicContactPairs_subset
  intro ij _ _
  exact Real.rpow_nonneg (sq_nonneg _) _

theorem balanced_energy_exponential_lower (p : ℝ) (hp : 0<p) (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    balancedLambda*exp (-balancedMean p q)*
      (∑ e : ContactIndex, contactWeight e*exp (-(balancedX p q e-balancedMean p q))) ≤
        tau^p*squaredEnergy p (orthographicChart q) := by
  have heq (e : ContactIndex) :
      balancedLambda*exp (-balancedMean p q)*contactWeight e*exp (-(balancedX p q e-balancedMean p q))=
      exp (-(p/tau)*contactDelta q e.1 (contactNext e)) := by
    have hbal := balancedZ_exponential e
    calc
      _ = balancedLambda*contactWeight e*(exp (-balancedMean p q)*
          exp (-(balancedX p q e-balancedMean p q))) := by ring
      _ = balancedLambda*contactWeight e*exp (balancedZ e-(p/tau)*contactDelta q e.1 (contactNext e)) := by
        rw [←Real.exp_add]
        congr 2
        unfold balancedX
        ring
      _ = (balancedLambda*contactWeight e*exp (balancedZ e))*
          exp (-(p/tau)*contactDelta q e.1 (contactNext e)) := by
        rw [Real.exp_sub,neg_mul,Real.exp_neg]
        ring
      _ = _ := by rw [hbal,one_mul]
  rw [Finset.mul_sum]
  have hsum : (∑ e : ContactIndex, exp (-(p/tau)*contactDelta q e.1 (contactNext e))) ≤
      ∑ e : ContactIndex, tau^p*(squaredDistance (orthographicChart q) e.1 (contactNext e))^(-p) := by
    apply Finset.sum_le_sum
    intro e _
    have hsep := (balanced_energy_distinct_chart q hq).2 _ _ (contactNext_ne e)
    have hd : 0<squaredDistance (orthographicChart q) e.1 (contactNext e) := by
      unfold squaredDistance
      nlinarith
    exact rpow_exp_linear_lower p _ hp hd
  have hleft : (∑ e : ContactIndex, balancedLambda*exp (-balancedMean p q)*
      (contactWeight e*exp (-(balancedX p q e-balancedMean p q))))=
      ∑ e : ContactIndex, exp (-(p/tau)*contactDelta q e.1 (contactNext e)) := by
    apply Finset.sum_congr rfl
    intro e _
    simpa only [mul_assoc] using heq e
  rw [hleft]
  refine hsum.trans ?_
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (contact_sum_le_energy p _) (Real.rpow_nonneg tau_pos.le p)

#print axioms balanced_energy_exponential_lower
end Blueprint.Thomson.Tail.Implementation
