import AllS.Units.N_GI.N_balanced_energy.N_reference_data
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem tail_geometric_constants :
    (261:ℝ)/1000<packingHeight ∧ packingHeight<262/1000 ∧
    (147759:ℝ)/10^5<tau ∧ tau<1847/1250 ∧
    (17071065:ℝ)/10^7<contactKappa ∧ contactKappa<1707107/10^6 ∧
    (5414213:ℝ)/250000<contactTotalWeight ∧ contactTotalWeight<216569/10^4 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hlo : (141421356:ℝ)/10^8<√2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hup : √(2:ℝ)<(141421357:ℝ)/10^8 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  rw [contactKappa_formula]
  dsimp [packingHeight,tau,contactTotalWeight]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem tail_log_constants : (534799:ℝ)/10^6<log contactKappa ∧ log contactKappa<534801/10^6 := by
  obtain ⟨_,_,_,_,hkl,hku,_,_⟩ := tail_geometric_constants
  have hl := Real.sum_range_le_log_div (x := (1414213:ℝ)/5414213) (by norm_num) (by norm_num) 8
  have hu := Real.log_div_le_sum_range_add (x := (707107:ℝ)/2707107) (by norm_num) (by norm_num) 8
  have hlm := Real.log_lt_log (by norm_num : (0:ℝ)<17071065/10^7) hkl
  have hum := Real.log_lt_log (by linarith : 0<contactKappa) hku
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith

theorem tail_d_constants :
    (197553:ℝ)/10^6<balancedD ∧ balancedD<197556/10^6 ∧
    (9877:ℝ)/50000<balancedD ∧ balancedD<4939/25000 ∧
    (843:ℝ)/2500<contactKappa*balancedD ∧ contactKappa*balancedD<1349/4000 := by
  obtain ⟨_,_,_,_,hkl,hku,_,_⟩ := tail_geometric_constants
  obtain ⟨hl,hu⟩ := tail_log_constants
  have hden : 0<contactKappa+1 := by linarith
  have hd : (contactKappa+1)*balancedD=log contactKappa := by unfold balancedD; field_simp
  have hdl : (197553:ℝ)/10^6<balancedD := by
    unfold balancedD
    apply (lt_div_iff₀ hden).mpr
    linarith
  have hdu : balancedD<(197556:ℝ)/10^6 := by
    unfold balancedD
    apply (div_lt_iff₀ hden).mpr
    linarith
  exact ⟨hdl,hdu,by linarith,by linarith,by nlinarith,by nlinarith⟩

theorem tail_lambda_constants :
    (71373:ℝ)/10^5<balancedLambda ∧ (7137:ℝ)/10^4<balancedLambda ∧
    balancedLambda<3569/5000 ∧ balancedLambda<357/500 := by
  obtain ⟨_,_,_,_,hkdL,hkdU⟩ := tail_d_constants
  have hl := Real.exp_bound (x := -(1349:ℝ)/4000) (by norm_num) (n := 8) (by norm_num)
  have hu := Real.exp_bound (x := -(843:ℝ)/2500) (by norm_num) (n := 8) (by norm_num)
  have hlm : exp (-(1349:ℝ)/4000)<balancedLambda := Real.exp_lt_exp.mpr (by linarith)
  have hum : balancedLambda<exp (-(843:ℝ)/2500) := Real.exp_lt_exp.mpr (by linarith)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl hu
  obtain ⟨hl1,hl2⟩ := abs_le.mp hl
  obtain ⟨hu1,hu2⟩ := abs_le.mp hu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem tail_Cmin_constants :
    (15457:ℝ)/1000<balancedLambda*contactTotalWeight ∧ balancedLambda*contactTotalWeight<15459/1000 := by
  obtain ⟨_,_,_,_,_,_,hWL,hWU⟩ := tail_geometric_constants
  obtain ⟨hl,_,hu,_⟩ := tail_lambda_constants
  have h1 := mul_pos (sub_pos.mpr hl) (sub_pos.mpr hWL)
  have h2 := mul_pos (sub_pos.mpr hu) (sub_pos.mpr hWU)
  constructor <;> nlinarith

#print axioms tail_geometric_constants
#print axioms tail_log_constants
#print axioms tail_d_constants
#print axioms tail_lambda_constants
#print axioms tail_Cmin_constants
end Blueprint.Thomson.Tail.Implementation
