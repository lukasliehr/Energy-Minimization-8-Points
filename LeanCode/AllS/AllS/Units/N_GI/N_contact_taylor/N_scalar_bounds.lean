import AllS.Units.N_GI.N_contact_taylor.N_radical_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactH (r : ℝ) : ℝ := packingHeight*r^2/(4*(1-r^2))+
  √(2*(1-packingHeight^2))*r/(1+√(1-r^2))
def contactGamma (r : ℝ) : ℝ := 1+
  (2*packingHeight+√(2*(1-packingHeight^2))*r)/(1+√(1-r^2))

theorem contact_packing_bounds : 13/50 < packingHeight ∧ packingHeight < 4/15 ∧
    0 ≤ 1-packingHeight^2 ∧ √(2*(1-packingHeight^2)) < 137/100 := by
  have ha : 13/50 < packingHeight := Blueprint.Thomson.Finite.packing_endpoint_bounds.1
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hau : packingHeight < 4/15 := by
    dsimp [packingHeight]
    have hh : √(2:ℝ) < 43/30 := by nlinarith
    linarith
  have hbase : 0 ≤ 1-packingHeight^2 := by nlinarith
  have hcs := Real.sq_sqrt (show 0 ≤ 2*(1-packingHeight^2) by positivity)
  have hc0 := Real.sqrt_nonneg (2*(1-packingHeight^2))
  exact ⟨ha,hau,hbase,by nlinarith⟩

theorem contact_scalar_bounds (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 3/10) :
    contactH r < 11/50 ∧ contactGamma r < 3/2 := by
  obtain ⟨ha,hau,hbase,hC⟩ := contact_packing_bounds
  have hs2 := Real.sq_sqrt (show 0 ≤ 1-r^2 by nlinarith)
  have hs0 := Real.sqrt_nonneg (1-r^2)
  have hs : 19/20 < √(1-r^2) := by nlinarith
  have hden : 0 < 1-r^2 := by nlinarith
  have hC0 := Real.sqrt_nonneg (2*(1-packingHeight^2))
  have hrr : r^2 ≤ 9/100 := by nlinarith
  have hnum : packingHeight*r^2 ≤ (4/15)*(9/100) :=
    mul_le_mul hau.le hrr (sq_nonneg r) (by norm_num)
  have hnum2 : √(2*(1-packingHeight^2))*r ≤ (137/100)*(3/10) :=
    mul_le_mul hC.le hr hr0 (by norm_num)
  have h1 : packingHeight*r^2/(4*(1-r^2)) ≤ 3/455 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have h2 : √(2*(1-packingHeight^2))*r/(1+√(1-r^2)) < 137/650 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have h3 : (2*packingHeight+√(2*(1-packingHeight^2))*r)/(1+√(1-r^2)) < 1/2 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  constructor
  · dsimp [contactH]; linarith
  · dsimp [contactGamma]; linarith

theorem pair_cubic_bound (u v r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (hs : u^2+v^2 ≤ r^2) :
    u^2*v+v^2*u ≤ r*(u^2+v^2)/√2 := by
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsum : u+v ≤ √2*r := by
    have h0 : 0 ≤ √2*r := mul_nonneg hp.le hr
    nlinarith [sq_nonneg (u-v)]
  have hprod : 2*u*v ≤ u^2+v^2 := by nlinarith [sq_nonneg (u-v)]
  apply (le_div_iff₀ hp).mpr
  have hbound := mul_le_mul hprod hsum (by positivity : 0 ≤ u+v)
    (by positivity : 0 ≤ u^2+v^2)
  have hh := mul_le_mul_of_nonneg_left hbound hp.le
  have he : √2*((u^2+v^2)*(√2*r))=2*r*(u^2+v^2) := by
    linear_combination r*(u^2+v^2)*h2
  rw [he] at hh
  nlinarith

#print axioms contact_scalar_bounds
#print axioms pair_cubic_bound
end Blueprint.Thomson.Tail.Implementation
