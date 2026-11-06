import AllS.Units.N_GI.N_packing_entry.N_minimum_attained
import AllS.Units.N_GI.N_constants.N_algebra

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem forceFactor_entry_lower : (6469:ℝ)/1250<forceFactor entryDistance := by
  obtain ⟨hm0,hmU⟩ := entryDistance_bounds
  have hs0 : 0<√(1-entryDistance/4) := Real.sqrt_pos.mpr (by linarith)
  have hs : (√(1-entryDistance/4))^2=1-entryDistance/4 := Real.sq_sqrt (by linarith)
  have ht := tail_geometric_constants.2.2.1
  have hx : √(1-entryDistance/4)<799283/10^6 := by
    have hrel : entryDistance=tau-33/1000 := rfl
    nlinarith [Real.sqrt_nonneg (1-entryDistance/4)]
  have hy0 : 0≤(1-√(1-entryDistance/4))/2 := by linarith
  have hy := Real.sq_sqrt hy0
  have hyl : (31679:ℝ)/100000<√((1-√(1-entryDistance/4))/2) := by
    nlinarith [Real.sqrt_nonneg ((1-√(1-entryDistance/4))/2)]
  have hnum : (4:ℝ)+8*(31679/100000)<4+8*√((1-√(1-entryDistance/4))/2) := by linarith
  have hd := (div_lt_div_of_pos_left (by norm_num : (0:ℝ)<4+8*(31679/100000)) hs0 hx).trans
    (div_lt_div_of_pos_right hnum hs0)
  have hrat : (6469:ℝ)/1250+3<(4+8*(31679/100000))/(799283/10^6) := by norm_num
  dsimp [forceFactor]
  linarith

theorem entry_ratio_lower : 1+(165:ℝ)/7223≤tau/entryDistance := by
  apply (le_div_iff₀ entryDistance_bounds.1).mpr
  have h := tail_geometric_constants.2.2.2.1
  dsimp [entryDistance]
  linarith

theorem entry_rpow_lower (p : ℝ) (hp : (97:ℝ)/2≤p) :
    ((1+(165:ℝ)/7223)^48)*((422113787:ℝ)/417373832)≤(tau/entryDistance)^p := by
  let b : ℝ := 1+165/7223
  have hb : 0<b := by norm_num [b]
  have hs : ((422113787:ℝ)/417373832)≤√b := by
    have h := Real.sq_sqrt hb.le
    have hn := Real.sqrt_nonneg b
    dsimp [b] at h hn
    nlinarith
  have he : b^((97:ℝ)/2)=b^48*√b := by
    rw [show (97:ℝ)/2=(48:ℝ)+(1/2) by norm_num,Real.rpow_add hb,←Real.sqrt_eq_rpow]
    norm_num
  have hpow : b^((97:ℝ)/2)≤(tau/entryDistance)^p :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num [b] : 1≤b) hp).trans
      (Real.rpow_le_rpow hb.le entry_ratio_lower (by linarith : 0≤p))
  rw [he] at hpow
  exact (mul_le_mul_of_nonneg_left hs (pow_nonneg hb.le 48)).trans hpow

theorem force_entry_strict (p : ℝ) (hp : (97:ℝ)/2≤p) :
    (619:ℝ)/40<forceFactor entryDistance*(tau/entryDistance)^p := by
  have hpow := entry_rpow_lower p hp
  have hf := forceFactor_entry_lower
  have hpR : 0<(tau/entryDistance)^p := Real.rpow_pos_of_pos (div_pos tau_pos entryDistance_bounds.1) p
  have hmul := (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤6469/1250)).trans_lt
    (mul_lt_mul_of_pos_right hf hpR)
  have he : (619:ℝ)/40<((6469:ℝ)/1250)*(((1+(165:ℝ)/7223)^48)*((422113787:ℝ)/417373832)) := by norm_num
  exact he.trans hmul

#print axioms force_entry_strict
end Blueprint.Thomson.Tail.Implementation
