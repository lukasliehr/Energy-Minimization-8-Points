import AllS.Units.N_GI.N_contact_weights.N_jensen
import AllS.Units.N_GI.N_contact_weights.N_jensen_surplus

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_weights_linear_upper (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) : contactScaledLinear p q e<119/100 := by
  by_contra hn
  have hle : (119:ℝ)/100≤contactScaledLinear p q e := le_of_not_gt hn
  obtain ⟨_,_,_,_,hkL,hkU,_,hWU⟩ := tail_geometric_constants
  obtain ⟨_,_,_,_,_,hkdU⟩ := tail_d_constants
  have hw : contactWeight e<contactTotalWeight := by
    have hWP : (20:ℝ)<contactTotalWeight := by
      obtain ⟨_,_,_,_,_,_,h,_⟩ := tail_geometric_constants
      linarith
    unfold contactWeight
    split_ifs <;> linarith
  have hx : jensenU≤contactLinearBalancedX p q e := by
    dsimp [contactLinearBalancedX,balancedZ,jensenU]
    split_ifs
    · linarith
    · linarith [balancedD_pos]
  have hj := weighted_exp_isolate (contactLinearBalancedX p q) (contactLinearBalancedX_mean p q) e hw
  have hs := jensen_surplus_lower contactTotalWeight (contactWeight e) (contactLinearBalancedX p q e)
    (contactWeight_ge_one e) hw (by dsimp [jensenW]; linarith) hx
  have h := mul_le_mul_of_nonneg_left (hs.trans hj) (Real.exp_pos (-contactKappa*balancedD)).le
  change balancedLambda*(contactTotalWeight+jensenSurplus)≤
    balancedLambda*(∑ f : ContactIndex, contactWeight f*exp (-contactLinearBalancedX p q f)) at h
  rw [←contactJ_balanced] at h
  have hC := (tail_Cstar_upper p hp).2
  have hJ := hq.2.2
  linarith [jensen_common_strict]

#print axioms contact_weights_linear_upper
end Blueprint.Thomson.Tail.Implementation
