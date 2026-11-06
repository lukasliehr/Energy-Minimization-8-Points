import Blueprint.Tail

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem packingHeight_quadratic : 7*packingHeight^2+2*packingHeight-1=0 := by
  have hs : √(2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  unfold packingHeight
  nlinarith

theorem constants_algebra : 0<packingHeight ∧
    packingHeight<packingHeight+33/2000 ∧ packingHeight+33/2000<7/25 ∧
    (7:ℝ)/25<3/10 ∧ (3:ℝ)/10<1/3 := by
  have hs : √(2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have hpos := Real.sqrt_nonneg (2:ℝ)
  have hlo : (7:ℝ)/5<√2 := by nlinarith
  have hup : √(2:ℝ)<283/200 := by nlinarith
  unfold packingHeight
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  norm_num

theorem packingHeight_mem_Ioo : packingHeight∈Set.Ioo (0:ℝ) 1 := by
  have h:=constants_algebra
  exact ⟨h.1,by linarith [h.2.2.1]⟩

theorem tau_pos : 0<tau := by
  unfold tau
  linarith [packingHeight_mem_Ioo.2]

#print axioms constants_algebra
end Blueprint.Thomson.Tail.Implementation
