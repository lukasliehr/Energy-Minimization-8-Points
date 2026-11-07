import AllS.Units.N_GI.N_cycle_winding.N_angle_sum_integer

noncomputable section
open Real
open scoped BigOperators
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem closest_projection_angle (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (m : ℝ) (i j : Fin 8) (hd : squaredDistance Y i j=m) :
    projectionAngle (forceAxis Y i j m) (Y i) (Y j)=forceAngle m := by
  have hx : projectionHeight (forceAxis Y i j m) (Y i)=0 := by
    simp [projectionHeight,forceAxis,inner_smul_left,crossVec_inner_left]
  have hy : projectionHeight (forceAxis Y i j m) (Y j)=0 := by
    simp [projectionHeight,forceAxis,inner_smul_left,crossVec_inner_right]
  have hi : inner ℝ (Y i) (Y j)=1-m/2 := by
    rw [squaredDistance_inner Y hY] at hd
    linarith
  simp [projectionAngle,projectionRadius,hx,hy,hi,forceAngle]

theorem cycle_angle_sum_lt (Y : Fin 8 → Point) (u : Point) (p : ℝ)
    (hY : IsConfiguration Y) (hu : ‖u‖=1) (C : FlowCycle) (hC : C.Positive (forceFlow p u Y)) :
    (∑ i,cycleProjectedAngle Y u C i) < (C.size+1 : ℕ)*π := by
  calc
    _ < ∑ _i : Fin (C.size+1),π := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i hi
      exact (projected_angle_spec u _ _ hu (hY.1 _) (hY.1 _)
        (forceFlow_pos_area Y u p _ _ (hC i))).2.2.2.1
    _ = _ := by simp

theorem cycle_winding_cases_of_sum (Y : Fin 8 → Point) (u : Point) (p : ℝ)
    (hY : IsConfiguration Y) (hu : ‖u‖=1) (C : FlowCycle) (hC : C.Positive (forceFlow p u Y))
    (q : ℤ) (hq : 1 ≤ q) (hsum : (∑ i,cycleProjectedAngle Y u C i)=2*π*q) :
    ((C.size+1=3 ∨ C.size+1=4) → q=1) ∧ (C.size+1=5 → q=1 ∨ q=2) := by
  have hb := cycle_angle_sum_lt Y u p hY hu C hC
  rw [hsum] at hb
  constructor
  · intro hk
    have hqr : (q:ℝ)<2 := by
      rcases hk with hk|hk <;> rw [hk] at hb <;> norm_num at hb <;> nlinarith [Real.pi_pos]
    have hqz : q<2 := by exact_mod_cast hqr
    omega
  · intro hk
    rw [hk] at hb
    norm_num at hb
    have hqr : (q:ℝ)<3 := by nlinarith [Real.pi_pos]
    have hqz : q<3 := by exact_mod_cast hqr
    omega

theorem cycle_winding_winding_cases (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (C : FlowCycle)
    (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y)) (q : ℤ) (hq : 1 ≤ q)
    (hsum : (∑ i,cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C i)=2*π*q) :
    ((C.size+1=3 ∨ C.size+1=4) → q=1) ∧ (C.size+1=5 → q=1 ∨ q=2) ∧
    (∀ k, C.point k=i₀ → C.point (k+1)=j₀ →
      cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C k=2*(forceAngle m/2)) := by
  obtain ⟨ha,hb⟩ := cycle_winding_cases_of_sum Y _ p hY
    (forceAxis_spec Y hY m hm hmmax i₀ j₀ hd).2.2.1 C hC q hq hsum
  refine ⟨ha,hb,?_⟩
  intro k hk hj
  dsimp [cycleProjectedAngle]
  rw [hk,hj,closest_projection_angle Y hY m i₀ j₀ hd]
  ring

#check cycle_winding_winding_cases
#print axioms cycle_winding_winding_cases
end Blueprint.Thomson.Tail.Implementation
