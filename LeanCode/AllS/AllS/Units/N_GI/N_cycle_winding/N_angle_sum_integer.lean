import AllS.Units.N_G.N_cycle_decomposition
import AllS.Units.N_G.N_edge_cost
import Lean_Code.TangentCircle

noncomputable section
open Real
open scoped BigOperators
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cross_norm_projectionRadius (u x : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) :
    ‖crossVec u x‖=projectionRadius u x := by
  have hc := crossVec_norm_sq u x
  rw [hu,hx] at hc
  have hr := projectionRadius_sq u x hu hx
  dsimp [projectionHeight] at hr
  have hn : 0 ≤ projectionRadius u x := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (crossVec u x)]

theorem projection_phase_triple (u x y : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (hrx : 0 < projectionRadius u x) (hry : 0 < projectionRadius u y) :
    inner ℝ u (crossVec x y)=projectionRadius u x*projectionRadius u y*
      sin (contactPhase u y-contactPhase u x) := by
  have hxn : crossVec u x ≠ 0 := norm_ne_zero_iff.mp (by rw [cross_norm_projectionRadius u x hu hx]; exact hrx.ne')
  have hyn : crossVec u y ≠ 0 := norm_ne_zero_iff.mp (by rw [cross_norm_projectionRadius u y hu hy]; exact hry.ne')
  have ht := tangentPhase_triple u (sphereTangent u x) (sphereTangent u y) hu
    (sphereTangent_unit u x hu hx hxn) (sphereTangent_unit u y hu hy hyn)
    (sphereTangent_perp u x hu) (sphereTangent_perp u y hu)
  change inner ℝ (crossVec (sphereTangent u x) (sphereTangent u y)) u=
    sin (contactPhase u y-contactPhase u x) at ht
  simp only [sphereTangent,crossVec_smul_left,crossVec_smul_right,inner_smul_left,
    starRingEnd_apply,star_trivial,cross_projection_triple,
    cross_norm_projectionRadius u x hu hx,cross_norm_projectionRadius u y hu hy] at ht
  rw [← real_inner_comm u (crossVec x y)]
  calc
    _ = projectionRadius u x*projectionRadius u y*
      ((projectionRadius u y)⁻¹*((projectionRadius u x)⁻¹*inner ℝ (crossVec x y) u)) := by
      field_simp [hrx.ne',hry.ne']
    _ = _ := congrArg (fun t => projectionRadius u x*projectionRadius u y*t) ht

theorem projection_phase_inner (u x y : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (hrx : 0 < projectionRadius u x) (hry : 0 < projectionRadius u y) :
    inner ℝ x y-projectionHeight u x*projectionHeight u y=
      projectionRadius u x*projectionRadius u y*cos (contactPhase u y-contactPhase u x) := by
  have hxn : crossVec u x ≠ 0 := norm_ne_zero_iff.mp (by rw [cross_norm_projectionRadius u x hu hx]; exact hrx.ne')
  have hyn : crossVec u y ≠ 0 := norm_ne_zero_iff.mp (by rw [cross_norm_projectionRadius u y hu hy]; exact hry.ne')
  have ht := tangentPhase_inner u (sphereTangent u x) (sphereTangent u y) hu
    (sphereTangent_unit u x hu hx hxn) (sphereTangent_unit u y hu hy hyn)
    (sphereTangent_perp u x hu) (sphereTangent_perp u y hu)
  change inner ℝ (sphereTangent u x) (sphereTangent u y)=cos (contactPhase u x-contactPhase u y) at ht
  have hc : cos (contactPhase u x-contactPhase u y)=cos (contactPhase u y-contactPhase u x) := by
    rw [Real.cos_sub,Real.cos_sub]
    ring
  rw [hc] at ht
  rw [← ht]
  simp only [sphereTangent,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,
    cross_norm_projectionRadius u x hu hx,cross_norm_projectionRadius u y hu hy,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial]
  rw [real_inner_self_eq_norm_sq,hu]
  rw [← real_inner_comm x u]
  dsimp [projectionHeight]
  field_simp [hrx.ne',hry.ne']
  ring

theorem projection_angle_phase_integer (u x y : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (harea : 0 < inner ℝ u (crossVec x y)) :
    ∃ q : ℤ, (q:ℝ)*(2*π)=contactPhase u y-contactPhase u x-projectionAngle u x y := by
  obtain ⟨hrx,hry,ha0,hapi,hs,hc⟩ := projected_angle_spec u x y hu hx hy harea
  have ht := projection_phase_triple u x y hu hx hy hrx hry
  have hi := projection_phase_inner u x y hu hx hy hrx hry
  have hr : projectionRadius u x*projectionRadius u y ≠ 0 := mul_ne_zero hrx.ne' hry.ne'
  have hsin : sin (contactPhase u y-contactPhase u x)=sin (projectionAngle u x y) := by
    apply mul_left_cancel₀ hr
    exact ht.symm.trans hs
  have hcos : cos (contactPhase u y-contactPhase u x)=cos (projectionAngle u x y) := by
    apply mul_left_cancel₀ hr
    linarith
  apply (Real.cos_eq_one_iff _).mp
  rw [Real.cos_sub,hsin,hcos]
  nlinarith [Real.sin_sq_add_cos_sq (projectionAngle u x y)]

def cycleProjectedAngle (Y : Fin 8 → Point) (u : Point) (C : FlowCycle)
    (i : Fin (C.size+1)) : ℝ := projectionAngle u (Y (C.point i)) (Y (C.point (i+1)))

theorem cycle_winding_angle_sum_integer (Y : Fin 8 → Point) (u : Point) (p : ℝ)
    (hY : IsConfiguration Y) (hu : ‖u‖=1) (C : FlowCycle) (hC : C.Positive (forceFlow p u Y)) :
    ∃ q : ℤ, 1 ≤ q ∧ (∑ i,cycleProjectedAngle Y u C i)=2*π*q := by
  have he (i : Fin (C.size+1)) : ∃ q : ℤ, (q:ℝ)*(2*π)=
      contactPhase u (Y (C.point (i+1)))-contactPhase u (Y (C.point i))-cycleProjectedAngle Y u C i :=
    projection_angle_phase_integer u _ _ hu (hY.1 _) (hY.1 _)
      (forceFlow_pos_area Y u p _ _ (hC i))
  choose q hq using he
  have hsum := congrArg (fun f : Fin (C.size+1) → ℝ => ∑ i,f i) (funext hq)
  have hshift : (∑ i : Fin (C.size+1),contactPhase u (Y (C.point (i+1))))=
      ∑ i : Fin (C.size+1),contactPhase u (Y (C.point i)) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin (C.size+1))) (fun i => contactPhase u (Y (C.point i)))
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,hshift,sub_self,zero_sub] at hsum
  have hangle : (∑ i,cycleProjectedAngle Y u C i)=2*π*(-∑ i,q i : ℤ) := by
    push_cast
    linarith
  have hpos : 0 < ∑ i,cycleProjectedAngle Y u C i := by
    apply Finset.sum_pos
    · intro i hi
      exact (projected_angle_spec u _ _ hu (hY.1 _) (hY.1 _)
        (forceFlow_pos_area Y u p _ _ (hC i))).2.2.1
    · exact Finset.univ_nonempty
  refine ⟨-∑ i,q i,?_,hangle⟩
  have hp : (0:ℝ) < (-∑ i,q i : ℤ) := by nlinarith [Real.pi_pos]
  have hpz : (0:ℤ) < -∑ i,q i := by exact_mod_cast hp
  omega

#check cycle_winding_angle_sum_integer
#print axioms cycle_winding_angle_sum_integer
end Blueprint.Thomson.Tail.Implementation
