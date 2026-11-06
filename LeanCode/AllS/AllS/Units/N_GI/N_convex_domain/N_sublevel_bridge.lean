import AllS.Units.N_GI.N_convex_domain.N_convexity
import AllS.Units.N_GI.N_balanced_energy.N_energy_inequality
import AllS.Units.N_GI.N_contact_taylor.N_quadratic_remainder

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem tail_small_radius (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) : ‖q‖≤3/10 := by
  have hp0 : 0<p := by linarith
  have h := (le_div_iff₀ hp0).mp hq
  dsimp [contraction] at h
  nlinarith

theorem contact_scaled_taylor_error (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) (e : ContactIndex) :
    |(p/tau)*contactDelta q e.1 (contactNext e)-contactScaledLinear p q e|≤tailEpsilon p := by
  have hp0 : 0<p := by linarith
  have hc : inner ℝ (packingReference e.1) (packingReference (contactNext e))=packingHeight := by
    rw [packingReference_inner_cyclic,if_neg (contactNext_ne e),if_pos (contactNext_contact e)]
  obtain ⟨h1,h2⟩ := contact_taylor_quadratic_remainder q (tail_small_radius p hp q hq) _ _ hc
  have hbound : ‖q‖^2≤(contraction/p)^2 := by
    have hpos : 0≤contraction/p := hq.trans' (norm_nonneg q)
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (add_nonneg hpos (norm_nonneg q))]
  have herr := mul_le_mul_of_nonneg_left (h1.trans h2) (div_pos hp0 tau_pos).le
  have he : (p/tau)*contactDelta q e.1 (contactNext e)-contactScaledLinear p q e=
      (p/tau)*(contactDelta q e.1 (contactNext e)-contactLinear q e.1 (contactNext e)) := by
    dsimp [contactScaledLinear]
    ring
  rw [he,abs_mul,abs_of_pos (div_pos hp0 tau_pos)]
  calc
    _ ≤ (p/tau)*((3/2)*‖q‖^2) := herr
    _ ≤ (p/tau)*((3/2)*(contraction/p)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by norm_num)) (div_pos hp0 tau_pos).le
    _ = tailEpsilon p := by dsimp [tailEpsilon]; field_simp <;> ring

theorem contactJ_energy_bound (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) :
    contactJ p q≤exp (tailEpsilon p)*tau^p*squaredEnergy p (orthographicChart q) := by
  have hp0 : 0<p := by linarith
  have hq3 := tail_small_radius p hp q hq
  have hs : (∑ e : ContactIndex, exp (-contactScaledLinear p q e))≤
      ∑ e : ContactIndex, exp (tailEpsilon p)*tau^p*
        (squaredDistance (orthographicChart q) e.1 (contactNext e))^(-p) := by
    apply Finset.sum_le_sum
    intro e _
    have herr := (abs_le.mp (contact_scaled_taylor_error p hp q hq e)).2
    have hd : 0<squaredDistance (orthographicChart q) e.1 (contactNext e) := by
      have hsep := (balanced_energy_distinct_chart q hq3).2 _ _ (contactNext_ne e)
      unfold squaredDistance
      nlinarith
    calc
      _ ≤ exp (tailEpsilon p-(p/tau)*contactDelta q e.1 (contactNext e)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = exp (tailEpsilon p)*exp (-(p/tau)*contactDelta q e.1 (contactNext e)) := by
        rw [sub_eq_add_neg,Real.exp_add]
        congr 2
        ring
      _ ≤ exp (tailEpsilon p)*(tau^p*(squaredDistance (orthographicChart q) e.1 (contactNext e))^(-p)) :=
        mul_le_mul_of_nonneg_left (rpow_exp_linear_lower p _ hp0 hd) (Real.exp_pos _).le
      _ = _ := by ring
  apply hs.trans
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (contact_sum_le_energy p _)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg tau_pos.le p))

/-- The small-radius inclusion; the annulus theorem supplies this radius for
every localized energy sublevel point in the final parent assembly. -/
theorem convexDomain_of_small_sublevel (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hV : q∈rotationSlice) (hq : ‖q‖≤contraction/p)
    (hE : tau^p*squaredEnergy p (orthographicChart q)≤ceiling) : q∈convexTailDomain p := by
  refine ⟨hV,hq,?_⟩
  have h := mul_le_mul_of_nonneg_left hE (Real.exp_pos (tailEpsilon p)).le
  have hj := contactJ_energy_bound p hp q hq
  dsimp [tailCstar]
  nlinarith

#print axioms contactJ_energy_bound
#print axioms convexDomain_of_small_sublevel
end Blueprint.Thomson.Tail.Implementation
