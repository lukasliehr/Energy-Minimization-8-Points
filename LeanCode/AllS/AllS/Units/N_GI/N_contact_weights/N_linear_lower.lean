import AllS.Units.N_GI.N_contact_weights.N_linear_upper
import AllS.Units.N_GI.N_convex_domain.N_sublevel_bridge

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem tail_log_ceiling : log ceiling<(29:ℝ)/10 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤29/10) 6
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num [ceiling] : 0<ceiling)).mpr
  dsimp [ceiling]
  linarith

theorem tail_log_Cstar (p : ℝ) : log (tailCstar p)=log ceiling+tailEpsilon p := by
  rw [tailCstar,Real.log_mul (by norm_num [ceiling] : ceiling≠0) (Real.exp_pos _).ne',Real.log_exp]

theorem contact_linear_strict_lower (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) : -log (tailCstar p)<contactScaledLinear p q e := by
  obtain ⟨f,hf⟩ := exists_ne e
  have hs := Finset.single_le_sum
    (fun k (_ : k∈(Finset.univ : Finset ContactIndex).erase e)=>(Real.exp_pos (-contactScaledLinear p q k)).le)
    (Finset.mem_erase.mpr ⟨hf,Finset.mem_univ f⟩)
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset ContactIndex))
    (fun k=>exp (-contactScaledLinear p q k)) (Finset.mem_univ e)
  have hlt : exp (-contactScaledLinear p q e)<contactJ p q := by
    dsimp [contactJ]
    linarith [Real.exp_pos (-contactScaledLinear p q f)]
  have hlog := Real.log_lt_log (Real.exp_pos _) (hlt.trans_le hq.2.2)
  rw [Real.log_exp] at hlog
  linarith

theorem contact_weights_linear_lower (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) :
    -log (tailCstar p)<contactScaledLinear p q e ∧
      |(p/tau)*contactDelta q e.1 (contactNext e)|<3 := by
  have hl := contact_linear_strict_lower p hp q hq e
  have hu := contact_weights_linear_upper p hp q hq e
  have he := abs_le.mp (contact_scaled_taylor_error p hp q hq.2.1 e)
  have hε := (tail_epsilon_bounds p hp).2
  have hC := tail_log_ceiling
  rw [tail_log_Cstar] at hl
  refine ⟨contact_linear_strict_lower p hp q hq e,abs_lt.mpr ⟨?_,?_⟩⟩ <;> linarith

#print axioms contact_weights_linear_lower
end Blueprint.Thomson.Tail.Implementation
