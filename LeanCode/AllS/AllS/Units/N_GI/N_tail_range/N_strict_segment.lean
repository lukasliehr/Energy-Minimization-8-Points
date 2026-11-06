import AllS.Units.N_G.N_full_hessian
import AllS.Units.N_G.N_stationary_chart
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Real Set
namespace Blueprint.Thomson.Tail.Implementation

theorem energy_line_second_derivative_at (p : ℝ) (q ξ : TangentCoordinates) (t : ℝ)
    (hq : ‖q+t • ξ‖<3/10) :
    HasDerivAt (deriv (fun u : ℝ=>squaredEnergy p (orthographicChart (q+u • ξ))))
      (energySecond p (q+t • ξ) ξ) t := by
  let g : ℝ→ℝ := fun u=>squaredEnergy p (orthographicChart (q+u • ξ))
  have h0 := energy_line_second_derivative p (q+t • ξ) ξ hq
  have he : (fun u : ℝ=>squaredEnergy p (orthographicChart (q+t • ξ+u • ξ)))=
      fun u : ℝ=>g (t+u) := by
    funext u
    dsimp [g]
    have hv : q+t • ξ+u • ξ=q+(t+u) • ξ := by module
    rw [hv]
  rw [he] at h0
  have hshift : deriv (fun u : ℝ=>g (t+u))=(fun u : ℝ=>deriv g (t+u)) :=
    funext (fun u=>deriv_comp_const_add g t u)
  rw [hshift] at h0
  have h : HasDerivAt (fun u : ℝ=>deriv g (t+u)) (energySecond p (q+t • ξ) ξ) (t-t) := by
    simpa using h0
  have hh := HasDerivAt.comp_sub_const t t h
  have heq : (fun u : ℝ=>deriv g (t+(u-t)))=deriv g := by
    funext u
    congr 1
    ring
  rw [heq] at hh
  exact hh

theorem strict_minimum_from_second_derivative (g : ℝ→ℝ)
    (hg : ∀ t∈Icc (0:ℝ) 1, DifferentiableAt ℝ g t)
    (hg' : ∀ t∈Icc (0:ℝ) 1, DifferentiableAt ℝ (deriv g) t)
    (hg'' : ∀ t∈Ioo (0:ℝ) 1, 0<deriv (deriv g) t)
    (hzero : deriv g 0=0) : g 0<g 1 := by
  have hm' : StrictMonoOn (deriv g) (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact (hg' t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact hg'' t (by simpa only [interior_Icc] using ht)
  have hm : StrictMonoOn g (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t∈Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
      have h := hm' (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) ⟨ht'.1.le,ht'.2.le⟩ ht'.1
      simpa only [hzero] using h
  exact hm (by norm_num) (by norm_num) (by norm_num)

theorem convexTailDomain_line_mem (p : ℝ) (q z : TangentCoordinates)
    (hq : q∈convexTailDomain p) (hz : z∈convexTailDomain p) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    q+t • (z-q)∈convexTailDomain p := by
  have h := convex_domain_convexity p hq hz (sub_nonneg.mpr ht.2) ht.1 (show (1-t)+t=1 by ring)
  have he : q+t • (z-q)=(1-t) • q+t • z := by module
  rwa [he]

theorem tail_range_strict_segment (p a : ℝ) (hp : (97:ℝ)/2≤p) (ha : a∈Ioo (0:ℝ) 1)
    (hF : F (2*p) a=0) (qh q : TangentCoordinates)
    (hqh : qh∈convexTailDomain p) (hq : q∈convexTailDomain p)
    (hc : Thomson.Congruent (orthographicChart qh) (X a)) :
    squaredEnergy p (orthographicChart qh)≤ squaredEnergy p (orthographicChart q) ∧
    (squaredEnergy p (orthographicChart qh)=squaredEnergy p (orthographicChart q) ↔ q=qh) := by
  by_cases he : q=qh
  · subst q
    simp
  have hξ : q-qh∈rotationSlice := rotationSlice.sub_mem hq.1 hqh.1
  have hξ0 : q-qh≠0 := sub_ne_zero.mpr he
  have hline (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : qh+t • (q-qh)∈convexTailDomain p :=
    convexTailDomain_line_mem p qh q hqh hq t ht
  let g : ℝ→ℝ := fun t=>squaredEnergy p (orthographicChart (qh+t • (q-qh)))
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : DifferentiableAt ℝ g t :=
    (energy_line_hasDerivAt p qh (q-qh) t (convexTailDomain_norm_lt p hp _ (hline t ht)).le).differentiableAt
  have hsecond (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (deriv g) (energySecond p (qh+t • (q-qh)) (q-qh)) t :=
    energy_line_second_derivative_at p qh (q-qh) t (convexTailDomain_norm_lt p hp _ (hline t ht))
  have hz : deriv g 0=0 :=
    (stationary_chart_chart_zero p a ha hF qh (q-qh) (by linarith [convexTailDomain_norm_lt p hp qh hqh]) hc).deriv
  have hstrict : g 0<g 1 := by
    apply strict_minimum_from_second_derivative g hg (fun t ht=>(hsecond t ht).differentiableAt) ?_ hz
    intro t ht
    rw [(hsecond t ⟨ht.1.le,ht.2.le⟩).deriv]
    exact energySecond_pos p hp _ _ (hline t ⟨ht.1.le,ht.2.le⟩) hξ hξ0
  have hg0 : g 0=squaredEnergy p (orthographicChart qh) := by simp [g]
  have hg1 : g 1=squaredEnergy p (orthographicChart q) := by
    simp only [g,one_smul]
    have hv : qh+(q-qh)=q := by module
    rw [hv]
  rw [hg0,hg1] at hstrict
  exact ⟨hstrict.le,iff_of_false (ne_of_lt hstrict) he⟩

#print axioms tail_range_strict_segment
end Blueprint.Thomson.Tail.Implementation
