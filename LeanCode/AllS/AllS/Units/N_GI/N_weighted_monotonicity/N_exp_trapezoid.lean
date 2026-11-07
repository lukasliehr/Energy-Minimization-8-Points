import AllS.Units.N_GI.N_weighted_monotonicity.N_coefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem cosh_sinh_gap_positive (h : ℝ) (hh : 0 < h) : 0 < h*cosh h-sinh h := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => t*cosh t-sinh t) (x*sinh x) x := by
    have he := ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)
    convert! he using 1 <;> simp <;> ring
  have hmono : StrictMonoOn (fun t : ℝ => t*cosh t-sinh t) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici,Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    exact mul_pos hx (Real.sinh_pos_iff.mpr hx)
  have he := hmono (show (0:ℝ) ∈ Set.Ici 0 by simp) hh.le hh
  simpa using he

theorem exp_trapezoid_strict (x y : ℝ) (hxy : x < y) :
    0 < exp x-exp y+(y-x)/2*(exp x+exp y) := by
  let m := (x+y)/2
  let h := (y-x)/2
  have hh : 0 < h := by dsimp [h]; linarith
  have hp := cosh_sinh_gap_positive h hh
  have hplus : exp m*exp h=exp y := by
    rw [← Real.exp_add]
    congr 1
    dsimp [m,h]; ring
  have hminus : exp m*exp (-h)=exp x := by
    rw [← Real.exp_add]
    congr 1
    dsimp [m,h]; ring
  have he : exp x-exp y+h*(exp x+exp y)=2*exp m*(h*cosh h-sinh h) := by
    rw [Real.cosh_eq,Real.sinh_eq,← hplus,← hminus]
    ring
  change 0 < exp x-exp y+h*(exp x+exp y)
  rw [he]
  positivity

#print axioms cosh_sinh_gap_positive
#print axioms exp_trapezoid_strict
end Blueprint.Thomson.Tail.Implementation
