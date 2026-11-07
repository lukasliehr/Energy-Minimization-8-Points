import AllS.Units.N_GI.N_contact_spectrum.N_contact_rows
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def tailEpsilon (p : ℝ) : ℝ := (3/2)*contraction^2/(tau*p)
def tailCstar (p : ℝ) : ℝ := ceiling*exp (tailEpsilon p)
def contactScaledLinear (p : ℝ) (q : TangentCoordinates) (e : ContactIndex) : ℝ :=
  p*contactLinear q e.1 (contactNext e)/tau
def contactJ (p : ℝ) (q : TangentCoordinates) : ℝ := ∑ e : ContactIndex, exp (-contactScaledLinear p q e)
def convexTailDomain (p : ℝ) : Set TangentCoordinates :=
  {q | q∈rotationSlice ∧ ‖q‖≤contraction/p ∧ contactJ p q≤tailCstar p}

theorem contactJ_convex (p : ℝ) : ConvexOn ℝ Set.univ (contactJ p) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  change (∑ e : ContactIndex, exp (-contactScaledLinear p (a • x+b • y) e))≤
    a*(∑ e : ContactIndex, exp (-contactScaledLinear p x e))+
      b*(∑ e : ContactIndex, exp (-contactScaledLinear p y e))
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := convexOn_exp.2 (x := -contactScaledLinear p x e) (y := -contactScaledLinear p y e)
    (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  convert! h using 1
  congr 1
  simp only [contactScaledLinear,contactLinear_add,contactLinear_smul_spectrum,smul_eq_mul]
  ring

theorem convex_domain_convexity (p : ℝ) : Convex ℝ (convexTailDomain p) := by
  have hj : Convex ℝ {q : TangentCoordinates | contactJ p q≤tailCstar p} := by
    simpa using (contactJ_convex p).convex_le (tailCstar p)
  have hr : Convex ℝ {q : TangentCoordinates | ‖q‖≤contraction/p} := by
    simpa [Metric.closedBall,dist_zero_right] using convex_closedBall (0:TangentCoordinates) (contraction/p)
  exact rotationSlice.convex.inter (hr.inter hj)

#print axioms convex_domain_convexity
end Blueprint.Thomson.Tail.Implementation
