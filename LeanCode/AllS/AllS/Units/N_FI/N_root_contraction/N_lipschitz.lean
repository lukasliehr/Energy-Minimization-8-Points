import AllS.Units.N_FI.N_root_contraction.N_derivative_T
import AllS.Units.N_FI.N_root_contraction.N_derivative_height

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

theorem rootT_lipschitz (q v w : ℝ) (m : ℕ) (hm : 1 ≤ m) (hmq : (m:ℝ) ≤ q)
    (hv : v ∈ Set.Icc 0 rootC) (hw : w ∈ Set.Icc 0 rootC) :
    |rootT q v-rootT q w| ≤ rootLambda m*|v-w| := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc 0 rootC) := rootT_derivative_bound q x m hm hmq hx.1
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) rootC).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hd x hx).1.hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using (hd x hx).2) hw hv

theorem rootHeight_lipschitz (q q₀ v w : ℝ) (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q)
    (hv : v ∈ Set.Icc 0 rootC) (hw : w ∈ Set.Icc 0 rootC) :
    |rootHeight q v-rootHeight q w| ≤ (5/(17*q₀))*|v-w| := by
  have hd (x : ℝ) := root_contraction_derivative_height q q₀ x hq₀ hq
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) rootC).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _hx => (hd x).1.hasDerivWithinAt)
      (fun x _hx => by simpa only [Real.norm_eq_abs,abs_of_pos (hd x).2.1] using (hd x).2.2) hw hv

theorem root_contraction_lipschitz (q q₀ v w : ℝ) (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q)
    (hv : v ∈ Set.Icc 0 rootC) (hw : w ∈ Set.Icc 0 rootC) :
    |rootT q v-rootT q w| ≤ rootLambda ⌊q₀⌋₊*|v-w| ∧
      |rootHeight q v-rootHeight q w| ≤ 5*|v-w|/(17*q₀) := by
  refine ⟨rootT_lipschitz q v w ⌊q₀⌋₊ (Nat.le_floor (by simpa using hq₀))
    ((Nat.floor_le (by linarith : 0 ≤ q₀)).trans hq) hv hw,?_⟩
  convert rootHeight_lipschitz q q₀ v w hq₀ hq hv hw using 1 <;> ring

#check root_contraction_lipschitz
#print axioms root_contraction_lipschitz
end Blueprint.Thomson.Finite
