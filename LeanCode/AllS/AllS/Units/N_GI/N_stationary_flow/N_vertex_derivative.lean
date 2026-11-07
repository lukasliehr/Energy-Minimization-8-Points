import AllS.Units.N_GI.N_stationary_flow.N_axis_defined
import AllS.Units.N_GI.N_upstream_bridge.N_energy
import Lean_Code.StationarityCalculus
import Lean_Code.LocalChart
import Lean_Code.CrossAlgebra

noncomputable section
open Real
open scoped BigOperators
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

/-- The existing sphere chart has the same first variation as rotation. -/
def tangentRay (x v : Point) (t : ℝ) : Point :=
  sqrt (1-t^2*‖v‖^2) • x+t • v

@[simp] theorem tangentRay_zero (x v : Point) : tangentRay x v 0=x := by
  simp [tangentRay]

theorem tangentRay_hasDerivAt (x v : Point) : HasDerivAt (tangentRay x v) v 0 := by
  have hg : HasDerivAt (fun t : ℝ => 1-t^2*‖v‖^2) 0 0 := by
    simpa using (((hasDerivAt_id (𝕜 := ℝ) 0).pow 2).mul_const (‖v‖^2)).const_sub 1
  have hs : HasDerivAt (fun t : ℝ => sqrt (1-t^2*‖v‖^2)) 0 0 := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sqrt
      (x := 1-(0 : ℝ)^2*‖v‖^2) (by norm_num)).comp 0 hg
  have hfirst := hs.smul_const x
  have hsecond := (hasDerivAt_id (𝕜 := ℝ) 0).smul_const v
  convert! hfirst.add hsecond using 1 <;>
    first | rfl | simp [tangentRay,Pi.add_apply]

theorem tangentRay_norm_eventually (x v : Point) (hx : ‖x‖=1)
    (hv : inner ℝ x v=0) : ∀ᶠ t in nhds (0 : ℝ), ‖tangentRay x v t‖=1 := by
  have hc : ContinuousAt (fun t : ℝ => ‖t • v‖) 0 := by fun_prop
  have hn := hc.eventually_lt (continuousAt_const (y := (1 : ℝ))) (by simp)
  filter_upwards [hn] with t ht
  have horth : inner ℝ (t • v) x=0 := by
    rw [real_inner_comm] at hv
    simp [inner_smul_left,hv]
  have h := SquareAntiprismVerification.sphereChart_norm x (t • v) hx horth ht.le
  simpa [SquareAntiprismVerification.sphereChart,tangentRay,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs] using h

theorem stationary_tangent_identity (p : ℝ) (Y : Fin 8 → Point)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (V : Fin 8 → Point) (hV : ∀ i, inner ℝ (Y i) (V i)=0) :
    (∑ i : Fin 8, inner ℝ
      (∑ j : Fin 8 with j≠i, (squaredDistance Y i j)^(-p-1) • Y j) (V i))=0 := by
  let γ : ℝ → Fin 8 → Point := fun t i => tangentRay (Y i) (V i) t
  have hγzero : γ 0=Y := by funext i; exact tangentRay_zero _ _
  have hγ : ∀ i, HasDerivAt (fun t => γ t i) (V i) 0 :=
    fun i => tangentRay_hasDerivAt _ _
  have hn : ∀ᶠ t in nhds (0 : ℝ), ∀ i, ‖γ t i‖=1 :=
    Filter.eventually_all.mpr (fun i => tangentRay_norm_eventually _ _ (hY.1 i) (hV i))
  have hz := hstat γ hγzero (fun i => (hγ i).differentiableAt) hn
  have hd := SquareAntiprismVerification.energy_curve_hasDerivAt p Y V γ hY hγzero hγ
  have heq : (fun t => squaredEnergy p (γ t)) =
      (fun t => SquareAntiprismVerification.E (2*p) (γ t)) := by
    funext t
    exact squaredEnergy_eq_upstream _ _
  rw [heq] at hz
  have hu := hz.unique hd
  rw [SquareAntiprismVerification.pair_tangent_sum Y V (-p-1) hV] at hu
  change 0 = -2*p*(-(∑ i : Fin 8, inner ℝ
      (∑ j : Fin 8 with j≠i, (squaredDistance Y i j)^(-p-1) • Y j) (V i))) at hu
  nlinarith

theorem stationary_oriented_vertex (p : ℝ) (Y : Fin 8 → Point)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (u : Point) (i : Fin 8) :
    (∑ j : Fin 8 with j≠i, (squaredDistance Y i j)^(-p-1)*orientedArea u Y i j)=0 := by
  classical
  let V : Fin 8 → Point := fun k => if k=i then crossVec u (Y i) else 0
  have hV : ∀ k, inner ℝ (Y k) (V k)=0 := by
    intro k
    by_cases hk : k=i
    · subst k
      simp only [V,if_pos rfl]
      rw [real_inner_comm]
      exact SquareAntiprismVerification.crossVec_inner_right _ _
    · simp [V,hk]
  have h := stationary_tangent_identity p Y hY hp hstat V hV
  simp only [V,apply_ite,inner_zero_right] at h
  rw [Finset.sum_ite_eq'] at h
  simp only [Finset.mem_univ,if_true] at h
  rw [sum_inner] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [inner_smul_left,starRingEnd_apply,star_trivial,orientedArea]
  congr 1
  calc
    inner ℝ u (crossVec (Y i) (Y j)) = inner ℝ (crossVec (Y i) (Y j)) u := real_inner_comm _ _
    _ = inner ℝ (crossVec u (Y i)) (Y j) :=
      (SquareAntiprismVerification.triple_cyclic u (Y i) (Y j)).symm
    _ = inner ℝ (Y j) (crossVec u (Y i)) := real_inner_comm _ _

theorem stationary_flow_vertex_derivative (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (_hne : i₀ ≠ j₀) (_hm : 0 < m) (_hmmax : m ≤ 29/20)
    (_hd : squaredDistance Y i₀ j₀=m) (_hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    ∀ i, (∑ j : Fin 8 with j≠i,
      (squaredDistance Y i j)^(-p-1)*orientedArea (forceAxis Y i₀ j₀ m) Y i j)=0 :=
  stationary_oriented_vertex p Y hY hp hstat _

#check stationary_flow_vertex_derivative
#print axioms stationary_flow_vertex_derivative
end Blueprint.Thomson.Tail.Implementation
