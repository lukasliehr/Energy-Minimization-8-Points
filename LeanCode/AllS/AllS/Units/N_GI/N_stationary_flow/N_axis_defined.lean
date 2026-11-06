import AllS.Units.N_G.N_setup
import Lean_Code.SphericalTriangle

noncomputable section
open Real
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

def forceAngle (m : ℝ) : ℝ := arccos (1-m/2)
def forceAxis (Y : Fin 8 → Point) (i j : Fin 8) (m : ℝ) : Point :=
  (sin (forceAngle m))⁻¹ • crossVec (Y i) (Y j)
def orientedArea (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) : ℝ :=
  inner ℝ u (crossVec (Y i) (Y j))

theorem squaredDistance_inner (Y : Fin 8 → Point) (hY : IsConfiguration Y) (i j : Fin 8) :
    squaredDistance Y i j = 2-2*inner ℝ (Y i) (Y j) := by
  simp [squaredDistance,norm_sub_sq_real,hY.1]
  ring

theorem forceAxis_spec (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) (i j : Fin 8)
    (hd : squaredDistance Y i j=m) :
    (0<forceAngle m ∧ forceAngle m<π/2) ∧ 0<sin (forceAngle m) ∧
      ‖forceAxis Y i j m‖=1 ∧
      orientedArea (forceAxis Y i j m) Y i j=sin (forceAngle m) := by
  have hi : inner ℝ (Y i) (Y j)=1-m/2 := by
    rw [squaredDistance_inner Y hY] at hd
    linarith
  have hc0 : (0 : ℝ)<1-m/2 := by linarith
  have hc1 : 1-m/2<(1 : ℝ) := by linarith
  have ht0 : 0<forceAngle m := Real.arccos_pos.mpr hc1
  have ht1 : forceAngle m<π/2 := Real.arccos_lt_pi_div_two.mpr hc0
  have hs : 0<sin (forceAngle m) := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  have hcos : cos (forceAngle m)=1-m/2 :=
    Real.cos_arccos (by linarith) hc1.le
  have hc := SquareAntiprismVerification.crossVec_norm_sq (Y i) (Y j)
  rw [hY.1 i,hY.1 j,hi] at hc
  have htrig := Real.sin_sq_add_cos_sq (forceAngle m)
  rw [hcos] at htrig
  have hn : ‖crossVec (Y i) (Y j)‖=sin (forceAngle m) := by
    nlinarith [norm_nonneg (crossVec (Y i) (Y j))]
  refine ⟨⟨ht0,ht1⟩,hs,?_,?_⟩
  · rw [forceAxis,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),hn]
    exact inv_mul_cancel₀ hs.ne'
  · simp only [orientedArea,forceAxis,inner_smul_left,starRingEnd_apply,star_trivial,
      real_inner_self_eq_norm_sq,hn]
    field_simp

theorem stationary_flow_axis_defined (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (_hp : 0 < p) (_hstat : Stationary p Y)
    (_hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (_hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    (0<forceAngle m ∧ forceAngle m<π/2) ∧ 0<sin (forceAngle m) ∧
      ‖forceAxis Y i₀ j₀ m‖=1 ∧
      orientedArea (forceAxis Y i₀ j₀ m) Y i₀ j₀=sin (forceAngle m) :=
  forceAxis_spec Y hY m hm hmmax i₀ j₀ hd

#check stationary_flow_axis_defined
#print axioms stationary_flow_axis_defined
end Blueprint.Thomson.Tail.Implementation
