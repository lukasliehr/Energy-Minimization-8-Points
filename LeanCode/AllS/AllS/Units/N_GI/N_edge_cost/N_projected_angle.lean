import AllS.Units.N_G.N_stationary_flow
import Lean_Code.SphericalStrictMetric

noncomputable section
open Real
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

def projectionHeight (u x : Point) : ℝ := inner ℝ u x
def projectionRadius (u x : Point) : ℝ := sqrt (1-(projectionHeight u x)^2)
def projectionAngle (u x y : Point) : ℝ :=
  arccos ((inner ℝ x y-projectionHeight u x*projectionHeight u y)/
    (projectionRadius u x*projectionRadius u y))

theorem projectionRadius_sq (u x : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) :
    (projectionRadius u x)^2=1-(projectionHeight u x)^2 := by
  have h : |inner ℝ u x| ≤ 1 := by simpa [hu,hx] using abs_real_inner_le_norm u x
  have hsq : (projectionHeight u x)^2 ≤ 1 := by
    have hh := mul_self_le_mul_self (abs_nonneg (inner ℝ u x)) h
    simpa [projectionHeight,sq_abs,← pow_two] using hh
  exact Real.sq_sqrt (by linarith)

theorem projected_angle_spec (u x y : Point) (hu : ‖u‖=1) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (harea : 0 < inner ℝ u (crossVec x y)) :
    0 < projectionRadius u x ∧ 0 < projectionRadius u y ∧
    0 < projectionAngle u x y ∧ projectionAngle u x y < π ∧
    inner ℝ u (crossVec x y)=projectionRadius u x*projectionRadius u y*sin (projectionAngle u x y) ∧
    inner ℝ x y=projectionRadius u x*projectionRadius u y*cos (projectionAngle u x y)+
      projectionHeight u x*projectionHeight u y := by
  let b := inner ℝ x y-projectionHeight u x*projectionHeight u y
  let r := projectionRadius u x*projectionRadius u y
  let δ := inner ℝ u (crossVec x y)
  have hg := SquareAntiprismVerification.unit_triple_gram_identity x y u hx hy hu
  rw [← real_inner_comm (crossVec x y) u,← real_inner_comm y u,← real_inner_comm x u] at hg
  have he : δ^2+b^2=r^2 := by
    dsimp [r]
    rw [mul_pow,projectionRadius_sq u x hu hx,projectionRadius_sq u y hu hy]
    dsimp [δ,b,projectionHeight]
    nlinarith [hg]
  have hr0 : 0 ≤ r := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hr : 0 < r := by
    have hd : 0 < δ^2 := sq_pos_of_pos harea
    nlinarith [sq_nonneg b]
  have hrx : 0 < projectionRadius u x := pos_of_mul_pos_left hr (Real.sqrt_nonneg _)
  have hry : 0 < projectionRadius u y := pos_of_mul_pos_right hr (Real.sqrt_nonneg _)
  have hb : -r < b ∧ b < r := by
    have hd : 0 < δ^2 := sq_pos_of_pos harea
    constructor <;> nlinarith [sq_nonneg (b+r),sq_nonneg (b-r)]
  have hq : -1 < b/r ∧ b/r < 1 := by
    constructor
    · apply (lt_div_iff₀ hr).mpr
      simpa using hb.1
    · apply (div_lt_iff₀ hr).mpr
      simpa using hb.2
  have ha0 : 0 < projectionAngle u x y := Real.arccos_pos.mpr hq.2
  have hapi : projectionAngle u x y < π := Real.arccos_lt_pi.mpr hq.1
  have hcos : r*cos (projectionAngle u x y)=b := by
    rw [projectionAngle,Real.cos_arccos hq.1.le hq.2.le]
    change r*(b/r)=b
    field_simp
  have hs : 0 < sin (projectionAngle u x y) := Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsum : (r*sin (projectionAngle u x y))^2+b^2=r^2 := by
    rw [← hcos]
    calc
      _ = r^2*(sin (projectionAngle u x y)^2+cos (projectionAngle u x y)^2) := by ring
      _ = r^2 := by rw [Real.sin_sq_add_cos_sq]; ring
  have hsin : δ=r*sin (projectionAngle u x y) := by
    have hprod := mul_pos hr hs
    nlinarith
  refine ⟨hrx,hry,ha0,hapi,hsin,?_⟩
  change inner ℝ x y=r*cos (projectionAngle u x y)+projectionHeight u x*projectionHeight u y
  rw [hcos]
  dsimp [b]
  ring

theorem edge_cost_projected_angle (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ i j : Fin 8) (hY : IsConfiguration Y) (_hp : 0 < p) (_hstat : Stationary p Y)
    (_hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (_hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (harea : 0 < orientedArea (forceAxis Y i₀ j₀ m) Y i j) :
    let u := forceAxis Y i₀ j₀ m
    0 < projectionRadius u (Y i) ∧ 0 < projectionRadius u (Y j) ∧
    0 < projectionAngle u (Y i) (Y j) ∧ projectionAngle u (Y i) (Y j) < π ∧
    orientedArea u Y i j=projectionRadius u (Y i)*projectionRadius u (Y j)*sin (projectionAngle u (Y i) (Y j)) ∧
    inner ℝ (Y i) (Y j)=projectionRadius u (Y i)*projectionRadius u (Y j)*cos (projectionAngle u (Y i) (Y j))+
      projectionHeight u (Y i)*projectionHeight u (Y j) :=
  projected_angle_spec _ _ _ (forceAxis_spec Y hY m hm hmmax i₀ j₀ hd).2.2.1 (hY.1 i) (hY.1 j) harea

#check edge_cost_projected_angle
#print axioms edge_cost_projected_angle
end Blueprint.Thomson.Tail.Implementation
