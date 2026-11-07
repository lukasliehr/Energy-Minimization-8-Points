import AllS.Units.N_GI.N_force_bound.N_sum_cycle_costs

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def forceX (m : ℝ) : ℝ := sqrt (1-m/4)
def forceY (m : ℝ) : ℝ := sqrt ((1-forceX m)/2)
def forceFactorDeriv (m : ℝ) : ℝ :=
  1/(4*(forceX m)^2*forceY m)+(1+2*forceY m)/(2*(forceX m)^3)

theorem force_radical_parameters (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    0 < forceX m ∧ forceX m < 1 ∧ 0 < forceY m ∧ forceY m ≤ 8/25 ∧
    forceX m=1-2*(forceY m)^2 ∧ m=4*(1-(forceX m)^2) := by
  obtain ⟨hx,hx1,hy,hx2,hsx,hsy⟩ := force_trig_parameters m hm hmmax
  have hy2 : (forceY m)^2=(1-forceX m)/2 := Real.sq_sqrt (by dsimp [forceX]; rw [hsx]; linarith)
  have hxx : 399/500 ≤ forceX m := by dsimp [forceX]; rw [hsx]; nlinarith
  have hyy : forceY m ≤ 8/25 := by
    have hn : 0 ≤ forceY m := Real.sqrt_nonneg _
    nlinarith
  refine ⟨by simpa [forceX,hsx] using hx,by simpa [forceX,hsx] using hx1,
    by simpa [forceY,forceX,hsy] using hy,hyy,by linarith,?_⟩
  dsimp [forceX]
  rw [hsx]
  linarith

theorem forceFactor_hasDerivAt (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    HasDerivAt forceFactor (forceFactorDeriv m) m := by
  obtain ⟨hx,hx1,hy,_,_,_⟩ := force_radical_parameters m hm hmmax
  have hdx : HasDerivAt forceX (-1/(8*forceX m)) m := by
    have h := (((hasDerivAt_id m).div_const 4).const_sub 1).sqrt
      (show 1-m/4 ≠ 0 by linarith)
    convert! h using 1
    dsimp [forceX]
    ring
  have hdy : HasDerivAt forceY (1/(32*forceX m*forceY m)) m := by
    have h := ((hdx.const_sub 1).div_const 2).sqrt (show (1-forceX m)/2 ≠ 0 by linarith)
    convert! h using 1
    dsimp [forceY]
    field_simp
    ring
  have h := (((hdy.const_mul 8).const_add 4).div hdx hx.ne').sub_const 3
  convert! h using 1
  dsimp [forceFactorDeriv]
  field_simp
  ring

/-- Exact polynomial form of the logarithmic-derivative estimate. -/
theorem force_derivative_polynomial_pos (y : ℝ) (hy : 0 < y) (hymax : y ≤ 8/25) :
    0 < 3+16*y-10*y^2-104*y^3-44*y^4+112*y^5+72*y^6 := by
  have h2 : y^2 ≤ (8/25)*y := by nlinarith
  have h3 : y^3 ≤ (64/625)*y := by
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le hymax 2) hy.le
    nlinarith
  have h4 : y^4 ≤ (512/15625)*y := by
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le hymax 3) hy.le
    nlinarith
  nlinarith [pow_nonneg hy.le 5,pow_nonneg hy.le 6]

theorem forceFactor_derivative_bound (m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    m*forceFactorDeriv m < (3/2)*forceFactor m := by
  let x := forceX m
  let y := forceY m
  obtain ⟨hx,hx1,hy,hymax,hxy,hmx⟩ := force_radical_parameters m hm hmmax
  have hg : forceFactor m=(4+8*y)/x-3 := rfl
  have hD : 0 < 2*x^3*y := by dsimp [x,y]; positivity
  have hid : 3*x^2*y*(4+8*y-3*x)-m*(x/2+y+2*y^2)=
      y*(3+16*y-10*y^2-104*y^3-44*y^4+112*y^5+72*y^6) := by
    change x=1-2*y^2 at hxy
    change m=4*(1-x^2) at hmx
    rw [hmx,hxy]
    ring
  have hp : 0 < 3*x^2*y*(4+8*y-3*x)-m*(x/2+y+2*y^2) := by
    rw [hid]
    exact mul_pos hy (force_derivative_polynomial_pos y hy hymax)
  apply (mul_lt_mul_iff_left₀ hD).mp
  have heL : m*forceFactorDeriv m*(2*x^3*y)=m*(x/2+y+2*y^2) := by
    dsimp [forceFactorDeriv]
    change m*(1/(4*x^2*y)+(1+2*y)/(2*x^3))*(2*x^3*y)=_
    field_simp [show x ≠ 0 from hx.ne',show y ≠ 0 from hy.ne']
    ring
  have heR : ((3/2)*forceFactor m)*(2*x^3*y)=3*x^2*y*(4+8*y-3*x) := by
    rw [hg]
    field_simp [show x ≠ 0 from hx.ne'] <;> ring
  rw [heL,heR]
  linarith

theorem forceEnergy_hasDerivAt (p m : ℝ) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    HasDerivAt (fun x => forceFactor x*x^(-p))
      (m^(-p-1)*(m*forceFactorDeriv m-p*forceFactor m)) m := by
  have h := (forceFactor_hasDerivAt m hm hmmax).mul
    (Real.hasDerivAt_rpow_const (x:=m) (p:= -p) (Or.inl hm.ne'))
  convert! h using 1
  have he : m^(-p)=m^(-p-1)*m := by
    calc
      _ = m^((-p-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hm,Real.rpow_one]
  rw [he]
  ring

theorem force_bound_endpoint_monotone (p : ℝ) (hp : 3/2 ≤ p) :
    StrictAntiOn (fun x : ℝ => forceFactor x*x^(-p)) (Set.Ioc 0 (29/20)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc (0:ℝ) (29/20))
  · intro x hx
    exact (forceEnergy_hasDerivAt p x hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioc (0:ℝ) (29/20) := interior_subset hx
    rw [(forceEnergy_hasDerivAt p x hx'.1 hx'.2).deriv]
    have h := forceFactor_derivative_bound x hx'.1 hx'.2
    have hG : 0 < forceFactor x := lt_trans (by norm_num) (force_factor_bounds x hx'.1 hx'.2).1
    have hneg : x*forceFactorDeriv x-p*forceFactor x < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hx'.1 _) hneg

#check force_bound_endpoint_monotone
#print axioms force_bound_endpoint_monotone
end Blueprint.Thomson.Tail.Implementation
