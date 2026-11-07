import AllS.Units.N_GI.N_weighted_monotonicity.N_exp_trapezoid

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def twoValueMassDeriv (W v z : ℝ) : ℝ :=
  exp (-v*twoValueA W z)-exp (v*twoValueB W z)+
    v*(twoValueA W z+twoValueB W z)/2*(exp (-v*twoValueA W z)+exp (v*twoValueB W z))

theorem weighted_monotonicity_mass_derivative (W v z : ℝ) (hv : 0 < v)
    (hz : 0 < z) (hzW : z < W) :
    HasDerivAt (fun t => twoValueExp W v t) (twoValueMassDeriv W v z) z ∧
      0 < twoValueMassDeriv W v z := by
  obtain ⟨hA,hB,hbal,h1,h2,hC⟩ := twoValue_coefficients W z hz hzW
  have hk : 0 < W-z := sub_pos.mpr hzW
  have hinvA : 1/(twoValueA W z*z)=twoValueA W z+twoValueB W z := by
    apply (div_eq_iff (by positivity)).mpr
    nlinarith
  have hinvB : 1/(twoValueB W z*(W-z))=twoValueA W z+twoValueB W z := by
    apply (div_eq_iff (by positivity)).mpr
    nlinarith
  have hza : z*(v/(2*twoValueA W z*z^2))=v*(twoValueA W z+twoValueB W z)/2 := by
    calc
      _ = (v/2)*(1/(twoValueA W z*z)) := by field_simp <;> ring
      _ = _ := by rw [hinvA]; ring
  have hkb : (W-z)*(v/(2*twoValueB W z*(W-z)^2))=v*(twoValueA W z+twoValueB W z)/2 := by
    calc
      _ = (v/2)*(1/(twoValueB W z*(W-z))) := by field_simp <;> ring
      _ = _ := by rw [hinvB]; ring
  have hdx : HasDerivAt (fun t => -v*twoValueA W t) (v/(2*twoValueA W z*z^2)) z := by
    have h := (twoValueA_hasDerivAt W z hz hzW).const_mul (-v)
    convert! h using 1 <;> ring
  have hdy : HasDerivAt (fun t => v*twoValueB W t) (v/(2*twoValueB W z*(W-z)^2)) z := by
    have h := (twoValueB_hasDerivAt W z hz hzW).const_mul v
    convert! h using 1 <;> ring
  refine ⟨?_,?_⟩
  · have h := ((hasDerivAt_id z).mul hdx.exp).add
      (((hasDerivAt_const z W).sub (hasDerivAt_id z)).mul hdy.exp)
    convert! h using 1
    dsimp [twoValueMassDeriv]
    linear_combination -exp (-v*twoValueA W z)*hza-exp (v*twoValueB W z)*hkb
  · have hxy : -v*twoValueA W z < v*twoValueB W z := by
      nlinarith [mul_pos hv hA,mul_pos hv hB]
    have h := exp_trapezoid_strict (-v*twoValueA W z) (v*twoValueB W z) hxy
    dsimp [twoValueMassDeriv]
    convert! h using 1 <;> ring

theorem twoValueExp_strictMono_mass (W v : ℝ) (hv : 0 < v) :
    StrictMonoOn (twoValueExp W v) (Set.Ioo 0 W) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 W)
  · intro z hz
    exact (weighted_monotonicity_mass_derivative W v z hv hz.1 hz.2).1.continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    obtain ⟨hd,hp⟩ := weighted_monotonicity_mass_derivative W v z hv hz.1 hz.2
    rwa [hd.deriv]

#check weighted_monotonicity_mass_derivative
#print axioms weighted_monotonicity_mass_derivative
#print axioms twoValueExp_strictMono_mass
end Blueprint.Thomson.Tail.Implementation
