import AllS.Units.N_FI.N_contact_interpolation.N_standard_rank
import AllS.Units.N_FI.N_contact_interpolation.N_scalar_lagrange

noncomputable section
namespace Blueprint.Thomson.Finite

def standardLinear (a : ℝ) (V : Fin 5 → ℝ) : Polynomial ℝ :=
  scalarLagrange ![-a,-1] ![V 3,V 4]

def standardH (a : ℝ) : Polynomial ℝ :=
  (Polynomial.X+Polynomial.C a)*(Polynomial.X+1)

def standardResidual (a : ℝ) (F G : Fin 5 → ℝ) (i : Fin 3) : ℝ :=
  (F (Fin.castAdd 2 i)+repeatedLambda a i*G (Fin.castAdd 2 i)-
    (standardLinear a F).eval (contactSigma a (Fin.castAdd 2 i))-
    repeatedLambda a i*(standardLinear a G).eval (contactSigma a (Fin.castAdd 2 i))) /
      (standardH a).eval (contactSigma a (Fin.castAdd 2 i))

def standardSlope (a : ℝ) (r : Fin 3 → ℝ) : ℝ :=
  (r 1-r 2)/(contactSigma a 1-contactSigma a 2)
def standardIntercept (a : ℝ) (r : Fin 3 → ℝ) : ℝ :=
  r 1-standardSlope a r*contactSigma a 1
def standardGamma (a : ℝ) (r : Fin 3 → ℝ) : ℝ :=
  2*(r 0-standardIntercept a r-standardSlope a r*contactSigma a 0)/(a-1)
def standardBeta (a : ℝ) (r : Fin 3 → ℝ) : ℝ := standardSlope a r+standardGamma a r/6
def standardAlpha (a : ℝ) (r : Fin 3 → ℝ) : ℝ := standardIntercept a r-standardGamma a r*a/2

def standardFStar (a : ℝ) (F G : Fin 5 → ℝ) : Polynomial ℝ :=
  standardLinear a F+standardH a*(Polynomial.C (standardAlpha a (standardResidual a F G))+
    Polynomial.C (standardBeta a (standardResidual a F G))*Polynomial.X)

def standardGStar (a : ℝ) (F G : Fin 5 → ℝ) : Polynomial ℝ :=
  standardLinear a G+Polynomial.C (standardGamma a (standardResidual a F G))*standardH a

def StandardInterpolantContract : Prop := ∀ a : ℝ, physical a → ∀ F G : Fin 5 → ℝ,
  (standardFStar a F G).natDegree ≤ 3 ∧ (standardGStar a F G).natDegree ≤ 2 ∧
  (∀ r : Fin 2,
    (standardFStar a F G).eval (contactSigma a (regularOrbit r)) = F (regularOrbit r) ∧
    (standardGStar a F G).eval (contactSigma a (regularOrbit r)) = G (regularOrbit r)) ∧
  (∀ i : Fin 3,
    (standardFStar a F G).eval (contactSigma a (Fin.castAdd 2 i))+
      repeatedLambda a i*(standardGStar a F G).eval (contactSigma a (Fin.castAdd 2 i)) =
        F (Fin.castAdd 2 i)+repeatedLambda a i*G (Fin.castAdd 2 i))


theorem standardRegularNodes_injective (a : ℝ) (ha : physical a) :
    Function.Injective (![-a,-1] : Fin 2 → ℝ) := by
  have hu := ha.2
  intro i j he
  fin_cases i <;> fin_cases j <;> norm_num at * <;> linarith

theorem standardLinear_degree (a : ℝ) (ha : physical a) (V : Fin 5 → ℝ) :
    (standardLinear a V).natDegree ≤ 1 := by
  have hd : (standardLinear a V).degree < 2 :=
    scalarLagrange_degree _ _ (standardRegularNodes_injective a ha)
  by_cases hz : standardLinear a V = 0
  · simp [hz]
  have h : (standardLinear a V).natDegree < 2 := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hd
  omega

theorem standardLinear_regular (a : ℝ) (ha : physical a) (V : Fin 5 → ℝ) (r : Fin 2) :
    (standardLinear a V).eval (contactSigma a (regularOrbit r)) = V (regularOrbit r) := by
  have h := scalarLagrange_eval ![-a,-1] ![V 3,V 4] (standardRegularNodes_injective a ha) r
  fin_cases r <;> simpa [standardLinear,regularOrbit,contactSigma_values] using h

theorem standardH_eval (a x : ℝ) : (standardH a).eval x = (x+a)*(x+1) := by
  simp [standardH]

theorem standardH_regular (a : ℝ) (r : Fin 2) :
    (standardH a).eval (contactSigma a (regularOrbit r)) = 0 := by
  rw [standardH_eval,contactSigma_values]
  fin_cases r <;> norm_num [regularOrbit]
  all_goals try dsimp
  all_goals simp

theorem standardH_repeated_ne (a : ℝ) (ha : physical a) (i : Fin 3) :
    (standardH a).eval (contactSigma a (Fin.castAdd 2 i)) ≠ 0 := by
  have h3 : contactSigma a (Fin.castAdd 2 i) ≠ contactSigma a 3 :=
    (contactSigma_injective a ha).ne (by fin_cases i <;> decide)
  have h4 : contactSigma a (Fin.castAdd 2 i) ≠ contactSigma a 4 :=
    (contactSigma_injective a ha).ne (by fin_cases i <;> decide)
  have h3v : contactSigma a 3 = -a := by rw [contactSigma_values]; rfl
  have h4v : contactSigma a 4 = -1 := by rw [contactSigma_values]; rfl
  rw [h3v] at h3
  rw [h4v] at h4
  rw [standardH_eval]
  apply mul_ne_zero <;> intro he
  · apply h3; linarith
  · apply h4; linarith

theorem standard_coeff_interpolation (a : ℝ) (ha : physical a) (r : Fin 3 → ℝ) (i : Fin 3) :
    standardAlpha a r+standardBeta a r*contactSigma a (Fin.castAdd 2 i)+
      standardGamma a r*repeatedLambda a i = r i := by
  have hd : contactSigma a 1-contactSigma a 2 ≠ 0 :=
    sub_ne_zero.mpr ((contactSigma_injective a ha).ne (by decide))
  have ha1 : a-1 ≠ 0 := by have hu := ha.2; linarith
  have hl1 : standardIntercept a r+standardSlope a r*contactSigma a 1 = r 1 := by
    unfold standardIntercept
    ring
  have hl2 : standardIntercept a r+standardSlope a r*contactSigma a 2 = r 2 := by
    unfold standardIntercept standardSlope
    field_simp
    <;> ring
  have hg : standardGamma a r*(a-1) =
      2*(r 0-standardIntercept a r-standardSlope a r*contactSigma a 0) := by
    unfold standardGamma
    field_simp
  have hlambda0 : repeatedLambda a 0-a/2+contactSigma a 0/6 = (a-1)/2 := by
    rw [contactSigma_values]
    dsimp [repeatedLambda]
    ring
  have hlambda1 : repeatedLambda a 1-a/2+contactSigma a 1/6 = 0 := by
    dsimp [repeatedLambda]
    ring
  have hlambda2 : repeatedLambda a 2-a/2+contactSigma a 2/6 = 0 := by
    dsimp [repeatedLambda]
    ring
  have he : standardAlpha a r+standardBeta a r*contactSigma a (Fin.castAdd 2 i)+
      standardGamma a r*repeatedLambda a i =
      standardIntercept a r+standardSlope a r*contactSigma a (Fin.castAdd 2 i)+
      standardGamma a r*(repeatedLambda a i-a/2+contactSigma a (Fin.castAdd 2 i)/6) := by
    unfold standardAlpha standardBeta
    ring
  rw [he]
  fin_cases i
  · change standardIntercept a r+standardSlope a r*contactSigma a 0+
      standardGamma a r*(repeatedLambda a 0-a/2+contactSigma a 0/6) = r 0
    rw [hlambda0]
    nlinarith [hg]
  · change standardIntercept a r+standardSlope a r*contactSigma a 1+
      standardGamma a r*(repeatedLambda a 1-a/2+contactSigma a 1/6) = r 1
    rw [hlambda1,mul_zero,add_zero]
    exact hl1
  · change standardIntercept a r+standardSlope a r*contactSigma a 2+
      standardGamma a r*(repeatedLambda a 2-a/2+contactSigma a 2/6) = r 2
    rw [hlambda2,mul_zero,add_zero]
    exact hl2

theorem standard_interpolant_regular (a : ℝ) (ha : physical a) (F G : Fin 5 → ℝ)
    (r : Fin 2) :
    (standardFStar a F G).eval (contactSigma a (regularOrbit r)) = F (regularOrbit r) ∧
    (standardGStar a F G).eval (contactSigma a (regularOrbit r)) = G (regularOrbit r) := by
  simp [standardFStar,standardGStar,standardH_regular,standardLinear_regular a ha]

theorem standard_interpolant_repeated (a : ℝ) (ha : physical a) (F G : Fin 5 → ℝ)
    (i : Fin 3) :
    (standardFStar a F G).eval (contactSigma a (Fin.castAdd 2 i))+
      repeatedLambda a i*(standardGStar a F G).eval (contactSigma a (Fin.castAdd 2 i)) =
        F (Fin.castAdd 2 i)+repeatedLambda a i*G (Fin.castAdd 2 i) := by
  have hH := standardH_repeated_ne a ha i
  have hr : (standardH a).eval (contactSigma a (Fin.castAdd 2 i))*standardResidual a F G i =
      F (Fin.castAdd 2 i)+repeatedLambda a i*G (Fin.castAdd 2 i)-
      (standardLinear a F).eval (contactSigma a (Fin.castAdd 2 i))-
      repeatedLambda a i*(standardLinear a G).eval (contactSigma a (Fin.castAdd 2 i)) := by
    unfold standardResidual
    field_simp
  have hc := standard_coeff_interpolation a ha (standardResidual a F G) i
  simp only [standardFStar,standardGStar,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  calc
    _ = (standardLinear a F).eval (contactSigma a (Fin.castAdd 2 i))+
        repeatedLambda a i*(standardLinear a G).eval (contactSigma a (Fin.castAdd 2 i))+
        (standardH a).eval (contactSigma a (Fin.castAdd 2 i)) *
        (standardAlpha a (standardResidual a F G)+standardBeta a (standardResidual a F G)*
          contactSigma a (Fin.castAdd 2 i)+standardGamma a (standardResidual a F G)*repeatedLambda a i) := by ring
    _ = _ := by rw [hc,hr]; ring

theorem polynomial_affine_natDegree (c d : ℝ) :
    (Polynomial.C c+Polynomial.C d*Polynomial.X).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · simpa using (Polynomial.natDegree_mul_le (p := Polynomial.C d) (q := (Polynomial.X : Polynomial ℝ)))

theorem standardH_degree (a : ℝ) : (standardH a).natDegree ≤ 2 := by
  have h1 : (Polynomial.X+Polynomial.C a).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (by simp)
  have h2 : (Polynomial.X+1 : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (by simp)
  exact Polynomial.natDegree_mul_le.trans (by omega)

theorem standardFStar_degree (a : ℝ) (ha : physical a) (F G : Fin 5 → ℝ) :
    (standardFStar a F G).natDegree ≤ 3 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (standardLinear_degree a ha F).trans (by decide)
  · apply Polynomial.natDegree_mul_le.trans
    have hH := standardH_degree a
    have hc := polynomial_affine_natDegree (standardAlpha a (standardResidual a F G))
      (standardBeta a (standardResidual a F G))
    omega

theorem standardGStar_degree (a : ℝ) (ha : physical a) (F G : Fin 5 → ℝ) :
    (standardGStar a F G).natDegree ≤ 2 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (standardLinear_degree a ha G).trans (by decide)
  · have h := Polynomial.natDegree_mul_le
      (p := Polynomial.C (standardGamma a (standardResidual a F G))) (q := standardH a)
    simpa using h.trans (by simpa using standardH_degree a)

theorem contact_interpolation_standard_interpolant : StandardInterpolantContract := by
  intro a ha F G
  exact ⟨standardFStar_degree a ha F G,standardGStar_degree a ha F G,
    standard_interpolant_regular a ha F G,standard_interpolant_repeated a ha F G⟩

#check contact_interpolation_standard_interpolant
#print axioms contact_interpolation_standard_interpolant

#check StandardInterpolantContract
#print axioms StandardInterpolantContract
end Blueprint.Thomson.Finite
