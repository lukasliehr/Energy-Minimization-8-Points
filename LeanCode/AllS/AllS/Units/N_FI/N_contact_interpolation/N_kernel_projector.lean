import AllS.Units.N_FI.N_contact_interpolation.N_standard_interpolant
import AllS.Units.N_FI.N_kernels.N_named_features

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def orbitData (a : ℝ) (p : Poly3) : Fin 5 → ℝ :=
  fun r => MvPolynomial.eval (standardContactPoint a r) p

def invariantProjector (a : ℝ) (p : Poly3) : Poly3 := invariantInterpolant a (orbitData a p)
def alternatingProjector (a : ℝ) (p : Poly3) : Poly3 :=
  alternatingInterpolant a (fun r => orbitData a p (regularOrbit r))
def standardComponent (F G : Poly3) (i : Fin 3) : Poly3 := standardPPoly i*F+standardQPoly i*G

def standardProjector (a : ℝ) (F G : Poly3) (i : Fin 3) : Poly3 :=
  standardComponent
    (polyLift (standardFStar a (orbitData a F) (orbitData a G)) sigma)
    (polyLift (standardGStar a (orbitData a F) (orbitData a G)) sigma) i

def KernelProjectorContract : Prop := ∀ a : ℝ, physical a →
  (∀ p : Poly3, p.IsSymmetric → ∀ r σ,
    MvPolynomial.eval (permutedContact a r σ) (invariantProjector a p) =
      MvPolynomial.eval (permutedContact a r σ) p) ∧
  (∀ p : Poly3, p.IsSymmetric → ∀ r σ,
    MvPolynomial.eval (permutedContact a r σ) (alternatingProjector a p) =
      MvPolynomial.eval (permutedContact a r σ) (deltaPoly*p)) ∧
  (∀ F G : Poly3, F.IsSymmetric → G.IsSymmetric → ∀ i r σ,
    MvPolynomial.eval (permutedContact a r σ) (standardProjector a F G i) =
      MvPolynomial.eval (permutedContact a r σ) (standardComponent F G i)) ∧
  (∀ p : Polynomial ℝ, p.degree < 5 →
    invariantProjector a (polyLift p sigma) = polyLift p sigma) ∧
  (∀ p : Polynomial ℝ, p.degree < 2 →
    alternatingProjector a (polyLift p sigma) = deltaPoly*polyLift p sigma) ∧
  (∀ f g : Polynomial ℝ, f.natDegree ≤ 3 → g.natDegree ≤ 2 →
    standardFStar a (fun r => f.eval (contactSigma a r)) (fun r => g.eval (contactSigma a r)) = f ∧
    standardGStar a (fun r => f.eval (contactSigma a r)) (fun r => g.eval (contactSigma a r)) = g) ∧
  (∀ F G : Poly3, F.IsSymmetric → G.IsSymmetric → ∀ (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) i,
    MvPolynomial.eval (x ∘ σ) (standardComponent F G i) =
      MvPolynomial.eval x (standardComponent F G (σ i)))

theorem eval_symmetric_permute (p : Poly3) (hp : p.IsSymmetric)
    (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (x ∘ σ) p = MvPolynomial.eval x p := by
  rw [← MvPolynomial.eval_rename, hp σ]

theorem eval_symmetric_contact (a : ℝ) (p : Poly3) (hp : p.IsSymmetric)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) p = orbitData a p r :=
  eval_symmetric_permute p hp _ σ

theorem standardPPoly_eval (x : Fin 3 → ℝ) (i : Fin 3) :
    MvPolynomial.eval x (standardPPoly i) = standardP x i := by
  simp [standardPPoly,standardP,sigma_eval]
  ring

theorem standardQPoly_eval (x : Fin 3 → ℝ) (i : Fin 3) :
    MvPolynomial.eval x (standardQPoly i) = standardQ x i := by
  simp [standardQPoly,standardQ,standardPPoly_eval]
  ring

theorem standardP_permute (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    standardP (x ∘ σ) i = standardP x (σ i) := by
  unfold standardP
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ]

theorem standardQ_permute (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    standardQ (x ∘ σ) i = standardQ x (σ i) := by
  unfold standardQ
  simp only [standardP_permute]
  rw [Equiv.sum_comp σ (fun j => standardP x j^2)]

theorem invariantProjector_eval (a : ℝ) (ha : physical a) (p : Poly3) (hp : p.IsSymmetric)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (invariantProjector a p) =
      MvPolynomial.eval (permutedContact a r σ) p := by
  rw [invariantProjector,invariantInterpolant_eval a ha,eval_symmetric_contact a p hp]

theorem alternatingProjector_eval (a : ℝ) (ha : physical a) (p : Poly3) (hp : p.IsSymmetric)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (alternatingProjector a p) =
      MvPolynomial.eval (permutedContact a r σ) (deltaPoly*p) := by
  rw [alternatingProjector,alternatingInterpolant_eval a ha,map_mul,eval_symmetric_contact a p hp]
  fin_cases r
  · have h := deltaPoly_repeated a 0 σ
    change MvPolynomial.eval (permutedContact a 0 σ) deltaPoly = 0 at h
    simp [h]
  · have h := deltaPoly_repeated a 1 σ
    change MvPolynomial.eval (permutedContact a 1 σ) deltaPoly = 0 at h
    simp [h]
  · have h := deltaPoly_repeated a 2 σ
    change MvPolynomial.eval (permutedContact a 2 σ) deltaPoly = 0 at h
    simp [h]
  · rfl
  · rfl

theorem standardComponent_eval (F G : Poly3) (x : Fin 3 → ℝ) (i : Fin 3) :
    MvPolynomial.eval x (standardComponent F G i) =
      standardP x i*MvPolynomial.eval x F+standardQ x i*MvPolynomial.eval x G := by
  simp only [standardComponent,map_add,map_mul,standardPPoly_eval,standardQPoly_eval]

theorem standardProjector_eval (a : ℝ) (ha : physical a) (F G : Poly3)
    (hF : F.IsSymmetric) (hG : G.IsSymmetric) (i : Fin 3) (r : Fin 5)
    (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (standardProjector a F G i) =
      MvPolynomial.eval (permutedContact a r σ) (standardComponent F G i) := by
  rw [standardProjector,standardComponent_eval,standardComponent_eval,
    polyLift_eval,polyLift_eval,sigma_eval_permutedContact,
    eval_symmetric_contact a F hF,eval_symmetric_contact a G hG]
  have hp : standardP (permutedContact a r σ) i = standardP (standardContactPoint a r) (σ i) :=
    standardP_permute _ σ i
  have hq : standardQ (permutedContact a r σ) i = standardQ (standardContactPoint a r) (σ i) :=
    standardQ_permute _ σ i
  rw [hp,hq]
  have hr (j : Fin 3) : ∀ h : r = Fin.castAdd 2 j, standardP (standardContactPoint a r) (σ i)*
      (standardFStar a (orbitData a F) (orbitData a G)).eval (contactSigma a r)+
      standardQ (standardContactPoint a r) (σ i)*
      (standardGStar a (orbitData a F) (orbitData a G)).eval (contactSigma a r) =
      standardP (standardContactPoint a r) (σ i)*orbitData a F r+
      standardQ (standardContactPoint a r) (σ i)*orbitData a G r := by
    intro he
    subst r
    rw [standard_repeated_lambda a j]
    simp only [Pi.smul_apply,smul_eq_mul]
    have hi := standard_interpolant_repeated a ha (orbitData a F) (orbitData a G) j
    nlinarith [congrArg (fun z : ℝ => standardP (standardContactPoint a (Fin.castAdd 2 j)) (σ i)*z) hi]
  have hs (j : Fin 2) : ∀ h : r = regularOrbit j, standardP (standardContactPoint a r) (σ i)*
      (standardFStar a (orbitData a F) (orbitData a G)).eval (contactSigma a r)+
      standardQ (standardContactPoint a r) (σ i)*
      (standardGStar a (orbitData a F) (orbitData a G)).eval (contactSigma a r) =
      standardP (standardContactPoint a r) (σ i)*orbitData a F r+
      standardQ (standardContactPoint a r) (σ i)*orbitData a G r := by
    intro he
    subst r
    obtain ⟨hf,hg⟩ := standard_interpolant_regular a ha (orbitData a F) (orbitData a G) j
    rw [hf,hg]
  fin_cases r
  · exact hr 0 rfl
  · exact hr 1 rfl
  · exact hr 2 rfl
  · exact hs 0 rfl
  · exact hs 1 rfl

theorem scalarLagrange_fix {n : ℕ} (z : Fin n → ℝ) (hz : Function.Injective z)
    (p : Polynomial ℝ) (hp : p.degree < n) :
    scalarLagrange z (fun i => p.eval (z i)) = p := by
  exact (Lagrange.eq_interpolate hz.injOn (by simpa using hp)).symm

theorem orbitData_polyLift (a : ℝ) (p : Polynomial ℝ) (r : Fin 5) :
    orbitData a (polyLift p sigma) r = p.eval (contactSigma a r) := by
  rw [orbitData,polyLift_eval,sigma_eval]
  rfl

theorem invariantProjector_fix (a : ℝ) (ha : physical a) (p : Polynomial ℝ) (hp : p.degree < 5) :
    invariantProjector a (polyLift p sigma) = polyLift p sigma := by
  unfold invariantProjector invariantInterpolant
  rw [show orbitData a (polyLift p sigma) = (fun r => p.eval (contactSigma a r)) from funext (orbitData_polyLift a p)]
  rw [scalarLagrange_fix _ (contactSigma_injective a ha) p hp]

theorem alternatingProjector_fix (a : ℝ) (ha : physical a) (p : Polynomial ℝ) (hp : p.degree < 2) :
    alternatingProjector a (polyLift p sigma) = deltaPoly*polyLift p sigma := by
  unfold alternatingProjector alternatingInterpolant
  simp only [orbitData_polyLift]
  have he : (fun r => contactSigma a (regularOrbit r)) = signSigmaNodes a := by
    funext r
    fin_cases r <;> rw [contactSigma_values] <;> rfl
  have hedata : (fun r => p.eval (contactSigma a (regularOrbit r))) =
      (fun r => p.eval (signSigmaNodes a r)) := by
        funext r
        rw [congrFun he r]
  rw [hedata]
  rw [scalarLagrange_fix _ (signSigmaNodes_injective a ha) p hp]

theorem standardComponent_permute (F G : Poly3) (hF : F.IsSymmetric) (hG : G.IsSymmetric)
    (x : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    MvPolynomial.eval (x ∘ σ) (standardComponent F G i) =
      MvPolynomial.eval x (standardComponent F G (σ i)) := by
  simp only [standardComponent_eval,standardP_permute,standardQ_permute,
    eval_symmetric_permute F hF,eval_symmetric_permute G hG]

theorem standardH_monic (a : ℝ) : (standardH a).Monic := by
  exact (Polynomial.monic_X_add_C a).mul (by simpa using Polynomial.monic_X_add_C (1 : ℝ))

theorem standardH_natDegree (a : ℝ) : (standardH a).natDegree = 2 := by
  rw [standardH,Polynomial.natDegree_mul (Polynomial.monic_X_add_C a).ne_zero
    (show (Polynomial.X+1 : Polynomial ℝ) ≠ 0 by
      simpa using (Polynomial.monic_X_add_C (1 : ℝ)).ne_zero)]
  change (Polynomial.X+Polynomial.C a).natDegree+
    (Polynomial.X+Polynomial.C (1 : ℝ)).natDegree=2
  rw [Polynomial.natDegree_X_add_C,Polynomial.natDegree_X_add_C]

theorem standardH_dvd (a : ℝ) (ha : physical a) (p : Polynomial ℝ)
    (hp : p.eval (-a)=0) (hq : p.eval (-1)=0) : standardH a ∣ p := by
  obtain ⟨q,heq⟩ := Polynomial.dvd_iff_isRoot.mpr (show p.IsRoot (-a) from hp)
  have hqzero : q.eval (-1)=0 := by
    rw [heq,Polynomial.eval_mul] at hq
    have hn : (Polynomial.X-Polynomial.C (-a) : Polynomial ℝ).eval (-1) ≠ 0 := by
      simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      have hu := ha.2
      linarith
    exact (mul_eq_zero.mp hq).resolve_left hn
  obtain ⟨r,hr⟩ := Polynomial.dvd_iff_isRoot.mpr (show q.IsRoot (-1) from hqzero)
  refine ⟨r,?_⟩
  rw [heq,hr]
  simp only [standardH,map_neg,sub_neg_eq_add,Polynomial.C_1]
  ring

theorem standardH_factor (a : ℝ) (ha : physical a) (p : Polynomial ℝ) (n : ℕ)
    (hd : p.natDegree ≤ n) (hp : p.eval (-a)=0) (hq : p.eval (-1)=0) :
    ∃ q : Polynomial ℝ, p=standardH a*q ∧ q.natDegree ≤ n-2 := by
  obtain ⟨q,hq⟩ := standardH_dvd a ha p hp hq
  refine ⟨q,hq,?_⟩
  by_cases hz : q=0
  · simp [hz]
  have h := Polynomial.natDegree_mul (standardH_monic a).ne_zero hz
  rw [← hq,standardH_natDegree] at h
  omega

theorem standard_coefficient_zero (a : ℝ) (ha : physical a) (α β γ : ℝ)
    (h : ∀ i : Fin 3, α+β*contactSigma a (Fin.castAdd 2 i)+γ*repeatedLambda a i=0) :
    α=0 ∧ β=0 ∧ γ=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change α+β*contactSigma a 1+γ*(a/2-contactSigma a 1/6)=0 at h1
  change α+β*contactSigma a 2+γ*(a/2-contactSigma a 2/6)=0 at h2
  have hell : (β-γ/6)*(contactSigma a 1-contactSigma a 2)=0 := by
    linear_combination h1-h2
  have hn : contactSigma a 1-contactSigma a 2 ≠ 0 :=
    sub_ne_zero.mpr ((contactSigma_injective a ha).ne (by decide))
  have hβ : β=γ/6 := sub_eq_zero.mp ((mul_eq_zero.mp hell).resolve_right hn)
  have hα : α= -γ*a/2 := by rw [hβ] at h1; linarith
  change α+β*contactSigma a 0+γ*((a-1)/3)=0 at h0
  have hs0 : contactSigma a 0=4*a-1 := by rw [contactSigma_values]; rfl
  rw [hα,hβ,hs0] at h0
  have hg : γ*(a-1)=0 := by linear_combination 2*h0
  have hγ : γ=0 := (mul_eq_zero.mp hg).resolve_right (by have hu:=ha.2; linarith)
  exact ⟨by simpa [hγ] using hα,by simpa [hγ] using hβ,hγ⟩

theorem standard_zero_unique (a : ℝ) (ha : physical a) (f g : Polynomial ℝ)
    (hf : f.natDegree ≤ 3) (hg : g.natDegree ≤ 2)
    (hr : ∀ i : Fin 2, f.eval (contactSigma a (regularOrbit i))=0 ∧
      g.eval (contactSigma a (regularOrbit i))=0)
    (he : ∀ i : Fin 3, f.eval (contactSigma a (Fin.castAdd 2 i))+
      repeatedLambda a i*g.eval (contactSigma a (Fin.castAdd 2 i))=0) : f=0 ∧ g=0 := by
  have h3 : contactSigma a (regularOrbit 0)= -a := by rw [contactSigma_values]; rfl
  have h4 : contactSigma a (regularOrbit 1)= -1 := by rw [contactSigma_values]; rfl
  obtain ⟨u,hu,hud⟩ := standardH_factor a ha f 3 hf
    (by simpa only [h3] using (hr 0).1) (by simpa only [h4] using (hr 1).1)
  obtain ⟨v,hv,hvd⟩ := standardH_factor a ha g 2 hg
    (by simpa only [h3] using (hr 0).2) (by simpa only [h4] using (hr 1).2)
  have hueq := Polynomial.eq_X_add_C_of_natDegree_le_one hud
  have hveq := Polynomial.eq_C_of_natDegree_le_zero hvd
  have hz : ∀ i : Fin 3, u.coeff 0+u.coeff 1*contactSigma a (Fin.castAdd 2 i)+
      v.coeff 0*repeatedLambda a i=0 := by
    intro i
    have hi := he i
    rw [hu,hv,hueq,hveq] at hi
    simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at hi
    have hm : (standardH a).eval (contactSigma a (Fin.castAdd 2 i))*
        (u.coeff 0+u.coeff 1*contactSigma a (Fin.castAdd 2 i)+v.coeff 0*repeatedLambda a i)=0 := by
      linear_combination hi
    exact (mul_eq_zero.mp hm).resolve_left (standardH_repeated_ne a ha i)
  obtain ⟨hα,hβ,hγ⟩ := standard_coefficient_zero a ha _ _ _ hz
  constructor
  · rw [hu,hueq]
    simp only [hα,hβ,Polynomial.C_0,mul_zero,zero_mul,add_zero]
  · rw [hv,hveq]
    simp only [hγ,Polynomial.C_0,mul_zero]

theorem standardProjector_fix (a : ℝ) (ha : physical a) (f g : Polynomial ℝ)
    (hf : f.natDegree ≤ 3) (hg : g.natDegree ≤ 2) :
    standardFStar a (fun r => f.eval (contactSigma a r)) (fun r => g.eval (contactSigma a r)) = f ∧
    standardGStar a (fun r => f.eval (contactSigma a r)) (fun r => g.eval (contactSigma a r)) = g := by
  let F : Fin 5 → ℝ := fun r => f.eval (contactSigma a r)
  let G : Fin 5 → ℝ := fun r => g.eval (contactSigma a r)
  have hdF : (standardFStar a F G-f).natDegree ≤ 3 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (standardFStar_degree a ha F G) hf)
  have hdG : (standardGStar a F G-g).natDegree ≤ 2 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (standardGStar_degree a ha F G) hg)
  have hr : ∀ i : Fin 2,
      (standardFStar a F G-f).eval (contactSigma a (regularOrbit i))=0 ∧
      (standardGStar a F G-g).eval (contactSigma a (regularOrbit i))=0 := by
    intro i
    obtain ⟨hF,hG⟩ := standard_interpolant_regular a ha F G i
    simp only [Polynomial.eval_sub]
    exact ⟨sub_eq_zero.mpr hF,sub_eq_zero.mpr hG⟩
  have he : ∀ i : Fin 3,
      (standardFStar a F G-f).eval (contactSigma a (Fin.castAdd 2 i))+
      repeatedLambda a i*(standardGStar a F G-g).eval (contactSigma a (Fin.castAdd 2 i))=0 := by
    intro i
    have h := standard_interpolant_repeated a ha F G i
    simp only [Polynomial.eval_sub]
    dsimp [F,G] at h
    linear_combination h
  obtain ⟨hF,hG⟩ := standard_zero_unique a ha _ _ hdF hdG hr he
  exact ⟨sub_eq_zero.mp hF,sub_eq_zero.mp hG⟩

theorem contact_interpolation_kernel_projector : KernelProjectorContract := by
  intro a ha
  exact ⟨invariantProjector_eval a ha,alternatingProjector_eval a ha,standardProjector_eval a ha,
    invariantProjector_fix a ha,alternatingProjector_fix a ha,standardProjector_fix a ha,
    standardComponent_permute⟩

#check contact_interpolation_kernel_projector
#print axioms contact_interpolation_kernel_projector

#check KernelProjectorContract
#print axioms KernelProjectorContract
end Blueprint.Thomson.Finite
