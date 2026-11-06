import ThomsonNegative.Structure.Functionals

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure ThomsonNegative.Geometry

lemma orbit_univariateLift_eval (r : Fin 5) (i : Fin 3) (H : Polynomial ℝ) (a : ℝ) :
    (orbitSubstitution r (univariateLift i H)).eval a=
      H.eval (contacts a (orbitLabels r i)) := by
  induction H using Polynomial.induction_on' with
  | add p q hp hq => simp only [univariateLift,map_add,Polynomial.eval_add] at *; exact congrArg₂ (·+·) hp hq
  | monomial n c =>
    simp [univariateLift,orbitSubstitution,Polynomial.aeval_monomial,contactPolynomial_eval]

def candidatePairPolynomial (H : Polynomial ℝ) : Polynomial ℝ :=
  8*H.comp (contactPolynomial 0)+4*H.comp (contactPolynomial 1)+
    8*H.comp (contactPolynomial 2)+8*H.comp (contactPolynomial 3)

lemma familyPolynomial_centered (H : Polynomial ℝ) (e : ℝ) :
    familyPolynomial (centeredPolynomial H e)=2*(candidatePairPolynomial H-Polynomial.C e) := by
  apply Polynomial.funext
  intro a
  simp [familyPolynomial_apply,centeredPolynomial,averagedPolynomial,
    show ∀r c, orbitSubstitution r (MvPolynomial.C c)=Polynomial.C c by
      intro r c; simp [orbitSubstitution],
    orbit_univariateLift_eval,orbitCount,orbitLabels,Fin.sum_univ_succ,
    candidatePairPolynomial,contactPolynomial_eval]
  ring

lemma candidatePairPolynomial_eval (H : Polynomial ℝ) (a : ℝ) (ha : physical a) :
    (candidatePairPolynomial H).eval a=polyPairEnergy H (X a) := by
  rw [show polyPairEnergy H (X a)=PairSum (fun i j => H.eval (inner ℝ (X a i) (X a j))) from rfl,
    candidate_pair_sum a ha (fun t => H.eval t)]
  simp [candidatePairPolynomial,contactPolynomial_eval]

lemma ell0_centered (H : Polynomial ℝ) (e a : ℝ) (ha : physical a) :
    ell0 a (centeredPolynomial H e)=2*(polyPairEnergy H (X a)-e) := by
  simp [ell0,familyPolynomial_centered,candidatePairPolynomial_eval H a ha]

lemma candidatePairPolynomial_derivative (H : Polynomial ℝ) (a : ℝ) :
    (candidatePairPolynomial H).derivative.eval a=candidateSlope H a := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn : Real.sqrt (2:ℝ)≠0 := by positivity
  have hi : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  have hd (i : Fin 4) : (contactPolynomial i).derivative.eval a=
      ![1,2,-1-1/Real.sqrt 2,-1+1/Real.sqrt 2] i := by
    fin_cases i <;> simp [contactPolynomial,one_div,hi] <;> ring
  simp only [candidatePairPolynomial,Polynomial.derivative_add,Polynomial.derivative_mul,
    Polynomial.derivative_ofNat,zero_mul,zero_add,Polynomial.derivative_comp,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp,
    contactPolynomial_eval,hd,candidateSlope]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]
  ring

lemma ell1_centered (H : Polynomial ℝ) (e a : ℝ) :
    ell1 a (centeredPolynomial H e)=2*candidateSlope H a := by
  simp [ell1,familyPolynomial_centered,candidatePairPolynomial_derivative]

theorem target_compatibility (q : ℝ) (hq : 0<q) :
    let a := aStar (2*q-2)
    let p := centeredPolynomial (concreteH q a) (auxEnergy q (X a))
    ell0 a p=0 ∧ ell1 a p=0 := by
  dsimp
  rw [ell0_centered _ _ _ (root_physical q hq),ell1_centered,
    concreteH_candidate_pair q _ (root_physical q hq),root_concreteH_candidateSlope q hq]
  constructor <;> ring

#print axioms target_compatibility
end ThomsonNegative.Certificate.Bridges
