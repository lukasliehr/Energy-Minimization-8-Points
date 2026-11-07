import ThomsonNegative.Structure.CanonicalBasis

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure

def addTag (t u : Tag) : Tag := (t.1+u.1,t.2.1+u.2.1,t.2.2+u.2.2)

lemma invariantMonomial_mul (t u : Tag) :
    invariantMonomial t*invariantMonomial u=invariantMonomial (addTag t u) := by
  simp only [invariantMonomial,addTag,pow_add]
  ring

lemma invariant_generator_rename (r : Fin 6) (i : Fin 3) :
    MvPolynomial.rename (coordinatePerm r) (invariantSubst (MvPolynomial.X i))=
      invariantSubst (MvPolynomial.X i) := by
  fin_cases r <;> fin_cases i <;>
    simp [invariantSubst,coordinatePerm,sigma,e2,e3] <;> ring

lemma invariantSubst_rename (r : Fin 6) (p : Poly3) :
    MvPolynomial.rename (coordinatePerm r) (invariantSubst p)=invariantSubst p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [invariantSubst]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp,invariant_generator_rename]

lemma reynolds_invariant (p : Poly3) : reynoldsPolynomial (invariantSubst p)=invariantSubst p := by
  simp only [reynoldsPolynomial,invariantSubst_rename,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  apply MvPolynomial.funext
  intro x
  simp

lemma reynolds_add (p q : Poly3) : reynoldsPolynomial (p+q)=reynoldsPolynomial p+reynoldsPolynomial q := by
  simp [reynoldsPolynomial,Finset.sum_add_distrib,smul_add]

lemma reynolds_C_mul (c : ℝ) (p : Poly3) :
    reynoldsPolynomial (MvPolynomial.C c*p)=MvPolynomial.C c*reynoldsPolynomial p := by
  simp only [reynoldsPolynomial,map_mul,MvPolynomial.rename_C]
  rw [← Finset.mul_sum,mul_smul_comm]

lemma reynolds_sum {ι : Type*} [Fintype ι] (p : ι → Poly3) :
    reynoldsPolynomial (∑ i,p i)=∑ i,reynoldsPolynomial (p i) := by
  simp only [reynoldsPolynomial,map_sum]
  rw [Finset.sum_comm,Finset.smul_sum]

def standardPairCoordinates (p q : Bool) : Poly3 :=
  if p && q then
    MvPolynomial.C (4/81:ℝ)*MvPolynomial.X 0^4-
      MvPolynomial.C (8/27:ℝ)*MvPolynomial.X 0^2*MvPolynomial.X 1+
      MvPolynomial.C (4/9:ℝ)*MvPolynomial.X 1^2
  else if p || q then
    MvPolynomial.C (4/27:ℝ)*MvPolynomial.X 0^3-
      MvPolynomial.C (2/3:ℝ)*MvPolynomial.X 0*MvPolynomial.X 1+MvPolynomial.C 2*MvPolynomial.X 2
  else MvPolynomial.C (4/9:ℝ)*MvPolynomial.X 0^2-MvPolynomial.C (4/3:ℝ)*MvPolynomial.X 1

def standardPairPhysical (p q : Bool) : Poly3 :=
  (if p then covariantQ 0 else covariantP 0)*(if q then covariantQ 0 else covariantP 0)+
    MvPolynomial.C (1/3:ℝ)*(if p then covariantQ 1-covariantQ 2 else covariantP 1-covariantP 2)*
      (if q then covariantQ 1-covariantQ 2 else covariantP 1-covariantP 2)

lemma standardPair_subst (p q : Bool) :
    invariantSubst (standardPairCoordinates p q)=standardPairPhysical p q := by
  cases p <;> cases q <;> apply MvPolynomial.funext <;> intro x <;>
    simp [standardPairCoordinates,standardPairPhysical,invariantSubst,covariantP,covariantQ,
      sigma,e2,e3,Fin.sum_univ_succ] <;> ring

def rawPlusCoordinates (r s : Fin 16) : Poly3 := coordinateMonomial (addTag (plusTag r) (plusTag s))

def rawPlusPolynomial (r s : Fin 16) : Poly3 :=
  reynoldsPolynomial (invariantMonomial (plusTag r)*invariantMonomial (plusTag s))

def rawStandardCoordinates (r s : Fin 18) : Poly3 :=
  standardPairCoordinates (standardTag r).1 (standardTag s).1*
    coordinateMonomial (addTag (standardTag r).2 (standardTag s).2)

def rawStandardPolynomial (r s : Fin 18) : Poly3 :=
  reynoldsPolynomial (standardRawA r*standardRawA s+
    MvPolynomial.C (1/3:ℝ)*standardRawB r*standardRawB s)

lemma rawPlus_subst (r s : Fin 16) : invariantSubst (rawPlusCoordinates r s)=rawPlusPolynomial r s := by
  rw [rawPlusCoordinates,rawPlusPolynomial,invariantMonomial_mul,
    ← invariantSubst_coordinateMonomial,reynolds_invariant]

lemma rawStandard_subst (r s : Fin 18) :
    invariantSubst (rawStandardCoordinates r s)=rawStandardPolynomial r s := by
  have hf : standardRawA r*standardRawA s+MvPolynomial.C (1/3:ℝ)*standardRawB r*standardRawB s =
      standardPairPhysical (standardTag r).1 (standardTag s).1*
        (invariantMonomial (standardTag r).2*invariantMonomial (standardTag s).2) := by
    unfold standardRawA standardRawB standardPairPhysical
    ring
  rw [rawStandardPolynomial,hf,invariantMonomial_mul,← standardPair_subst,
    ← invariantSubst_coordinateMonomial,← map_mul,reynolds_invariant]
  rfl

#print axioms rawPlus_subst
#print axioms rawStandard_subst
end ThomsonNegative.Certificate.Bridges
