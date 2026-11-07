import ThomsonNegative.Certificate.Bridges.RawScalar

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
open MvPolynomial

def linearFeature {n m : Nat} (B : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → Poly3) (i : Fin m) : Poly3 :=
  ∑ r, C (B r i)*f r

def quadraticMix {n m : Nat} (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) Poly3) (i j : Fin m) : Poly3 :=
  ∑ r, ∑ s, C (B r i*B s j)*P r s

lemma reynolds_features {n m : Nat} (B : Matrix (Fin n) (Fin m) ℝ)
    (f g : Fin n → Poly3) (i j : Fin m) :
    reynoldsPolynomial (linearFeature B f i*linearFeature B g j)=
      quadraticMix B (fun r s => reynoldsPolynomial (f r*g s)) i j := by
  simp only [linearFeature,Finset.sum_mul_sum,reynolds_sum,quadraticMix]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hh : C (B r i)*f r*(C (B s j)*g s)=C (B r i*B s j)*(f r*g s) := by rw [map_mul]; ring
  rw [hh,reynolds_C_mul]

lemma quadraticMix_add {n m : Nat} (B : Matrix (Fin n) (Fin m) ℝ)
    (P Q : Matrix (Fin n) (Fin n) Poly3) (i j : Fin m) :
    quadraticMix B (P+Q) i j=quadraticMix B P i j+quadraticMix B Q i j := by
  simp [quadraticMix,mul_add,Finset.sum_add_distrib]

lemma quadraticMix_C_mul {n m : Nat} (B : Matrix (Fin n) (Fin m) ℝ)
    (c : ℝ) (P : Matrix (Fin n) (Fin n) Poly3) (i j : Fin m) :
    quadraticMix B (fun r s => C c*P r s) i j=C c*quadraticMix B P i j := by
  simp only [quadraticMix,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

lemma square_reynolds (p q : Poly3) :
    (∑ r : Fin 6, C (1/6:ℝ)*rename (coordinatePerm r) p*rename (coordinatePerm r) q)=
      reynoldsPolynomial (p*q) := by
  simp only [reynoldsPolynomial,map_mul,MvPolynomial.smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

lemma plusPolynomial_mix (B : Matrix (Fin 16) (Fin 11) ℝ) (i j : Fin 11) :
    plusPolynomial B i j=quadraticMix B rawPlusPolynomial i j := by
  change (∑ r : Fin 6, C (1/6:ℝ)*rename (coordinatePerm r) (plusFeature B i)*
    rename (coordinatePerm r) (plusFeature B j))=_
  rw [square_reynolds]
  exact reynolds_features B (fun r => invariantMonomial (plusTag r)) _ i j

lemma standardPolynomial_reynolds (B : Matrix (Fin 18) (Fin 11) ℝ) (i j : Fin 11) :
    standardPolynomial B i j=
      reynoldsPolynomial (linearFeature B standardRawA i*linearFeature B standardRawA j)+
      C (1/3:ℝ)*reynoldsPolynomial (linearFeature B standardRawB i*linearFeature B standardRawB j) := by
  unfold standardPolynomial squarePolynomial
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [Fin.isValue,Prod.fst,Prod.snd,ite_true,show (1:Fin 2)≠0 from by decide,ite_false]
  have ha : standardFeature B 0=linearFeature B standardRawA := by funext k; simp [standardFeature,linearFeature]
  have hb : standardFeature B 1=linearFeature B standardRawB := by funext k; simp [standardFeature,linearFeature]
  rw [ha,hb,square_reynolds]
  congr 1
  rw [reynoldsPolynomial,MvPolynomial.smul_eq_C_mul]
  simp only [map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← mul_assoc,← map_mul]
  norm_num
  ring

lemma standardPolynomial_mix (B : Matrix (Fin 18) (Fin 11) ℝ) (i j : Fin 11) :
    standardPolynomial B i j=quadraticMix B rawStandardPolynomial i j := by
  rw [standardPolynomial_reynolds,reynolds_features,reynolds_features]
  erw [← quadraticMix_C_mul,← quadraticMix_add]
  apply congrArg (fun P => quadraticMix B P i j)
  funext r s
  change reynoldsPolynomial (standardRawA r*standardRawA s)+
    C (1/3:ℝ)*reynoldsPolynomial (standardRawB r*standardRawB s)=rawStandardPolynomial r s
  rw [rawStandardPolynomial,reynolds_add]
  congr 1
  rw [mul_assoc,reynolds_C_mul]

end ThomsonNegative.Certificate.Bridges
