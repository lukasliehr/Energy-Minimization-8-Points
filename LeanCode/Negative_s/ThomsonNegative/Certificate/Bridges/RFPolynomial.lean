import ThomsonNegative.Certificate.Bridges.RFNormalization
import ThomsonNegative.Structure.Packed.IdentitySound

noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure.Packed ThomsonNegative.Structure.PolynomialLift
open ThomsonNegative.Compact.Packed (qval evalQ)

def signedNumerator (a : Bool × ℕ × ℕ) : ℤ :=
  if a.1 then -(a.2.1:ℤ) else (a.2.1:ℤ)

lemma qval_signedNumerator (a : Bool × ℕ × ℕ) :
    qval a=(signedNumerator a:ℝ)/(a.2.2:ℝ) := by
  rcases a with ⟨b,n,d⟩
  cases b <;> simp [qval,signedNumerator] <;> ring

lemma evalZ_cons (c : ℤ) (L : List ℤ) (a : ℝ) :
    evalZ (c::L) a=(c:ℝ)+a*evalZ L a := rfl

lemma evalQ_common_den (L : List (Bool × ℕ × ℕ)) (d : ℕ)
    (hd : ∀ x ∈ L,x.2.2=d) (a : ℝ) :
    evalQ L a=evalZ (L.map signedNumerator) a/(d:ℝ) := by
  induction L with
  | nil => simp [evalQ,evalZ]
  | cons c L ih =>
    rw [evalQ,qval_signedNumerator,hd c (by simp),ih (fun x hx => hd x (by simp [hx]))]
    simp only [List.map_cons,evalZ_cons]
    ring

def integerCoefficients (p : PolyData) : List ℤ := (polyArgs p).map signedNumerator

lemma polyData_eval (p : PolyData) (a : ℝ) :
    p.eval a=evalZ (integerCoefficients p) a/(p.denominator:ℝ) := by
  apply evalQ_common_den
  intro x hx
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
  rfl

def factorCoefficients : List PolyData → List ℤ
  | [] => [1]
  | p::L => convL (integerCoefficients p) (factorCoefficients L)

def factorDenominator : List PolyData → ℕ
  | [] => 1
  | p::L => p.denominator*factorDenominator L

lemma factorProduct_eval (L : List PolyData) (a : ℝ) :
    (L.map (fun p => p.eval a)).prod=evalZ (factorCoefficients L) a/(factorDenominator L:ℝ) := by
  induction L with
  | nil => simp [factorCoefficients,factorDenominator,evalZ,horner]
  | cons p L ih =>
    simp only [List.map_cons,List.prod_cons,factorCoefficients,factorDenominator,Nat.cast_mul]
    rw [polyData_eval,ih,evalZ_convL]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

/-- Homogeneous affine shift: the output evaluates to d^length times the
input evaluated at a+c/d. Arithmetic leaves certify the resulting lists. -/
def affineShift : List ℤ → ℤ → ℤ → List ℤ
  | [],_,_ => []
  | b::L,c,d =>
    addL [b*d^(L.length+1)]
      (addL (scaleL c (affineShift L c d)) (0::scaleL d (affineShift L c d)))

lemma affineShift_eval (L : List ℤ) (c d : ℤ) (hd : d ≠ 0) (a : ℝ) :
    evalZ (affineShift L c d) a=(d:ℝ)^L.length*evalZ L (a+(c:ℝ)/d) := by
  have hd' : (d:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  induction L with
  | nil => simp [affineShift,evalZ]
  | cons b L ih =>
    simp only [affineShift,evalZ_addL,evalZ_scaleL,evalZ_cons,ih,Int.cast_zero,
      zero_add,List.length_cons,Int.cast_mul,Int.cast_pow,
      show evalZ [] a=0 from rfl,mul_zero,add_zero,pow_succ]

    field_simp [hd']
    ring

#print axioms polyData_eval
#print axioms affineShift_eval
end ThomsonNegative.Certificate.Bridges
