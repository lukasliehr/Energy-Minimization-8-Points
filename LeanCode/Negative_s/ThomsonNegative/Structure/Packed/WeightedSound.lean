import ThomsonNegative.Structure.Packed.WeightedKernel
import ThomsonNegative.Structure.Packed.IdentitySound
namespace ThomsonNegative.Structure.Exact
open ThomsonNegative.Structure.Packed ThomsonNegative.Structure.PolynomialLift
open scoped BigOperators

def weightedSum (n : Nat) (w : Nat → Signed) (p q : Nat → List ℤ) : List ℤ :=
  Nat.rec (motive := fun _ => List ℤ) []
    (fun k r => addL r (scaleL (sv (w k)) (convL (p k) (q k)))) n

theorem signed_natAbs (w : Signed) : (sv w).natAbs=w.2 := by
  rcases w with ⟨b,m⟩
  cases b <;> simp [sv]

theorem sumWeightedProducts_value (R : Nat) (hR : 0<R) (weight : Nat → Signed)
    (left right : Nat → Nat) (n : Nat) :
    accumulatorValue (sumWeightedProducts R weight left right n)=
      horner ((2:ℤ)^R) (weightedSum n weight (fun k => recCoeffs (left k))
        (fun k => recCoeffs (right k))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change accumulatorValue (addSigned (sumWeightedProducts R weight left right n)
      (signedMul (weight n) (signedMul (polyVal R (left n)) (polyVal R (right n))))) =
      horner _ (addL (weightedSum n weight _ _) (scaleL _ (convL _ _)))
    rw [addSigned_value,signedMul_value,signedMul_value,ih,
      sv_polyVal R _ hR,sv_polyVal R _ hR,horner_addL,horner_scaleL,horner_convL]

theorem weightedSum_l1_bound (n K M : Nat) (w : Nat → Signed) (p q : Nat → List ℤ)
    (hw : ∀k,k<n → (w k).2≤M)
    (hp : ∀k,k<n → l1 (p k)≤K) (hq : ∀k,k<n → l1 (q k)≤K) :
    l1 (weightedSum n w p q)≤n*M*(K*K) := by
  induction n with
  | zero => simp [weightedSum,l1]
  | succ n ih =>
    have hn := ih (fun k hk => hw k (by omega))
      (fun k hk => hp k (by omega)) (fun k hk => hq k (by omega))
    have hprod := (l1_convL (p n) (q n)).trans
      (Nat.mul_le_mul (hp n (by omega)) (hq n (by omega)))
    have hscaled : l1 (scaleL (sv (w n)) (convL (p n) (q n)))≤M*(K*K) := by
      rw [l1_scaleL,signed_natAbs]
      exact Nat.mul_le_mul (hw n (by omega)) hprod
    change l1 (addL (weightedSum n w p q) (scaleL _ (convL _ _)))≤_
    have hh := l1_addL (weightedSum n w p q) (scaleL (sv (w n)) (convL (p n) (q n)))
    nlinarith

def WeightedEquation.residualPolynomial (e : WeightedEquation) : List ℤ :=
  addL (convL (weightedSum e.terms e.weight (fun k => recCoeffs (e.left k))
      (fun k => recCoeffs (e.right k))) (recCoeffs e.scale))
    (scaleL (-1) (convL (convL (recCoeffs e.target0) (recCoeffs e.target1)) (recCoeffs e.target2)))

theorem WeightedEquation.residual_l1_bound (e : WeightedEquation) (h : e.headers=true) :
    l1 e.residualPolynomial≤(e.terms*e.maxWeight+1)*
      (e.coefficientBound*e.coefficientBound*e.coefficientBound) := by
  have hh : e.toEquation.headers=true ∧
      allBelow e.terms (fun k => Nat.ble (e.weight k).2 e.maxWeight)=true := by
    simpa only [WeightedEquation.headers,Bool.and_eq_true] using h
  obtain ⟨hs,h0,h1,h2,hlr⟩ := e.toEquation.headers_spec hh.1
  have bound (x : Nat) (hx : recordOk e.maxLength e.maxWidth x=true) :
      l1 (recCoeffs x)≤e.coefficientBound := by
    simpa only [Equation.coefficientBound,nat_mul,nat_shiftLeft,nat_sub,one_mul] using
      record_l1_bound x _ _ hx
  have hp := weightedSum_l1_bound e.terms e.coefficientBound e.maxWeight e.weight
    (fun k => recCoeffs (e.left k)) (fun k => recCoeffs (e.right k))
    (fun k hk => Nat.le_of_ble_eq_true (allBelow_spec _ _ hh.2 k hk))
    (fun k hk => bound _ (hlr k hk).1) (fun k hk => bound _ (hlr k hk).2)
  have ha := (l1_convL _ (recCoeffs e.scale)).trans (Nat.mul_le_mul hp (bound _ hs))
  have hb0 := (l1_convL (recCoeffs e.target0) (recCoeffs e.target1)).trans
    (Nat.mul_le_mul (bound _ h0) (bound _ h1))
  have hb := (l1_convL _ (recCoeffs e.target2)).trans (Nat.mul_le_mul hb0 (bound _ h2))
  unfold WeightedEquation.residualPolynomial
  have hadd := l1_addL
    (convL (weightedSum e.terms e.weight (fun k => recCoeffs (e.left k))
      (fun k => recCoeffs (e.right k))) (recCoeffs e.scale))
    (scaleL (-1) (convL (convL (recCoeffs e.target0) (recCoeffs e.target1)) (recCoeffs e.target2)))
  simp only [l1_scaleL,Int.natAbs_neg,Int.natAbs_one,one_mul] at hadd
  nlinarith

theorem WeightedEquation.arithmetic_sound (e : WeightedEquation)
    (hR : 0<e.radixBits) (h : e.arithmetic=true) :
    horner ((2:ℤ)^e.radixBits) e.residualPolynomial=0 := by
  have he := equalsSigned_sound _ _ h
  rw [scaleAccumulator_value,sumWeightedProducts_value _ hR,signedMul_value,signedMul_value,
    sv_polyVal _ _ hR,sv_polyVal _ _ hR,sv_polyVal _ _ hR,sv_polyVal _ _ hR] at he
  simp only [WeightedEquation.residualPolynomial,horner_addL,horner_convL,horner_scaleL]
  linear_combination he

theorem evalZ_weightedSum (n : Nat) (w : Nat → Signed) (p q : Nat → List ℤ) (a : ℝ) :
    evalZ (weightedSum n w p q) a=
      ∑ k∈Finset.range n, (sv (w k):ℝ)*(evalZ (p k) a*evalZ (q k) a) := by
  induction n with
  | zero => simp [weightedSum,evalZ]
  | succ n ih =>
    change evalZ (addL (weightedSum n w p q) (scaleL _ (convL (p n) (q n)))) a=_
    rw [evalZ_addL,evalZ_scaleL,evalZ_convL,ih,Finset.sum_range_succ]

theorem WeightedEquation.sound (e : WeightedEquation) (h : e.check=true) (a : ℝ) :
    (∑ k∈Finset.range e.terms, (sv (e.weight k):ℝ)*
      (evalZ (recCoeffs (e.left k)) a*evalZ (recCoeffs (e.right k)) a))*
        evalZ (recCoeffs e.scale) a=
      evalZ (recCoeffs e.target0) a*evalZ (recCoeffs e.target1) a*
        evalZ (recCoeffs e.target2) a := by
  have hh : (e.headers && e.separation)=true ∧ e.arithmetic=true := by
    simpa only [WeightedEquation.check,Bool.and_eq_true] using h
  have hh0 : e.headers=true ∧ e.separation=true := by
    simpa only [Bool.and_eq_true] using hh.1
  have sep : Nat.ble 1 e.radixBits=true ∧
      Nat.blt (Nat.mul 2 (Nat.mul (Nat.add (Nat.mul e.terms e.maxWeight) 1)
        (Nat.mul e.coefficientBound (Nat.mul e.coefficientBound e.coefficientBound))))
        (Nat.shiftLeft 1 e.radixBits)=true := by
    simpa only [WeightedEquation.separation,Bool.and_eq_true] using hh0.2
  have hR : 0<e.radixBits := Nat.le_of_ble_eq_true sep.1
  have hb : 2≤2^e.radixBits := by
    cases h : e.radixBits with
    | zero => omega
    | succ n =>
      have hp : 0<(2:ℕ)^n := pow_pos (by norm_num) _
      simp only [pow_succ]
      omega
  have hbnd : 2*((e.terms*e.maxWeight+1)*
      (e.coefficientBound*e.coefficientBound*e.coefficientBound))<2^e.radixBits := by
    have hs := Nat.blt_eq.mp sep.2
    simpa only [nat_mul,nat_add,nat_shiftLeft,one_mul,mul_assoc] using hs
  have hzero := lift (2^e.radixBits) hb e.residualPolynomial
    ((Nat.mul_le_mul_left 2 (e.residual_l1_bound hh0.1)).trans_lt hbnd)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using e.arithmetic_sound hR hh.2) a
  simp only [WeightedEquation.residualPolynomial,evalZ_addL,evalZ_convL,evalZ_scaleL,
    evalZ_weightedSum,Int.cast_neg,Int.cast_one] at hzero
  linarith
end ThomsonNegative.Structure.Exact
