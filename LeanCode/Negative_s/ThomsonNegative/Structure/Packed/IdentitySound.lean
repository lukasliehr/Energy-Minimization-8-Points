import ThomsonNegative.Structure.Packed.IdentityKernel
import ThomsonNegative.Structure.Packed.PolyDecode
import ThomsonNegative.Structure.Packed.PolynomialLift
import Mathlib.Tactic

namespace ThomsonNegative.Structure.Exact

open ThomsonNegative.Structure.Packed ThomsonNegative.Structure.PolynomialLift
open scoped BigOperators

def accumulatorValue (s : Accumulator) : ℤ := (s.1 : ℤ)-s.2

theorem signedMul_value (x y : Signed) : sv (signedMul x y)=sv x*sv y := by
  rcases x with ⟨b,m⟩
  rcases y with ⟨c,n⟩
  cases b <;> cases c <;> simp [signedMul, sv, nat_mul]

theorem addSigned_value (s : Accumulator) (x : Signed) :
    accumulatorValue (addSigned s x)=accumulatorValue s+sv x := by
  rcases x with ⟨b,m⟩
  cases b <;> simp [addSigned, accumulatorValue, sv, nat_add] <;> ring

theorem scaleAccumulator_value (x : Signed) (s : Accumulator) :
    accumulatorValue (scaleAccumulator x s)=sv x*accumulatorValue s := by
  rcases x with ⟨b,m⟩
  cases b <;> simp [scaleAccumulator, accumulatorValue, sv, nat_mul] <;> ring

theorem equalsSigned_sound (s : Accumulator) (x : Signed) (h : equalsSigned s x=true) :
    accumulatorValue s=sv x := by
  rcases x with ⟨b,m⟩
  cases b
  · have he : s.1=s.2+m := Nat.eq_of_beq_eq_true h
    simp [accumulatorValue, sv, he]
  · have he : s.1+m=s.2 := Nat.eq_of_beq_eq_true h
    simp [accumulatorValue, sv, ← he]

theorem allBelow_spec (n : Nat) (p : Nat → Bool) (h : allBelow n p=true) :
    ∀ k, k<n → p k=true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have hh : allBelow n p=true ∧ p n=true := by
      change (allBelow n p && p n)=true at h
      simpa only [Bool.and_eq_true] using h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih hh.1 k hk
    · exact hh.2

theorem recordOk_spec (L W x : Nat) (h : recordOk L W x=true) :
    1≤hdrW x ∧ hdrW x≤W ∧ hdrL x≤L := by
  have hh : (Nat.ble 1 (fld x 20 12) && Nat.ble (fld x 20 12) W) = true ∧
      Nat.ble (fld x 12 8) L=true := by simpa only [recordOk, Bool.and_eq_true] using h
  have hhh : Nat.ble 1 (fld x 20 12)=true ∧ Nat.ble (fld x 20 12) W=true := by
    simpa only [Bool.and_eq_true] using hh.1
  have eW : fld x 20 12=hdrW x := rfl
  have eL : fld x 12 8=hdrL x := rfl
  exact ⟨eW ▸ Nat.le_of_ble_eq_true hhh.1, eW ▸ Nat.le_of_ble_eq_true hhh.2,
    eL ▸ Nat.le_of_ble_eq_true hh.2⟩

theorem record_coefficient_bound (x L W : Nat) (h : recordOk L W x=true) :
    (recCoeffs x).length≤L ∧ ∀ z∈recCoeffs x, |z|≤(2:ℤ)^(W-1) := by
  obtain ⟨h1,h2,h3⟩ := recordOk_spec L W x h
  refine ⟨by rw [length_recCoeffs]; exact h3, ?_⟩
  intro z hz
  simp only [recCoeffs, List.mem_map, List.mem_reverse] at hz
  obtain ⟨s,hs,rfl⟩ := hz
  have hs' := digitsN_lt _ _ _ s hs
  have e : (2:ℕ)^hdrW x=2*2^(hdrW x-1) := by rw [← pow_succ']; congr 1; omega
  have hle : (2:ℤ)^(hdrW x-1)≤2^(W-1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hs2 : (s:ℤ)<2*2^(hdrW x-1) := by exact_mod_cast (e ▸ hs')
  rw [abs_le]
  constructor <;> push_cast <;> omega

theorem list_l1_bound (c : List ℤ) (K : ℕ) (h : ∀ z∈c, |z|≤(K:ℤ)) :
    l1 c≤c.length*K := by
  induction c with
  | nil => simp [l1]
  | cons z c ih =>
    have hz := h z (by simp)
    have hc := ih (fun x hx => h x (by simp [hx]))
    have hzInt : (z.natAbs:ℤ)≤(K:ℤ) := by simpa only [Int.natCast_natAbs] using hz
    have hz' : z.natAbs≤K := by exact_mod_cast hzInt
    rw [l1_cons, List.length_cons]
    nlinarith

theorem record_l1_bound (x L W : Nat) (h : recordOk L W x=true) :
    l1 (recCoeffs x)≤L*2^(W-1) := by
  obtain ⟨hl,hc⟩ := record_coefficient_bound x L W h
  exact (list_l1_bound _ _ hc).trans (Nat.mul_le_mul_right _ hl)

def productSum (n : Nat) (p q : Nat → List ℤ) : List ℤ :=
  Nat.rec (motive := fun _ => List ℤ) [] (fun k r => addL r (convL (p k) (q k))) n

theorem sumProducts_value (R : Nat) (hR : 0<R) (left right : Nat → Nat) (n : Nat) :
    accumulatorValue (sumProducts R left right n)=
      horner ((2:ℤ)^R) (productSum n (fun k => recCoeffs (left k)) (fun k => recCoeffs (right k))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change accumulatorValue (addSigned (sumProducts R left right n)
      (signedMul (polyVal R (left n)) (polyVal R (right n)))) =
      horner _ (addL (productSum n _ _) (convL _ _))
    rw [addSigned_value, signedMul_value, ih, sv_polyVal R _ hR, sv_polyVal R _ hR,
      horner_addL, horner_convL]

theorem productSum_l1_bound (n K : Nat) (p q : Nat → List ℤ)
    (hp : ∀ k, k<n → l1 (p k)≤K) (hq : ∀ k, k<n → l1 (q k)≤K) :
    l1 (productSum n p q)≤n*(K*K) := by
  induction n with
  | zero => simp [productSum, l1]
  | succ n ih =>
    have hn := ih (fun k hk => hp k (by omega)) (fun k hk => hq k (by omega))
    have hprod := (l1_convL (p n) (q n)).trans (Nat.mul_le_mul (hp n (by omega)) (hq n (by omega)))
    change l1 (addL (productSum n p q) (convL (p n) (q n)))≤_
    have hh := l1_addL (productSum n p q) (convL (p n) (q n))
    nlinarith

def Equation.residualPolynomial (e : Equation) : List ℤ :=
  addL (convL (productSum e.terms (fun k => recCoeffs (e.left k))
      (fun k => recCoeffs (e.right k))) (recCoeffs e.scale))
    (scaleL (-1) (convL (convL (recCoeffs e.target0) (recCoeffs e.target1)) (recCoeffs e.target2)))

theorem Equation.headers_spec (e : Equation) (h : e.headers=true) :
    recordOk e.maxLength e.maxWidth e.scale=true ∧
    recordOk e.maxLength e.maxWidth e.target0=true ∧
    recordOk e.maxLength e.maxWidth e.target1=true ∧
    recordOk e.maxLength e.maxWidth e.target2=true ∧
    (∀ k, k<e.terms → recordOk e.maxLength e.maxWidth (e.left k)=true ∧
      recordOk e.maxLength e.maxWidth (e.right k)=true) := by
  simp only [Equation.headers, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,
    fun k hk => by simpa only [Bool.and_eq_true] using (allBelow_spec _ _ h.2 k hk)⟩

theorem Equation.residual_l1_bound (e : Equation) (h : e.headers=true) :
    l1 e.residualPolynomial≤(e.terms+1)*(e.coefficientBound*e.coefficientBound*e.coefficientBound) := by
  obtain ⟨hs,h0,h1,h2,hlr⟩ := e.headers_spec h
  have bound (x : Nat) (hx : recordOk e.maxLength e.maxWidth x=true) :
      l1 (recCoeffs x)≤e.coefficientBound := by
    simpa only [Equation.coefficientBound, nat_mul, nat_shiftLeft, nat_sub, one_mul] using record_l1_bound x _ _ hx
  have hp := productSum_l1_bound e.terms e.coefficientBound
    (fun k => recCoeffs (e.left k)) (fun k => recCoeffs (e.right k))
    (fun k hk => bound _ (hlr k hk).1) (fun k hk => bound _ (hlr k hk).2)
  have ha := (l1_convL _ (recCoeffs e.scale)).trans (Nat.mul_le_mul hp (bound _ hs))
  have hb0 := (l1_convL (recCoeffs e.target0) (recCoeffs e.target1)).trans
    (Nat.mul_le_mul (bound _ h0) (bound _ h1))
  have hb := (l1_convL _ (recCoeffs e.target2)).trans (Nat.mul_le_mul hb0 (bound _ h2))
  unfold Equation.residualPolynomial
  have hh := l1_addL
    (convL (productSum e.terms (fun k => recCoeffs (e.left k)) (fun k => recCoeffs (e.right k))) (recCoeffs e.scale))
    (scaleL (-1) (convL (convL (recCoeffs e.target0) (recCoeffs e.target1)) (recCoeffs e.target2)))
  simp only [l1_scaleL, Int.natAbs_neg, Int.natAbs_one, one_mul] at hh
  nlinarith

theorem Equation.arithmetic_sound (e : Equation) (hR : 0<e.radixBits) (h : e.arithmetic=true) :
    horner ((2:ℤ)^e.radixBits) e.residualPolynomial=0 := by
  have he := equalsSigned_sound _ _ h
  rw [scaleAccumulator_value, sumProducts_value _ hR, signedMul_value, signedMul_value,
    sv_polyVal _ _ hR, sv_polyVal _ _ hR, sv_polyVal _ _ hR, sv_polyVal _ _ hR] at he
  simp only [Equation.residualPolynomial, horner_addL, horner_convL, horner_scaleL]
  linear_combination he

theorem evalZ_productSum (n : Nat) (p q : Nat → List ℤ) (a : ℝ) :
    evalZ (productSum n p q) a=∑ k∈Finset.range n, evalZ (p k) a*evalZ (q k) a := by
  induction n with
  | zero => simp [productSum, evalZ]
  | succ n ih =>
    change evalZ (addL (productSum n p q) (convL (p n) (q n))) a=_
    rw [evalZ_addL, evalZ_convL, ih, Finset.sum_range_succ]

/-- A bounded Init-only identity leaf proves a polynomial identity for every real argument. -/
theorem Equation.sound (e : Equation) (h : e.check=true) (a : ℝ) :
    (∑ k∈Finset.range e.terms, evalZ (recCoeffs (e.left k)) a * evalZ (recCoeffs (e.right k)) a) *
        evalZ (recCoeffs e.scale) a =
      evalZ (recCoeffs e.target0) a * evalZ (recCoeffs e.target1) a * evalZ (recCoeffs e.target2) a := by
  have hh : (e.headers && e.separation)=true ∧ e.arithmetic=true := by
    simpa only [Equation.check, Bool.and_eq_true] using h
  have hh0 : e.headers=true ∧ e.separation=true := by
    simpa only [Bool.and_eq_true] using hh.1
  have sep : Nat.ble 1 e.radixBits=true ∧
      Nat.blt (Nat.mul 2 (Nat.mul (Nat.add e.terms 1)
        (Nat.mul e.coefficientBound (Nat.mul e.coefficientBound e.coefficientBound))))
        (Nat.shiftLeft 1 e.radixBits)=true := by
    simpa only [Equation.separation, Bool.and_eq_true] using hh0.2
  have hR : 0<e.radixBits := Nat.le_of_ble_eq_true sep.1
  have hb : 2≤2^e.radixBits := by
    cases h : e.radixBits with
    | zero => omega
    | succ n =>
      have hp : 0<(2:ℕ)^n := pow_pos (by norm_num) _
      simp only [pow_succ]
      omega
  have hbnd : 2*((e.terms+1)*(e.coefficientBound*e.coefficientBound*e.coefficientBound))<2^e.radixBits := by
    have hs := Nat.blt_eq.mp sep.2
    simpa only [nat_mul, nat_add, nat_shiftLeft, one_mul, mul_assoc] using hs
  have hzero := lift (2^e.radixBits) hb e.residualPolynomial
    ((Nat.mul_le_mul_left 2 (e.residual_l1_bound hh0.1)).trans_lt hbnd)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using e.arithmetic_sound hR hh.2) a
  simp only [Equation.residualPolynomial, evalZ_addL, evalZ_convL, evalZ_scaleL,
    evalZ_productSum, Int.cast_neg, Int.cast_one] at hzero
  linarith

end ThomsonNegative.Structure.Exact
