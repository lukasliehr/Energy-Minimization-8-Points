import ThomsonNegative.Certificate.FactorKernel
import ThomsonNegative.Certificate.MatrixSound
import ThomsonNegative.Certificate.RFSound
import Mathlib.Data.Nat.Choose.Basic

/-! Exact square-factor and Bernstein semantics for arbitrary stored integers. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
open scoped BigOperators

noncomputable def pairReal (p : NatPair) : ℝ := (p.1 : ℝ) - p.2

theorem differenceArg_val (p : NatPair) (d : ℕ) :
    qval (differenceArg p d) = pairReal p / d := by
  obtain ⟨a,b⟩ := p
  by_cases h : a < b
  · simp only [differenceArg, Nat.blt_eq, h, qval, if_true, Nat.add_eq, Nat.sub_eq,
      Nat.sub_eq_zero_of_le h.le, zero_add, pairReal]
    rw [Nat.cast_sub h.le]
    ring
  · have hba : b ≤ a := by omega
    simp only [differenceArg, Nat.blt_eq, h, qval, if_false, Nat.add_eq, Nat.sub_eq,
      Nat.sub_eq_zero_of_le hba, add_zero, pairReal]
    rw [Nat.cast_sub hba]

theorem pairReal_add (a b : NatPair) : pairReal (pairAdd a b) = pairReal a + pairReal b := by
  change ((a.1+b.1:ℕ):ℝ)-((a.2+b.2:ℕ):ℝ) = _
  simp only [pairReal,Nat.cast_add]
  ring

theorem pairReal_mul (a b : NatPair) : pairReal (pairMul a b) = pairReal a * pairReal b := by
  change ((a.1*b.1+a.2*b.2:ℕ):ℝ)-((a.1*b.2+a.2*b.1:ℕ):ℝ) = _
  simp only [pairReal,Nat.cast_add,Nat.cast_mul]
  ring

theorem dotNat_val (f g : ℕ → NatPair) (n : ℕ) :
    pairReal (dotNat f g n) = ∑ k ∈ Finset.range n, pairReal (f k) * pairReal (g k) := by
  induction n with
  | zero => simp [dotNat,pairReal]
  | succ n ih =>
    change pairReal (pairAdd (dotNat f g n) (pairMul (f n) (g n))) = _
    rw [pairReal_add,pairReal_mul,ih,Finset.sum_range_succ]

noncomputable def FactorData.eval (F : FactorData) (i j : ℕ) : ℝ :=
  pairReal (factorEntry F i j) / 2^F.bits

noncomputable def FactorData.square (F : FactorData) (i j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range F.order, F.eval i k * F.eval j k

variable {N S B W : ℕ}

theorem squareEntryTM_sound (hg : Good N S B W) (F : FactorData) (i j : ℕ)
    (hok : (squareEntryTM (mkCtx N S B W) F i j).ok = true) :
    Encl (mkCtx N S B W) (squareEntryTM (mkCtx N S B W) F i j)
      (fun _ => F.square i j) := by
  have h := rationalTM_sound hg _ hok
  apply h.congr
  intro t ht
  rw [differenceArg_val,dotNat_val]
  change (∑ k ∈ Finset.range F.order, pairReal (factorEntry F i k) * pairReal (factorEntry F j k)) /
    (((2:ℕ)^(2*F.bits):ℕ):ℝ) = _
  have he : (((2:ℕ)^(2*F.bits):ℕ):ℝ) = (2:ℝ)^F.bits*(2:ℝ)^F.bits := by
    push_cast
    rw [show 2*F.bits=F.bits+F.bits by omega,pow_add]
  rw [he,div_eq_mul_inv,Finset.sum_mul]
  simp only [FactorData.square,FactorData.eval]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem powerTM_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (n : ℕ)
    (hok : (powerTM (mkCtx N S B W) A n).ok = true) :
    Encl (mkCtx N S B W) (powerTM (mkCtx N S B W) A n) (fun t => (a t)^n) := by
  induction n with
  | zero =>
    simpa [powerTM,qval] using rationalTM_sound hg (false,1,1) hok
  | succ n ih =>
    have hp := mul_ok hok
    have h := refresh_sound hg (mul_sound hg (ih hp.1) ha hok)
    simpa only [powerTM,pow_succ] using h

theorem fact_factorial (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [fact, Nat.factorial_succ, ih, Nat.mul_eq]

theorem chooseN_eq (n k : ℕ) : chooseN n k = n.choose k := by
  cases hb : Nat.ble k n with
  | true =>
    have h := Nat.le_of_ble_eq_true hb
    simp only [chooseN,hb,cond_true,fact_factorial,Nat.mul_eq,Nat.sub_eq]
    exact (Nat.choose_eq_factorial_div_factorial h).symm
  | false =>
    have h : n < k := by
      by_contra! hn
      have ht := Nat.ble_eq_true_of_le hn
      rw [hb] at ht
      contradiction
    simp only [chooseN,hb,cond_false]
    exact (Nat.choose_eq_zero_of_lt h).symm

theorem bernsteinTM_sound (hg : Good N S B W) {T : TM} {x : ℝ → ℝ}
    (hT : Encl (mkCtx N S B W) T x) (d i : ℕ)
    (hok : (bernsteinTM (mkCtx N S B W) d i T).ok = true) :
    Encl (mkCtx N S B W) (bernsteinTM (mkCtx N S B W) d i T)
      (fun t => (d.choose i:ℝ) * ((1+x t)/2)^i * ((1-x t)/2)^(d-i)) := by
  let c := mkCtx N S B W
  let one := rationalTM c (false,1,1)
  let half := rationalTM c (false,1,2)
  let plus := refresh c (mul c half (add c one T))
  let minus := refresh c (mul c half (add c one (neg c T)))
  let r := refresh c (mul c (rationalTM c (false,chooseN d i,1))
    (mul c (powerTM c plus i) (powerTM c minus (d-i))))
  have hh : (r.ok && plus.ok && minus.ok)=true := hok
  simp only [Bool.and_eq_true] at hh
  have hp := mul_ok hh.1.2
  have hm := mul_ok hh.2
  have hone := rationalTM_sound hg (false,1,1) (add_ok hp.2).1
  have hhalf := rationalTM_sound hg (false,1,2) hp.1
  have hpsem : Encl c plus (fun t => (1+x t)/2) := by
    have h := refresh_sound hg (mul_sound hg hhalf (add_sound hone hT hp.2) hh.1.2)
    exact h.congr (fun t _ => by simp only [qval]; norm_num; ring)
  have hmsem : Encl c minus (fun t => (1-x t)/2) := by
    have h := refresh_sound hg (mul_sound hg hhalf (add_sound hone (neg_sound hT) hm.2) hh.2)
    exact h.congr (fun t _ => by simp only [qval]; norm_num; ring)
  have hr := mul_ok hh.1.1
  have hpp := mul_ok hr.2
  have hpw := powerTM_sound hg hpsem i hpp.1
  have hmw := powerTM_sound hg hmsem (d-i) hpp.2
  have hw := rationalTM_sound hg (false,chooseN d i,1) hr.1
  have hraw := refresh_sound hg (mul_sound hg hw (mul_sound hg hpw hmw hr.2) hh.1.1)
  have h : Encl c r (fun t => (d.choose i:ℝ) * ((1+x t)/2)^i * ((1-x t)/2)^(d-i)) :=
    hraw.congr (fun t _ => by simp only [qval,chooseN_eq]; norm_num; ring)
  exact h.of_fields rfl rfl rfl rfl

#print axioms squareEntryTM_sound
#print axioms powerTM_sound
#print axioms bernsteinTM_sound
end ThomsonNegative.Certificate
