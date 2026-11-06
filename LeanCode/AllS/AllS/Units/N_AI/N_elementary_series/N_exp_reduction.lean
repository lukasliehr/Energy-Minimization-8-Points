import AllS.Units.N_AI.N_elementary_series.N_exp_tail
import AllS.Units.N_AI.N_interval_semantics.N_product
import AllS.Units.N_AI.N_interval_semantics.N_inverse_sqrt
import Blueprint.Target

noncomputable section
namespace Blueprint.CAP
def ExpInitialGate (y : ℝ) (n : ℕ) (I : Box) : Prop :=
  (I.lo:ℝ) ≤ expTaylor n y ∧
    expTaylor n y + (y^(n+1)/(Nat.factorial (n+1):ℝ))/(1-y/((n:ℝ)+2)) ≤ (I.hi:ℝ)

def ExpReductionStatement : Prop :=
  ∀ (z : ℚ) (r n : ℕ) (I : Fin (r+1) → Box),
    0≤(z:ℝ)/2^r → (z:ℝ)/2^r≤1/8 →
    ExpInitialGate ((z:ℝ)/2^r) n (I 0) →
    (∀ j : Fin r, Box.MulGate (I j.castSucc) (I j.castSucc) (I j.succ)) →
    (I ⟨r, Nat.lt_succ_self r⟩).Contains (Real.exp (z:ℝ))

theorem Box.contains_exp_initial {y : ℝ} {n : ℕ} {I : Box}
    (hy0 : 0≤y) (hy1 : y≤1/8) (hg : ExpInitialGate y n I) :
    I.Contains (Real.exp y) := by
  have h := elementary_series_exp_tail y n hy0 hy1
  exact ⟨hg.1.trans h.1, h.2.trans hg.2⟩

theorem exp_squaring_chain (r : ℕ) (I : Fin (r+1)→Box) (y : ℝ)
    (h0 : (I 0).Contains (Real.exp y))
    (hg : ∀ j : Fin r, Box.MulGate (I j.castSucc) (I j.castSucc) (I j.succ)) :
    ∀ j : ℕ, ∀ hj : j≤r,
      (I ⟨j, Nat.lt_succ_of_le hj⟩).Contains (Real.exp (2^j*y)) := by
  intro j
  induction j with
  | zero => intro hj; simpa using h0
  | succ j ih =>
    intro hj
    have hjr : j<r := by omega
    have hp := ih (Nat.le_of_lt hjr)
    have hprod := Box.contains_mul hp hp (hg ⟨j,hjr⟩)
    have hexp : Real.exp (2^j*y)*Real.exp (2^j*y) = Real.exp (2^(j+1)*y) := by
      rw [←Real.exp_add]
      congr 1
      rw [pow_succ]
      ring
    have hi : (⟨j,hjr⟩ : Fin r).succ = ⟨j+1, Nat.lt_succ_of_le hj⟩ := by
      apply Fin.ext
      rfl
    rw [hexp, hi] at hprod
    exact hprod

theorem elementary_series_exp_reduction : ExpReductionStatement := by
  intro z r n I hy0 hy1 hinit hsteps
  have h := exp_squaring_chain r I ((z:ℝ)/2^r)
    (Box.contains_exp_initial hy0 hy1 hinit) hsteps r le_rfl
  have hz : (2:ℝ)^r*((z:ℝ)/2^r) = z := by field_simp
  simpa only [hz] using h

theorem expTaylor_one_le (x : ℝ) (n : ℕ) (hx : 0≤x) : 1≤expTaylor n x := by
  have h := Finset.single_le_sum (f:=fun k:ℕ => x^k/(Nat.factorial k:ℝ))
    (s:=Finset.range (n+1)) (a:=0) (fun k _ => by positivity) (by simp)
  simpa [expTaylor] using h

/-- A precision-parameterized rational expression bounds the negative
exponential, without an alternating-series assumption. -/
theorem exp_negative_enclosure (x : ℝ) (n : ℕ) (hx : 0≤x) (hxn : x<(n:ℝ)+2) :
    1/(expTaylor n x + (x^(n+1)/(Nat.factorial (n+1):ℝ))/(1-x/((n:ℝ)+2))) ≤
      Real.exp (-x) ∧ Real.exp (-x) ≤ 1/expTaylor n x := by
  have h := expTail_general x n hx hxn
  have hp : 0<expTaylor n x := lt_of_lt_of_le zero_lt_one (expTaylor_one_le x n hx)
  have hl := one_div_le_one_div_of_le (Real.exp_pos x) h.2
  have hu := one_div_le_one_div_of_le hp h.1
  simpa only [Real.exp_neg, one_div] using And.intro hl hu

theorem Box.contains_exp_negative {z : ℝ} {I K : Box}
    (hI : I.Contains (Real.exp z)) (hInv : I.InvGate K) :
    K.Contains (Real.exp (-z)) := by
  simpa only [Real.exp_neg, one_div] using (Box.contains_inverse hI hInv).1

theorem Box.contains_exp_of_endpoints {a b x : ℝ} {I J K : Box}
    (hx : a≤x ∧ x≤b) (hI : I.Contains (Real.exp a)) (hJ : J.Contains (Real.exp b))
    (hlo : K.lo≤I.lo) (hhi : J.hi≤K.hi) : K.Contains (Real.exp x) := by
  have hl : (K.lo:ℝ)≤I.lo := by exact_mod_cast hlo
  have hh : (J.hi:ℝ)≤K.hi := by exact_mod_cast hhi
  exact ⟨hl.trans (hI.1.trans (Real.exp_le_exp.mpr hx.1)),
    ((Real.exp_le_exp.mpr hx.2).trans hJ.2).trans hh⟩

#check elementary_series_exp_reduction
#print ExpReductionStatement
#print axioms elementary_series_exp_reduction
#print axioms exp_negative_enclosure
#print axioms Box.contains_exp_negative
#print axioms Box.contains_exp_of_endpoints
end Blueprint.CAP
