import ThomsonNegative.Geometry.Base

/-! Generic Newton interpolation, adapted from the three read-only source files
recorded in analysis/formalization_geometry/NEWTON_PROVENANCE.json. -/
noncomputable section


open scoped BigOperators
namespace ThomsonNegative.Geometry

theorem power_jet_zero (z : ℝ) (j k : ℕ) (Q : Polynomial ℝ) (hk : k < j) :
    ((Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z = 0 := by
  have hdiv : (Polynomial.X-Polynomial.C z)^(j-k) ∣
      (Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q) :=
    Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k (dvd_mul_right _ _)
  have hx : Polynomial.X-Polynomial.C z ∣
      (Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q) := by
    apply dvd_trans _ hdiv
    simpa only [pow_one] using
      (pow_dvd_pow (Polynomial.X-Polynomial.C z) (show 1 ≤ j-k by omega))
  exact Polynomial.dvd_iff_isRoot.mp hx

theorem power_jet_diagonal (z : ℝ) (j : ℕ) (Q : Polynomial ℝ) :
    ((Polynomial.derivative^[j]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z =
      (j.factorial : ℝ)*Q.eval z := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single 0]
  · simp [Polynomial.iterate_derivative_X_sub_pow_self]
  · intro b hb hb0
    have hb' : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hz : ((Polynomial.derivative^[j-b]) ((Polynomial.X-Polynomial.C z)^j)).eval z = 0 := by
      simpa only [mul_one] using power_jet_zero z j (j-b) 1 (by omega)
    simp [Polynomial.eval_smul, Polynomial.eval_mul, hz]
  · simp

theorem newton_hermite_power_jets (z : ℝ) (j k : ℕ) (Q : Polynomial ℝ) :
    (k < j → ((Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z = 0) ∧
    ((Polynomial.derivative^[j]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z =
      (j.factorial : ℝ)*Q.eval z :=
  ⟨power_jet_zero z j k Q, power_jet_diagonal z j Q⟩

end ThomsonNegative.Geometry


open scoped BigOperators
namespace ThomsonNegative.Geometry

def newtonBasis (z : ℕ → ℝ) (l : ℕ) : Polynomial ℝ :=
  ∏ k ∈ Finset.range l, (Polynomial.X-Polynomial.C (z k))

def priorMultiplicity (z : ℕ → ℝ) (l : ℕ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.range l).filter (fun k => z k = x)).card

def newtonRemainder (z : ℕ → ℝ) (l : ℕ) (x : ℝ) : Polynomial ℝ := by
  classical
  exact ∏ k ∈ (Finset.range l).filter (fun k => z k ≠ x), (Polynomial.X-Polynomial.C (z k))

theorem newtonBasis_factor (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    newtonBasis z l = (Polynomial.X-Polynomial.C x)^(priorMultiplicity z l x) *
      newtonRemainder z l x := by
  classical
  have hE : (∏ k ∈ (Finset.range l).filter (fun k => z k = x),
      (Polynomial.X-Polynomial.C (z k))) =
      (Polynomial.X-Polynomial.C x)^(priorMultiplicity z l x) := by
    calc
      _ = ∏ _k ∈ (Finset.range l).filter (fun k => z k = x),
          (Polynomial.X-Polynomial.C x) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
      _ = _ := by simp [priorMultiplicity]
  calc
    newtonBasis z l =
        (∏ k ∈ (Finset.range l).filter (fun k => z k = x),
          (Polynomial.X-Polynomial.C (z k))) * newtonRemainder z l x :=
      (Finset.prod_filter_mul_prod_filter_not (Finset.range l)
        (fun k => z k = x) (fun k => Polynomial.X-Polynomial.C (z k))).symm
    _ = _ := by rw [hE]

theorem newtonRemainder_eval (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (newtonRemainder z l x).eval x =
      ∏ k ∈ (Finset.range l).filter (fun k => z k ≠ x), (x-z k) := by
  classical
  simp [newtonRemainder, Polynomial.eval_prod]

theorem newtonRemainder_eval_ne_zero (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (newtonRemainder z l x).eval x ≠ 0 := by
  classical
  rw [newtonRemainder_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact sub_ne_zero.mpr (Finset.mem_filter.mp hk).2.symm

theorem newtonBasis_degree (z : ℕ → ℝ) (l : ℕ) : (newtonBasis z l).degree = l := by
  rw [newtonBasis, Polynomial.degree_prod_of_monic]
  · simp
  · intro k hk
    exact Polynomial.monic_X_sub_C (z k)

theorem newtonBasis_jet_zero (z : ℕ → ℝ) (l : ℕ) (x : ℝ) (k : ℕ)
    (hk : k < priorMultiplicity z l x) :
    ((Polynomial.derivative^[k]) (newtonBasis z l)).eval x = 0 := by
  rw [newtonBasis_factor z l x]
  exact power_jet_zero x (priorMultiplicity z l x) k (newtonRemainder z l x) hk

theorem newtonBasis_jet_diagonal (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x =
      ((priorMultiplicity z l x).factorial : ℝ)*(newtonRemainder z l x).eval x := by
  rw [newtonBasis_factor z l x]
  exact power_jet_diagonal x (priorMultiplicity z l x) (newtonRemainder z l x)

theorem newtonBasis_jet_diagonal_ne_zero (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x ≠ 0 := by
  rw [newtonBasis_jet_diagonal]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (newtonRemainder_eval_ne_zero z l x)

theorem newton_hermite_basis_jet (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (∀ k < priorMultiplicity z l x, ((Polynomial.derivative^[k]) (newtonBasis z l)).eval x = 0) ∧
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x =
      ((priorMultiplicity z l x).factorial : ℝ)*(newtonRemainder z l x).eval x ∧
    ((Polynomial.derivative^[priorMultiplicity z l x]) (newtonBasis z l)).eval x ≠ 0 ∧
    (newtonBasis z l).degree = l :=
  ⟨newtonBasis_jet_zero z l x, newtonBasis_jet_diagonal z l x,
    newtonBasis_jet_diagonal_ne_zero z l x, newtonBasis_degree z l⟩

end ThomsonNegative.Geometry


open scoped BigOperators
namespace ThomsonNegative.Geometry

def newtonHermite (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) : ℕ → Polynomial ℝ
  | 0 => 0
  | l+1 =>
    let H := newtonHermite z J l
    let r := priorMultiplicity z l (z l)
    let c := (J r (z l)-((Polynomial.derivative^[r]) H).eval (z l)) /
      ((Polynomial.derivative^[r]) (newtonBasis z l)).eval (z l)
    H + Polynomial.C c * newtonBasis z l

@[simp] theorem priorMultiplicity_zero (z : ℕ → ℝ) (x : ℝ) :
    priorMultiplicity z 0 x = 0 := by simp [priorMultiplicity]

theorem priorMultiplicity_succ (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    priorMultiplicity z (l+1) x = priorMultiplicity z l x + if z l = x then 1 else 0 := by
  classical
  by_cases h : z l = x <;> simp [priorMultiplicity, Finset.range_add_one, Finset.filter_insert, h]

theorem newtonHermite_jet_update (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ)
    (l k : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[k]) (newtonHermite z J (l+1))).eval x =
    ((Polynomial.derivative^[k]) (newtonHermite z J l)).eval x +
    ((J (priorMultiplicity z l (z l)) (z l) -
      ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonHermite z J l)).eval (z l)) /
      ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonBasis z l)).eval (z l)) *
      ((Polynomial.derivative^[k]) (newtonBasis z l)).eval x := by
  simp only [newtonHermite, ← Module.End.pow_apply, map_add]
  simp only [Module.End.pow_apply, Polynomial.iterate_derivative_C_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

theorem newton_hermite_stage_invariant (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (l : ℕ) :
    (newtonHermite z J l).degree < l ∧
    ∀ (x : ℝ) (k : ℕ), k < priorMultiplicity z l x →
      ((Polynomial.derivative^[k]) (newtonHermite z J l)).eval x = J k x := by
  induction l with
  | zero => simp [newtonHermite]
  | succ l ih =>
    constructor
    · let c := (J (priorMultiplicity z l (z l)) (z l) -
        ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonHermite z J l)).eval (z l)) /
        ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonBasis z l)).eval (z l)
      change (newtonHermite z J l + Polynomial.C c * newtonBasis z l).degree < _
      have hc : (Polynomial.C c * newtonBasis z l).degree ≤ (l : WithBot ℕ) := by
        rw [← newtonBasis_degree z l]
        simpa only [Polynomial.smul_eq_C_mul] using Polynomial.degree_smul_le c (newtonBasis z l)
      have hl : (l : WithBot ℕ) < (l+1 : ℕ) := WithBot.coe_lt_coe.mpr (Nat.lt_succ_self l)
      exact (Polynomial.degree_add_le _ _).trans_lt (max_lt (ih.1.trans hl) (hc.trans_lt hl))
    · intro x k hk
      rw [newtonHermite_jet_update]
      by_cases hold : k < priorMultiplicity z l x
      · rw [newtonBasis_jet_zero z l x k hold, mul_zero, add_zero]
        exact ih.2 x k hold
      · have hx : z l = x := by
          by_contra hn
          rw [priorMultiplicity_succ, if_neg hn, add_zero] at hk
          exact hold hk
        subst x
        have hk' : k = priorMultiplicity z l (z l) := by
          rw [priorMultiplicity_succ, if_pos rfl] at hk
          omega
        subst k
        rw [div_mul_cancel₀ _ (newtonBasis_jet_diagonal_ne_zero z l (z l))]
        ring

end ThomsonNegative.Geometry
#print axioms ThomsonNegative.Geometry.newton_hermite_stage_invariant
