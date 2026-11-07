import AllS.Units.N_AI.N_data.ScalarGates
import AllS.Units.N_AI.N_matrix_polynomials.N_midpoint_radius
import AllS.Units.N_AI.N_scalar_models.N_product_error
import AllS.Units.N_AI.N_scalar_models.N_log_common_hull
import AllS.Units.N_AI.N_root_models.RootControlSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def QInterval.asBox (I : QInterval) : Box := ⟨I.lo, I.hi⟩
def QModel.asTM {n : ℕ} (M : QModel n) : TM n :=
  ⟨fun k => (M.coeff k).asBox, M.error⟩

def ProductGateSupportStatement : Prop :=
  ∀ {n : ℕ} (A B R : QModel n) (f g : ℝ → ℝ) (T : ℚ),
    A.asTM.Valid f → B.asTM.Valid g → A.ProductGate B R T →
    R.asTM.Valid (fun x => f x*g x)

theorem QInterval.contains_midpoint {I : QInterval} {x : ℝ}
    (hx : I.asBox.Contains x) : 0 ≤ I.rad ∧ |x-(I.mid:ℝ)| ≤ (I.rad:ℝ) := by
  have hle : I.lo ≤ I.hi := by exact_mod_cast hx.1.trans hx.2
  refine ⟨by dsimp [QInterval.rad]; linarith, ?_⟩
  apply abs_le.mpr
  dsimp [QInterval.mid, QInterval.rad]
  push_cast
  change (I.lo:ℝ) ≤ x ∧ x ≤ (I.hi:ℝ) at hx
  constructor <;> linarith [hx.1, hx.2]

theorem qProductRad_nonneg {n : ℕ} (A B : QModel n) (a b : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hb : B.asTM.CoeffContains b) (k : ℕ) :
    0 ≤ qProductRad A B k := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact add_nonneg (add_nonneg
      (mul_nonneg (abs_nonneg _) (QInterval.contains_midpoint (hb j)).1)
      (mul_nonneg (QInterval.contains_midpoint (ha i)).1 (abs_nonneg _)))
      (mul_nonneg (QInterval.contains_midpoint (ha i)).1 (QInterval.contains_midpoint (hb j)).1)
  · exact le_rfl

theorem cauchyCoeff_qProduct_bound {n : ℕ} (A B : QModel n) (a b : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hb : B.asTM.CoeffContains b) (k : ℕ) :
    |cauchyCoeff a b k-(qProductMid A B k:ℝ)| ≤ (qProductRad A B k:ℝ) := by
  simp only [cauchyCoeff, qProductMid, qProductRad, Rat.cast_sum, apply_ite,
    Rat.cast_zero, Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i.val+j.val=k
  · simp only [if_pos hij]
    exact product_midpoint_radius _ _ _ _ _ _
      (by exact_mod_cast (QInterval.contains_midpoint (ha i)).1)
      (by exact_mod_cast (QInterval.contains_midpoint (hb j)).1)
      (QInterval.contains_midpoint (ha i)).2 (QInterval.contains_midpoint (hb j)).2
  · simp [hij]

theorem cauchyHigh_eval_padded {n : ℕ} (a b : Fin (n+1) → ℝ) (x : ℝ) :
    (cauchyHigh a b).eval x =
      scalarEval (fun k : Fin (n+1) => cauchyCoeff a b (n+1+k.val)) x := by
  simp only [cauchyHigh, finitePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, scalarEval]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last,
    cauchyCoeff_eq_zero a b (n+1+n) (by omega), zero_mul, add_zero]

theorem QModel.coefficient_norm {n : ℕ} (A : QModel n) (a : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) : (∑ k, |a k|) ≤ (A.norm:ℝ) := by
  simpa [QModel.norm, QInterval.mag, QModel.asTM, QInterval.asBox, Box.magnitude]
    using Finset.sum_le_sum (s:=Finset.univ) (fun k _ => Box.abs_le_magnitude (ha k))

theorem qProductTailControl_cast {n : ℕ} (A B : QModel n) (i : Fin (n+1)) :
    bernsteinControls (fun k : Fin (n+1) => (qProductMid A B (n+1+k.val):ℝ)) i =
      (qProductTailControl A B i:ℝ) := by
  simp only [bernsteinControls, qProductTailControl, Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [rationalBernsteinTransform_cast n i.val k.val (by omega)]

theorem qProductTailRadius_cast {n : ℕ} (A B : QModel n) (i : Fin (n+1)) :
    bernsteinRadii (fun k : Fin (n+1) => (qProductRad A B (n+1+k.val):ℝ)) i =
      (qProductTailRadius A B i:ℝ) := by
  simp only [bernsteinRadii, qProductTailRadius, Rat.cast_sum, Rat.cast_mul, Rat.cast_abs]
  apply Finset.sum_congr rfl
  intro k _
  rw [rationalBernsteinTransform_cast n i.val k.val (by omega)]

theorem qProduct_tail_bound {n : ℕ} (A B : QModel n) (a b : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hb : B.asTM.CoeffContains b) (T : ℚ)
    (hT : qProductTailPower A B ≤ T ∨ ∀ i : Fin (n+1),
      |qProductTailControl A B i| + qProductTailRadius A B i ≤ T) :
    ∀ x ∈ cellDomain, |x^(n+1)*(cauchyHigh a b).eval x| ≤ (T:ℝ) := by
  intro x hx
  let h : Fin (n+1) → ℝ := fun k => cauchyCoeff a b (n+1+k.val)
  let mid : Fin (n+1) → ℝ := fun k => (qProductMid A B (n+1+k.val):ℝ)
  let rad : Fin (n+1) → ℝ := fun k => (qProductRad A B (n+1+k.val):ℝ)
  have herr (k) : |h k-mid k| ≤ rad k := cauchyCoeff_qProduct_bound A B a b ha hb _
  have hs : |scalarEval h x| ≤ (T:ℝ) := by
    rcases hT with hp | hbnd
    · calc
        _ ≤ ∑ k, |h k| := scalarEval_abs_le_sum h x hx
        _ ≤ ∑ k, (|mid k| + rad k) := by
          apply Finset.sum_le_sum
          intro k _
          calc
            |h k| = |mid k+(h k-mid k)| := by congr 1; ring
            _ ≤ |mid k|+|h k-mid k| := abs_add_le _ _
            _ ≤ _ := add_le_add le_rfl (herr k)
        _ = (qProductTailPower A B:ℝ) := by simp [qProductTailPower, mid, rad]
        _ ≤ (T:ℝ) := by exact_mod_cast hp
    · apply bernstein_bound_of_controls h _ x _ hx
      intro i
      calc
        |bernsteinControls h i| =
            |bernsteinControls mid i+(bernsteinControls h i-bernsteinControls mid i)| := by
              congr 1; ring
        _ ≤ |bernsteinControls mid i|+|bernsteinControls h i-bernsteinControls mid i| := abs_add_le _ _
        _ ≤ |bernsteinControls mid i|+bernsteinRadii rad i :=
          add_le_add le_rfl (bernsteinControls_error h mid rad herr i)
        _ = (|qProductTailControl A B i|+qProductTailRadius A B i:ℚ) := by
          rw [qProductTailControl_cast, qProductTailRadius_cast]
          norm_cast
        _ ≤ (T:ℝ) := by exact_mod_cast hbnd i
  rw [abs_mul, abs_pow, cauchyHigh_eval_padded]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx))
    (abs_nonneg _)).trans (by simpa [h] using hs)

theorem productGateSupport : ProductGateSupportStatement := by
  intro n A B R f g T hA hB hgate
  rcases hA with ⟨heA, a, ha, hra⟩
  rcases hB with ⟨heB, b, hb, hrb⟩
  let wa : A.asTM.Witness f := ⟨a,ha,heA,hra⟩
  let wb : B.asTM.Witness g := ⟨b,hb,heB,hrb⟩
  apply scalar_models_product_error A.asTM B.asTM R.asTM f g wa wb
    (A.norm:ℝ) (B.norm:ℝ) (T:ℝ)
  · exact QModel.coefficient_norm A a ha
  · exact QModel.coefficient_norm B b hb
  · exact qProduct_tail_bound A B a b ha hb T hgate.2.1
  · intro k
    have he := abs_le.mp (cauchyCoeff_qProduct_bound A B a b ha hb k.val)
    have hlo : ((R.coeff k).lo:ℝ) ≤ (qProductMid A B k.val:ℝ)-(qProductRad A B k.val:ℝ) := by
      exact_mod_cast (hgate.1 k).1
    have hhi : (qProductMid A B k.val:ℝ)+(qProductRad A B k.val:ℝ) ≤ ((R.coeff k).hi:ℝ) := by
      exact_mod_cast (hgate.1 k).2
    change ((R.coeff k).lo:ℝ) ≤ cauchyCoeff a b k.val ∧
      cauchyCoeff a b k.val ≤ ((R.coeff k).hi:ℝ)
    constructor <;> linarith [he.1, he.2]
  · exact_mod_cast hgate.2.2

#check productGateSupport
#print ProductGateSupportStatement
#print axioms productGateSupport
end Blueprint.CAP
