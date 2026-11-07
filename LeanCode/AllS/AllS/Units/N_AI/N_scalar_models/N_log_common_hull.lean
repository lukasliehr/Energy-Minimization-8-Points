import Blueprint.CAPContracts
import AllS.Units.N_AI.N_interval_semantics.N_hulls
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
def Box.magnitude (I : Box) : ℚ := max |I.lo| |I.hi|
def TM.variationRadius {n : ℕ} (M : TM n) : ℚ :=
  ∑ k ∈ (Finset.univ.erase (0 : Fin (n+1))), (M.coeff k).magnitude
def TM.PowerHullGate {n : ℕ} (M : TM n) (I : Box) : Prop :=
  I.lo ≤ (M.coeff 0).lo - M.variationRadius - M.error ∧
    (M.coeff 0).hi + M.variationRadius + M.error ≤ I.hi
def ScalarLogCommonHullStatement : Prop :=
  ∀ {n : ℕ} (M : TM n) (I : Box) (μ : ℚ), 0≤M.error →
    0<μ → μ≤I.lo → M.PowerHullGate I → M.CommonPositiveHull I μ
theorem Box.abs_le_magnitude {I : Box} {x : ℝ} (hx : I.Contains x) :
    |x|≤(I.magnitude:ℝ) := by
  have hl : -max |(I.lo:ℝ)| |(I.hi:ℝ)| ≤ (I.lo:ℝ) :=
    (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
  have hu : (I.hi:ℝ) ≤ max |(I.lo:ℝ)| |(I.hi:ℝ)| :=
    (le_abs_self _).trans (le_max_right _ _)
  have h := abs_le.mpr ⟨hl.trans hx.1, hx.2.trans hu⟩
  simpa [Box.magnitude] using h

theorem scalarEval_split_zero {n : ℕ} (a : Fin (n+1)→ℝ) (x : ℝ) :
    scalarEval a x = a 0 + ∑ k ∈ (Finset.univ.erase (0:Fin (n+1))), a k*x^k.val := by
  have h := Finset.add_sum_erase Finset.univ (fun k : Fin (n+1)=>a k*x^k.val)
    (Finset.mem_univ (0:Fin (n+1)))
  simpa [scalarEval] using h.symm

theorem TM.nonconstant_sum_bound {n : ℕ} (M : TM n) (a : Fin (n+1)→ℝ)
    (ha : M.CoeffContains a) (x : ℝ) (hx : x∈cellDomain) :
    |∑ k ∈ (Finset.univ.erase (0:Fin (n+1))), a k*x^k.val| ≤ (M.variationRadius:ℝ) := by
  have hxabs : |x|≤1 := abs_le.mpr hx
  have hterm (k : Fin (n+1)) : |a k*x^k.val| ≤ ((M.coeff k).magnitude:ℝ) := by
    calc
      |a k*x^k.val| = |a k| * |x|^k.val := by rw [abs_mul, abs_pow]
      _ ≤ |a k| * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (abs_nonneg x) hxabs) (abs_nonneg _)
      _ = |a k| := mul_one _
      _ ≤ ((M.coeff k).magnitude:ℝ) := Box.abs_le_magnitude (ha k)
  have hs := (Finset.abs_sum_le_sum_abs (fun k : Fin (n+1)=>a k*x^k.val)
    (Finset.univ.erase 0)).trans (Finset.sum_le_sum (fun k _=>hterm k))
  simpa [TM.variationRadius] using hs

theorem scalar_models_log_common_hull : ScalarLogCommonHullStatement := by
  intro n M I μ _ hμ hμI hg
  refine ⟨hμ,hμI,?_⟩
  intro a ha x hx r hr
  have hs := abs_le.mp (TM.nonconstant_sum_bound M a ha x hx)
  have hconst := ha 0
  have herr := abs_le.mp hr
  have hlo : (I.lo:ℝ) ≤ ((M.coeff 0).lo:ℝ) - (M.variationRadius:ℝ) - (M.error:ℝ) := by
    exact_mod_cast hg.1
  have hhi : ((M.coeff 0).hi:ℝ) + (M.variationRadius:ℝ) + (M.error:ℝ) ≤ (I.hi:ℝ) := by
    exact_mod_cast hg.2
  rw [scalarEval_split_zero]
  constructor <;> linarith [hconst.1, hconst.2, hs.1, hs.2, herr.1, herr.2]

#check scalar_models_log_common_hull
#print ScalarLogCommonHullStatement
#print axioms scalar_models_log_common_hull
end Blueprint.CAP
