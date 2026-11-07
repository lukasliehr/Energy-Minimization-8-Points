import AllS.Units.N_F.N_root_defect
import AllS.Units.N_AI.N_scalar_models.N_log_common_hull

noncomputable section
open Blueprint.Thomson Blueprint.Thomson.Finite
namespace Blueprint.CAP

def RootHeightEnclosureStatement : Prop :=
  ∀ {N : ℕ} (M R : TM N) (S P : ℝ → ℝ) (q₀ δ : ℝ) (m : ℕ) (I : Box),
    M.Valid (fun x => rootHeight (1+S x/2) (P x)) →
    1 ≤ q₀ → 1 ≤ m → (m:ℝ) ≤ q₀ → 0 ≤ δ →
    (∀ x ∈ cellDomain, 0 ≤ S x ∧ q₀ ≤ 1+S x/2 ∧ P x ∈ Set.Icc 0 rootC ∧
      |P x-rootT (1+S x/2) (P x)| ≤ δ) →
    R.coeff = M.coeff →
    (M.error:ℝ)+5*δ/(17*q₀*(1-rootLambda m)) ≤ (R.error:ℝ) →
    R.PowerHullGate I → (13/50:ℚ) < I.lo → I.hi < (1/3:ℚ) →
    R.Valid (fun x => aS (S x)) ∧ R.CommonPositiveHull I (13/50) ∧
    ∀ x ∈ cellDomain, aS (S x) ∈ Set.Ioo (13/50:ℝ) (1/3)

theorem TM.valid_root_height {N : ℕ} (M R : TM N) (S P : ℝ → ℝ)
    (q₀ δ : ℝ) (m : ℕ)
    (hM : M.Valid (fun x => rootHeight (1+S x/2) (P x)))
    (hq₀ : 1 ≤ q₀) (hm : 1 ≤ m) (hmq₀ : (m:ℝ) ≤ q₀) (hδ : 0 ≤ δ)
    (hdomain : ∀ x ∈ cellDomain, 0 ≤ S x ∧ q₀ ≤ 1+S x/2 ∧
      P x ∈ Set.Icc 0 rootC ∧ |P x-rootT (1+S x/2) (P x)| ≤ δ)
    (hc : R.coeff = M.coeff)
    (he : (M.error:ℝ)+5*δ/(17*q₀*(1-rootLambda m)) ≤ (R.error:ℝ)) :
    R.Valid (fun x => aS (S x)) := by
  obtain ⟨hem, a, ha, hr⟩ := hM
  have hlambda := (rootLambda_bounds m).2
  have hqpos : 0 < q₀ := by linarith
  have hden : 0 < 17*q₀*(1-rootLambda m) := by positivity
  have hcor : 0 ≤ 5*δ/(17*q₀*(1-rootLambda m)) := div_nonneg (by positivity) hden.le
  have hemR : (0:ℝ) ≤ M.error := by exact_mod_cast hem
  have hR : (0:ℝ) ≤ R.error := (add_nonneg hemR hcor).trans he
  refine ⟨by exact_mod_cast hR, a, ?_, ?_⟩
  · simpa only [TM.CoeffContains, hc] using ha
  · intro x hx
    obtain ⟨hs, hq, hP, hres⟩ := hdomain x hx
    have hroot := root_defect_point (S x) q₀ (P x) δ m hs hq₀ hq hm hmq₀ hP hres
    calc
      |aS (S x)-scalarEval a x| ≤
          |aS (S x)-rootHeight (1+S x/2) (P x)|+
          |rootHeight (1+S x/2) (P x)-scalarEval a x| := abs_sub_le _ _ _
      _ ≤ 5*δ/(17*q₀*(1-rootLambda m))+(M.error:ℝ) := add_le_add hroot (hr x hx)
      _ ≤ (R.error:ℝ) := by linarith

theorem root_models_height_enclosure : RootHeightEnclosureStatement := by
  intro N M R S P q₀ δ m I hM hq₀ hm hmq₀ hδ hdomain hc he hg hlo hhi
  have hv := TM.valid_root_height M R S P q₀ δ m hM hq₀ hm hmq₀ hδ hdomain hc he
  have hp := scalar_models_log_common_hull R I (13/50) hv.1 (by norm_num) hlo.le hg
  refine ⟨hv, hp, ?_⟩
  obtain ⟨a, ha, hr⟩ := hv.2
  intro x hx
  have hI : I.Contains (aS (S x)) := by
    convert hp.2.2 a ha x hx (aS (S x)-scalarEval a x) (hr x hx) using 1 <;> ring
  have hloR : (13/50:ℝ) < (I.lo:ℝ) := by
    have h : ((13/50:ℚ):ℝ) < (I.lo:ℝ) := Rat.cast_lt.mpr hlo
    norm_num at h ⊢
    exact h
  have hhiR : (I.hi:ℝ) < (1/3:ℝ) := by
    have h : (I.hi:ℝ) < ((1/3:ℚ):ℝ) := Rat.cast_lt.mpr hhi
    norm_num at h ⊢
    exact h
  exact ⟨hloR.trans_le hI.1, hI.2.trans_lt hhiR⟩

#print RootHeightEnclosureStatement
#print axioms root_models_height_enclosure
end Blueprint.CAP
