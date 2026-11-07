import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def annulusA : ℝ := 1321/1000
def annulusB : ℝ := 621/1000
def annulusD : ℝ := 351/10000
def annulusW : ℝ := 1083/50
def annulusBeta : ℝ := 128/125
def annulusE : ℝ := 800/(1477*97)
def annulusK : ℝ := 77/100
def annulusV (x : ℝ) : ℝ := annulusA*x-annulusB-annulusD*x^2
def annulusP (x : ℝ) : ℝ :=
  (annulusA-2*annulusD*x)*annulusV x-annulusE*x*annulusW*(1+annulusBeta*annulusV x)

theorem annulus_endpoint_bounds :
    1/3<annulusP annulusK ∧ 11/50<annulusP 6 ∧ 3/8<annulusV annulusK := by
  norm_num [annulusP,annulusV,annulusA,annulusB,annulusD,annulusW,annulusBeta,annulusE,annulusK]

theorem annulus_polynomial_chord (x : ℝ) :
    annulusP x-((6-x)*annulusP annulusK+(x-annulusK)*annulusP 6)/(6-annulusK)=
    (x-annulusK)*(6-x)*(3*annulusA*annulusD+annulusE*annulusW*annulusBeta*annulusA-
      (2*annulusD^2+annulusE*annulusW*annulusBeta*annulusD)*(annulusK+6+x)) := by
  dsimp [annulusP,annulusV,annulusA,annulusB,annulusD,annulusW,annulusBeta,annulusE,annulusK]
  ring

theorem continuous_annulus_polynomial_positive (x : ℝ) (hlo : annulusK≤x) (hhi : x≤6) :
    0<annulusP x ∧ 3/8<annulusV x ∧ 0<annulusA-2*annulusD*x := by
  obtain ⟨hp0,hp1,hv0⟩ := annulus_endpoint_bounds
  have hc : 0≤3*annulusA*annulusD+annulusE*annulusW*annulusBeta*annulusA-
      (2*annulusD^2+annulusE*annulusW*annulusBeta*annulusD)*(annulusK+6+x) := by
    norm_num [annulusA,annulusB,annulusD,annulusW,annulusBeta,annulusE,annulusK]
    linarith
  have hg := mul_nonneg (mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)) hc
  rw [←annulus_polynomial_chord] at hg
  have hden : 0<6-annulusK := by norm_num [annulusK]
  have hchord : 0<((6-x)*annulusP annulusK+(x-annulusK)*annulusP 6)/(6-annulusK) := by
    apply div_pos _ hden
    have h0 := mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hp0.le)
    have h1 := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hp1.le)
    dsimp [annulusK] at hlo h0 h1 ⊢
    nlinarith
  have hvcoef : 0≤annulusA-annulusD*(x+annulusK) := by
    norm_num [annulusA,annulusD,annulusK]
    linarith
  have hv := mul_nonneg (sub_nonneg.mpr hlo) hvcoef
  have hveq : annulusV x-annulusV annulusK=(x-annulusK)*(annulusA-annulusD*(x+annulusK)) := by
    dsimp [annulusV]
    ring
  rw [←hveq] at hv
  refine ⟨by linarith,by linarith,?_⟩
  norm_num [annulusA,annulusD]
  linarith

#print axioms continuous_annulus_polynomial_positive
end Blueprint.Thomson.Tail.Implementation
