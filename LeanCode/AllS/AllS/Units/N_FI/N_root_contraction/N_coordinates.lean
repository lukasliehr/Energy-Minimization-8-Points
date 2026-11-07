import AllS.Units.N_F.N_height_upper

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def rootAlpha : ℝ := 1+sqrt 2/2
def rootBeta : ℝ := 1-sqrt 2/2
def rootC : ℝ := log rootAlpha
def rootT (q v : ℝ) : ℝ := rootC-log (1+exp (-q*log 2)-
  rootBeta*exp (-q*log (sqrt 2+exp (v/q))))
def rootHeight (q v : ℝ) : ℝ :=
  (2*exp (v/q)-2+sqrt 2)/(2*exp (v/q)+2+sqrt 2)
def rootV (s : ℝ) : ℝ := (1+s/2)*log (dC (aS s)/dA (aS s))
def rootLambda (m : ℕ) : ℝ := (1/19)*(5/12)^(m-1)

theorem root_sqrt_bounds : 7/5 < sqrt (2:ℝ) ∧ sqrt (2:ℝ) < 27/19 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  constructor <;> nlinarith

theorem root_constants : 1 < rootAlpha ∧ 0 < rootBeta ∧ rootBeta < 1 ∧ 0 < rootC := by
  obtain ⟨hl,hu⟩ := root_sqrt_bounds
  have ha : 1 < rootAlpha := by dsimp [rootAlpha]; linarith
  exact ⟨ha,by dsimp [rootBeta]; linarith,by dsimp [rootBeta]; linarith,
    Real.log_pos ha⟩

theorem physical_root_coordinates (a : ℝ) (ha : physical a) :
    0 < dA a ∧ 1 < dC a/dA a ∧
    dB a=2*dA a ∧ dD a=(sqrt 2+dC a/dA a)*dA a ∧
    (2*(dC a/dA a)-2+sqrt 2)/(2*(dC a/dA a)+2+sqrt 2)=a := by
  have hr := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hs := root_sqrt_bounds
  have hA : 0 < dA a := by dsimp [dA]; linarith [ha.2]
  have hCa : dA a < dC a := by
    have hal := ha.1
    dsimp [aInf] at hal
    have hpos : 0 < (2+sqrt (2:ℝ))*(a-(2*sqrt 2-1)/7) := mul_pos (by linarith [hs.1]) (by linarith)
    dsimp [dA,dC]
    nlinarith
  have hu : 1 < dC a/dA a := (lt_div_iff₀ hA).mpr (by simpa using hCa)
  refine ⟨hA,hu,?_,?_,?_⟩
  · dsimp [dA,dB]; ring
  · field_simp
    dsimp [dA,dC,dD]
    ring
  · have hden : 2*(dC a/dA a)+2+sqrt 2 ≠ 0 := by linarith [hs.1]
    apply (div_eq_iff hden).mpr
    field_simp [hA.ne']
    dsimp [dA,dC]
    ring

theorem rootT_delta_pos (q u : ℝ) (hq : 0 < q) (hu : 1 ≤ u) :
    0 < exp (-q*log 2)-rootBeta*exp (-q*log (sqrt 2+u)) := by
  have hz : (2:ℝ) < sqrt 2+u := by linarith [root_sqrt_bounds.1]
  have hl : log (2:ℝ)<log (sqrt 2+u) := Real.log_lt_log (by norm_num) hz
  have he : exp (-q*log (sqrt 2+u)) < exp (-q*log 2) := Real.exp_lt_exp.mpr (by nlinarith)
  have hb := root_constants
  have hp := Real.exp_pos (-q*log (sqrt 2+u))
  nlinarith

theorem root_stationary_normalized (s a : ℝ) (ha : physical a) (hF : F s a=0) :
    1+exp (-(1+s/2)*log 2)-rootBeta*exp (-(1+s/2)*log (sqrt 2+dC a/dA a))=
      rootAlpha*exp (-(1+s/2)*log (dC a/dA a)) := by
  obtain ⟨hA,hu,hB,hD,_⟩ := physical_root_coordinates a ha
  have hu0 : 0 < dC a/dA a := by linarith
  have hz0 : 0 < sqrt 2+dC a/dA a := by linarith [root_sqrt_bounds.1]
  have hC : dC a=(dC a/dA a)*dA a := by field_simp
  have hpos := Real.rpow_pos_of_pos hA (-(1+s/2))
  unfold F at hF
  dsimp only at hF
  rw [hB,hC,hD,Real.mul_rpow (by norm_num : (0:ℝ)≤2) hA.le,
    Real.mul_rpow hu0.le hA.le,Real.mul_rpow hz0.le hA.le] at hF
  have hnorm : 1+(2:ℝ)^(-(1+s/2))-rootBeta*(sqrt 2+dC a/dA a)^(-(1+s/2))=
      rootAlpha*(dC a/dA a)^(-(1+s/2)) := by
    dsimp [rootAlpha,rootBeta]
    nlinarith
  simpa only [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos hu0,Real.rpow_def_of_pos hz0,mul_comm] using hnorm

theorem aS_root_coordinates_strict (s : ℝ) (hs : 0 ≤ s) :
    rootV s ∈ Set.Ioo 0 rootC ∧ rootT (1+s/2) (rootV s)=rootV s ∧
      rootHeight (1+s/2) (rootV s)=aS s := by
  let q := 1+s/2
  let a := aS s
  let u := dC a/dA a
  have hq : 0 < q := by dsimp [q]; linarith
  have ha : physical a := aS_physical s hs
  obtain ⟨hA,hu,hB,hD,hh⟩ := physical_root_coordinates a ha
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hv : rootV s=q*log u := rfl
  have hexp : exp (rootV s/q)=u := by rw [hv,mul_div_cancel_left₀ _ hq.ne',Real.exp_log hu0]
  let δ := exp (-q*log 2)-rootBeta*exp (-q*log (sqrt 2+u))
  have hd : 0 < δ := rootT_delta_pos q u hq hu.le
  have hn : 1+δ=rootAlpha*exp (-rootV s) := by
    have h := root_stationary_normalized s a ha (aS_mem_and_root s hs).2
    change 1+exp (-q*log 2)-rootBeta*exp (-q*log (sqrt 2+u))=rootAlpha*exp (-q*log u) at h
    simpa only [δ,hv,neg_mul,add_sub_assoc] using h
  have halpha : 0 < rootAlpha := lt_trans (by norm_num) root_constants.1
  have hlog : log (1+δ)=rootC-rootV s := by
    rw [hn,Real.log_mul halpha.ne' (Real.exp_pos _).ne',Real.log_exp]
    rfl
  have hv0 : 0 < rootV s := by rw [hv]; exact mul_pos hq (Real.log_pos hu)
  have hvc : rootV s < rootC := by
    have h := Real.log_pos (show 1 < 1+δ by linarith)
    linarith
  refine ⟨⟨hv0,hvc⟩,?_,?_⟩
  · change rootT q (rootV s)=rootV s
    unfold rootT
    rw [hexp]
    rw [add_sub_assoc]
    change rootC-log (1+δ)=rootV s
    linarith
  · change rootHeight q (rootV s)=a
    unfold rootHeight
    rw [hexp]
    exact hh

theorem aS_root_coordinates (s : ℝ) (hs : 0 ≤ s) :
    rootV s ∈ Set.Icc 0 rootC ∧ rootT (1+s/2) (rootV s)=rootV s ∧
      rootHeight (1+s/2) (rootV s)=aS s := by
  obtain ⟨hv,hT,hh⟩ := aS_root_coordinates_strict s hs
  exact ⟨⟨hv.1.le,hv.2.le⟩,hT,hh⟩

theorem root_contraction_coordinates (s a : ℝ) (hs : 0 ≤ s)
    (ha : a ∈ Set.Ioo 0 1) (hF : F s a=0) :
    let q := 1+s/2
    let u := dC a/dA a
    let v := q*log u
    1 < u ∧ v ∈ Set.Ioo 0 rootC ∧ rootT q v=v ∧ rootHeight q v=a := by
  have heq : a=aS s := SquareAntiprismVerification.aStar_unique s hs a ha hF
  subst a
  exact ⟨(physical_root_coordinates (aS s) (aS_physical s hs)).2.1,
    aS_root_coordinates_strict s hs⟩

#check root_contraction_coordinates
#print axioms root_contraction_coordinates
end Blueprint.Thomson.Finite
