import AllS.Units.N_AI.N_elementary_series.N_log_geometric
import AllS.Units.N_AI.N_interval_semantics.N_affine
import Blueprint.Target

noncomputable section
namespace Blueprint.CAP
def logTransform (v : ℝ) : ℝ := (v-1)/(v+1)
def LogInitialGate (v : ℝ) (n : ℕ) (I : Box) : Prop :=
  (I.lo:ℝ) ≤ 2*logOddPartial (n+1) (logTransform v) ∧
    2*logOddPartial (n+1) (logTransform v) +
      2*(logTransform v)^(2*n+3)/(((2*n+3:ℕ):ℝ)*(1-(logTransform v)^2)) ≤ (I.hi:ℝ)
def LogReductionStatement : Prop :=
  ∀ (z : ℚ) (r : ℤ) (nV nTwo : ℕ) (Iv Itwo Ir Iout : Box), 0<z →
    1≤(z:ℝ)/(2:ℝ)^r → (z:ℝ)/(2:ℝ)^r≤2 →
    LogInitialGate ((z:ℝ)/(2:ℝ)^r) nV Iv → LogInitialGate 2 nTwo Itwo →
    Box.ScaleGate (r:ℚ) Itwo Ir → Box.AddGate Iv Ir Iout →
    Iout.Contains (Real.log (z:ℝ))
theorem logTransform_range (v : ℝ) (hv1 : 1≤v) (hv2 : v≤2) :
    0≤logTransform v ∧ logTransform v≤1/3 := by
  have hd : 0<v+1 := by linarith
  constructor
  · exact div_nonneg (by linarith) hd.le
  · dsimp [logTransform]
    apply (div_le_iff₀ hd).2
    linarith

theorem logTransform_inverse (v : ℝ) (hv : 1≤v) :
    (1+logTransform v)/(1-logTransform v)=v := by
  have hd : v+1≠0 := by linarith
  dsimp [logTransform]
  field_simp
  ring

theorem Box.contains_log_initial {v : ℝ} {n : ℕ} {I : Box}
    (hv1 : 1≤v) (hv2 : v≤2) (hg : LogInitialGate v n I) :
    I.Contains (Real.log v) := by
  have hr := logTransform_range v hv1 hv2
  have hu : logTransform v<1 := by linarith [hr.2]
  have h := elementary_series_log_geometric (logTransform v) n hr.1 hu
  rw [logTransform_inverse v hv1] at h
  exact ⟨hg.1.trans h.1, h.2.trans hg.2⟩

theorem log_powerTwo_identity (z : ℝ) (r : ℤ) (hz : 0<z) :
    Real.log z = Real.log (z/(2:ℝ)^r) + (r:ℝ)*Real.log 2 := by
  rw [Real.log_div (ne_of_gt hz) (ne_of_gt (zpow_pos (by norm_num : (0:ℝ)<2) r)),
    Real.log_zpow]
  ring

theorem elementary_series_log_reduction : LogReductionStatement := by
  intro z r nV nTwo Iv Itwo Ir Iout hz hv1 hv2 hgV hgTwo hgScale hgAdd
  have hV := Box.contains_log_initial hv1 hv2 hgV
  have hTwo := Box.contains_log_initial (by norm_num : (1:ℝ)≤2) le_rfl hgTwo
  have hScale := Box.contains_scale hTwo hgScale
  have hOut := Box.contains_add hV hScale hgAdd
  have hzR : (0:ℝ)<z := by exact_mod_cast hz
  have hid := log_powerTwo_identity (z:ℝ) r hzR
  simpa only [Rat.cast_intCast, ←hid] using hOut

theorem Box.contains_log_of_endpoints {a b x : ℝ} {I J K : Box}
    (ha : 0<a) (hx : a≤x ∧ x≤b)
    (hI : I.Contains (Real.log a)) (hJ : J.Contains (Real.log b))
    (hlo : K.lo≤I.lo) (hhi : J.hi≤K.hi) : K.Contains (Real.log x) := by
  have hx0 : 0<x := ha.trans_le hx.1
  have hl : (K.lo:ℝ)≤I.lo := by exact_mod_cast hlo
  have hh : (J.hi:ℝ)≤K.hi := by exact_mod_cast hhi
  exact ⟨hl.trans (hI.1.trans (Real.log_le_log ha hx.1)),
    ((Real.log_le_log hx0 hx.2).trans hJ.2).trans hh⟩

#check elementary_series_log_reduction
#print LogReductionStatement
#print axioms elementary_series_log_reduction
#print axioms Box.contains_log_of_endpoints
end Blueprint.CAP
