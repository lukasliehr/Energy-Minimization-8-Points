import Lean_Code.SolidAngleAlgebra

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma hasDerivAt_arg_curve {f : ℝ → ℂ} {f' : ℂ} {r : ℝ}
    (hf : HasDerivAt f f' r) (hslit : f r ∈ Complex.slitPlane) :
    HasDerivAt (fun s => (f s).arg) (f' / f r).im r := by
  have hlog := (Complex.hasDerivAt_log hslit).hasFDerivAt.restrictScalars ℝ
  have hcomp := hlog.comp_hasDerivAt r hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hcomp
  simpa [Function.comp_def, Complex.log_im, div_eq_mul_inv, mul_comm] using him

def solidAngleComplex (p a b : ℝ³) : ℂ :=
  ⟨solidAngleDenom p a b, solidAngleNumer p a b⟩

def solidAnglePhase (p a b : ℝ³) : ℝ := 2 * (solidAngleComplex p a b).arg

lemma solidAngleComplex_curve_derivative {f : ℝ → ℝ³} {h : ℝ³} {r : ℝ}
    (hf : HasDerivAt f h r) (a b : ℝ³) :
    HasDerivAt (fun s => solidAngleComplex (f s) a b)
      (⟨inner ℝ a h + inner ℝ b h, inner ℝ (crossVec a b) h⟩ : ℂ) r := by
  have hD := ((hasDerivAt_const r (1 + inner ℝ a b)).add
    ((hasDerivAt_const r a).inner ℝ hf)).add ((hasDerivAt_const r b).inner ℝ hf)
  have hN := (hasDerivAt_const r (crossVec a b)).inner ℝ hf
  have hD' : HasDerivAt (fun s => solidAngleDenom (f s) a b)
      (inner ℝ a h + inner ℝ b h) r := by
    have hca : (fun s => inner ℝ a (f s)) = (fun s => inner ℝ (f s) a) :=
      funext (fun s => real_inner_comm (f s) a)
    have hcb : (fun s => inner ℝ b (f s)) = (fun s => inner ℝ (f s) b) :=
      funext (fun s => real_inner_comm (f s) b)
    rw [hca, hcb] at hD
    convert hD using 1 <;> first
      | rfl
      | simp only [solidAngleDenom, inner_zero_left, add_zero, zero_add, Pi.add_apply]
  have hN' : HasDerivAt (fun s => solidAngleNumer (f s) a b)
      (inner ℝ (crossVec a b) h) r := by simpa [solidAngleNumer] using hN
  have hDc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hD'
  have hNc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hN'
  have hh := hDc.add (hNc.mul_const Complex.I)
  have hmk (u v : ℝ) : (⟨u, v⟩ : ℂ) = (u : ℂ) + (v : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  convert hh using 1 <;> first
    | rfl
    | (funext s; apply Complex.ext <;> simp [solidAngleComplex, Function.comp_def])
    | (apply Complex.ext <;> simp)

lemma solidAnglePhase_curve_derivative {f : ℝ → ℝ³} {h : ℝ³} {r : ℝ}
    (hf : HasDerivAt f h r) (a b : ℝ³)
    (hp : ‖f r‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hph : inner ℝ (f r) h = 0)
    (hslit : solidAngleComplex (f r) a b ∈ Complex.slitPlane) :
    HasDerivAt (fun s => solidAnglePhase (f s) a b)
      (inner ℝ (crossVec (f r) b) h / (1 + inner ℝ (f r) b) -
        inner ℝ (crossVec (f r) a) h / (1 + inner ℝ (f r) a)) r := by
  have hder := (hasDerivAt_arg_curve (solidAngleComplex_curve_derivative hf a b) hslit).const_mul 2
  have hnorm : solidAngleDenom (f r) a b ^ 2 + solidAngleNumer (f r) a b ^ 2 ≠ 0 := by
    rcases Complex.mem_slitPlane_iff.mp hslit with hD | hN
    · change 0 < solidAngleDenom (f r) a b at hD
      nlinarith [sq_pos_of_pos hD, sq_nonneg (solidAngleNumer (f r) a b)]
    · change solidAngleNumer (f r) a b ≠ 0 at hN
      nlinarith [sq_pos_of_ne_zero hN, sq_nonneg (solidAngleDenom (f r) a b)]
  have hidentity := solidAngle_norm_identity (f r) a b hp ha hb
  have hproduct : 2 * (1 + inner ℝ a b) * (1 + inner ℝ (f r) a) * (1 + inner ℝ (f r) b) ≠ 0 := by
    rw [← hidentity]
    exact hnorm
  have hC : 1 + inner ℝ a b ≠ 0 := by intro he; simp [he] at hproduct
  have hA : 1 + inner ℝ (f r) a ≠ 0 := by intro he; simp [he] at hproduct
  have hB : 1 + inner ℝ (f r) b ≠ 0 := by intro he; simp [he] at hproduct
  have htangent := solidAngle_tangent_numerator (f r) a b h hp ha hb hph
  have hvalue : 2 * ((⟨inner ℝ a h + inner ℝ b h, inner ℝ (crossVec a b) h⟩ : ℂ) /
      solidAngleComplex (f r) a b).im =
      inner ℝ (crossVec (f r) b) h / (1 + inner ℝ (f r) b) -
        inner ℝ (crossVec (f r) a) h / (1 + inner ℝ (f r) a) := by
    rw [Complex.div_im, Complex.normSq_apply]
    change 2 * (inner ℝ (crossVec a b) h * solidAngleDenom (f r) a b /
      (solidAngleDenom (f r) a b * solidAngleDenom (f r) a b + solidAngleNumer (f r) a b * solidAngleNumer (f r) a b) -
      (inner ℝ a h + inner ℝ b h) * solidAngleNumer (f r) a b /
      (solidAngleDenom (f r) a b * solidAngleDenom (f r) a b + solidAngleNumer (f r) a b * solidAngleNumer (f r) a b)) = _
    rw [show solidAngleDenom (f r) a b * solidAngleDenom (f r) a b +
        solidAngleNumer (f r) a b * solidAngleNumer (f r) a b =
        solidAngleDenom (f r) a b ^ 2 + solidAngleNumer (f r) a b ^ 2 by ring]
    rw [← sub_div]
    rw [show inner ℝ (crossVec a b) h * solidAngleDenom (f r) a b -
        (inner ℝ a h + inner ℝ b h) * solidAngleNumer (f r) a b =
        solidAngleDenom (f r) a b * inner ℝ (crossVec a b) h -
          solidAngleNumer (f r) a b * (inner ℝ a h + inner ℝ b h) by ring]
    rw [htangent, hidentity]
    field_simp
  rw [hvalue] at hder
  exact hder

end SquareAntiprismVerification
