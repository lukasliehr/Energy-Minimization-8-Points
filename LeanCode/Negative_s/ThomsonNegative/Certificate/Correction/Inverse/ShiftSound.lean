import ThomsonNegative.Certificate.Correction.Inverse.ShiftKernel
import ThomsonNegative.Certificate.Bridges.RFPolynomial

noncomputable section
namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Packed ThomsonNegative.Structure.Exact ThomsonNegative.Structure.PolynomialLift

lemma recordInts_eq (x : ℕ) : recordInts x=recCoeffs x := by
  unfold recordInts
  dsimp only
  unfold recCoeffs digitsN
  rw [List.map_reverse]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  change ((fld (Nat.shiftRight x 32) (Nat.mul (hdrW x) k) (hdrW x):ℕ):ℤ)-
      ((Nat.pow 2 (Nat.sub (hdrW x) 1):ℕ):ℤ) = _
  rw [show fld (Nat.shiftRight x 32) (Nat.mul (hdrW x) k) (hdrW x)=
      (Nat.shiftRight x 32)/2^(hdrW x*k)%2^(hdrW x) from by
    unfold fld mask
    rw [land_mask,nat_shiftRight]
    rfl]
  push_cast
  rfl

lemma addI_eq (a b : List ℤ) : addI a b=addL a b := by
  induction a generalizing b with
  | nil => rfl
  | cons x xs ih => cases b <;> simp only [addI,addL,ih]; rfl

lemma scaleI_eq (c : ℤ) (a : List ℤ) : scaleI c a=scaleL c a := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [scaleI,scaleL,ih]; rfl

lemma affineStep_eval (L : List ℤ) (c d carry : ℤ) (u : ℝ) :
    evalZ (affineStep c d carry L) u=(carry:ℝ)+((c:ℝ)+(d:ℝ)*u)*evalZ L u := by
  induction L generalizing carry with
  | nil => simp [affineStep,evalZ,horner]
  | cons x xs ih =>
    simp only [affineStep,Bridges.evalZ_cons,ih,Int.add_def,Int.mul_def,Int.cast_add,Int.cast_mul]
    ring

lemma shiftI_eval (L : List ℤ) (c d : ℤ) (hd : d≠0) (u : ℝ) :
    evalZ (shiftI L c d) u=(d:ℝ)^L.length*evalZ L (u+(c:ℝ)/d) := by
  have hd' : (d:ℝ)≠0 := Int.cast_ne_zero.mpr hd
  induction L with
  | nil => simp [shiftI,evalZ,horner]
  | cons x xs ih =>
    rw [shiftI,affineStep_eval,ih,Bridges.evalZ_cons]
    simp only [List.length_cons,Int.cast_mul,Int.cast_pow]
    field_simp [hd']
    ring

/-- The checked translated record represents the same rational-function
numerator at `u+83/256`, with one common positive scale `256^degree`. -/
theorem shiftCheck_sound (degree source shifted : ℕ)
    (h : shiftCheck degree source shifted=true) (u : ℝ) :
    evalZ (recCoeffs shifted) u=(256:ℝ)^degree *
      evalZ (recCoeffs source) (u+83/256) := by
  simp only [shiftCheck,Bool.and_eq_true,Nat.ble_eq,beq_iff_eq] at h
  rw [recordInts_eq,recordInts_eq,scaleI_eq] at h
  rw [h.2,evalZ_scaleL,shiftI_eval _ 83 256 (by norm_num)]
  have hl : (recCoeffs source).length=hdrL source := length_recCoeffs source
  norm_num only [Int.cast_pow,Int.cast_ofNat]
  rw [← mul_assoc,← pow_add,hl,hdrL,Nat.sub_add_cancel h.1]

#print axioms shiftCheck_sound
end ThomsonNegative.Certificate.Correction.Inverse
