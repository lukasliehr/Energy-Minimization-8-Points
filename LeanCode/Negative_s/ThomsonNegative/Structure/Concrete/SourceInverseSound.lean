import ThomsonNegative.Structure.Concrete.SourceOperator
import ThomsonNegative.Certificate.Correction.Inverse.Kernel
import ThomsonNegative.Certificate.Correction.Inverse.ShiftSound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed
open ThomsonNegative.Certificate.Correction.Inverse

structure SourceIdentityChecks : Prop where
  denominators : ∀j : Fin 68,(denominatorEquation j.val).check=true
  lifts : ∀i j : Fin 68,(liftEquation i.val j.val).check=true
  inverse : ∀i j : Fin 68,(inverseEquation i.val j.val).check=true
  shiftNumerators : ∀i j : Fin 68,
    shiftCheck shiftDegree (Factored.HighData.A.numerator i.val j.val)
      (shiftANumerator i.val j.val)=true
  shiftDenom : shiftCheck shiftDegree Factored.HighData.A.denominator shiftDenominator=true

namespace SourceIdentityChecks

theorem denominator_identity (C : SourceIdentityChecks) (u : ℝ) (j : Fin 68) :
    evalZ (recCoeffs (gamma j.val)) u*
      evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator j.val)) u=
    evalZ (recCoeffs commonDenominator) u := by
  have h := (denominatorEquation j.val).sound (C.denominators j) u
  simpa [denominatorEquation,oneRecord_decode,evalZ,horner] using h

theorem lift_identity (C : SourceIdentityChecks) (u : ℝ) (i j : Fin 68) :
    evalZ (recCoeffs (shiftANumerator i.val j.val)) u*
      evalZ (recCoeffs (gamma j.val)) u=
    evalZ (recCoeffs (liftANumerator i.val j.val)) u := by
  have h := (liftEquation i.val j.val).sound (C.lifts i j) u
  simpa [liftEquation,oneRecord_decode,evalZ,horner] using h

theorem gamma23_decode : recCoeffs (gamma 23)=[1073741824] := by decide +kernel

theorem common_nonzero (C : SourceIdentityChecks) (u : ℝ)
    (h23 : evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator 23)) u≠0) :
    evalZ (recCoeffs commonDenominator) u≠0 := by
  have h := C.denominator_identity u (23:Fin 68)
  change evalZ (recCoeffs (gamma 23)) u*
    evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator 23)) u=
    evalZ (recCoeffs commonDenominator) u at h
  rw [← h]
  apply mul_ne_zero _ h23
  rw [gamma23_decode]
  norm_num [evalZ,horner]

theorem source_denominator_nonzero (C : SourceIdentityChecks) (u : ℝ)
    (h23 : evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator 23)) u≠0)
    (j : Fin 68) :
    evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator j.val)) u≠0 := by
  have h := C.denominator_identity u j
  have hg := C.common_nonzero u h23
  intro hj
  rw [hj,mul_zero] at h
  exact hg h.symm

theorem source_common_entry (C : SourceIdentityChecks) (u : ℝ)
    (h23 : evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator 23)) u≠0)
    (i j : Fin 68) :
    sourceMatrix u i j=
      evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowNumerator i.val j.val)) u*
        evalZ (recCoeffs (gamma i.val)) u/evalZ (recCoeffs commonDenominator) u := by
  apply (div_eq_div_iff (C.source_denominator_nonzero u h23 i) (C.common_nonzero u h23)).mpr
  rw [← C.denominator_identity u i]
  ring

theorem inverse_identity (C : SourceIdentityChecks) (u : ℝ) (i j : Fin 68) :
    (∑ k : Fin 68,evalZ (recCoeffs (liftANumerator i.val k.val)) u*
      evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowNumerator k.val j.val)) u)=
      if i=j then evalZ (recCoeffs shiftDenominator) u*evalZ (recCoeffs commonDenominator) u else 0 := by
  have h := (inverseEquation i.val j.val).sound (C.inverse i j) u
  change (∑ k∈Finset.range 68,evalZ (recCoeffs (liftANumerator i.val k)) u*
    evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowNumerator k j.val)) u)*
      evalZ (recCoeffs oneRecord) u=
    evalZ (recCoeffs (cond (Nat.beq i.val j.val) shiftDenominator zeroRecord)) u*
      evalZ (recCoeffs commonDenominator) u*evalZ (recCoeffs oneRecord) u at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  by_cases hij : i=j
  · subst j
    simpa [oneRecord_decode,evalZ,horner] using h
  · have hv : i.val≠j.val := fun he => hij (Fin.ext he)
    have hbeq : Nat.beq i.val j.val=false := by
      cases he : Nat.beq i.val j.val
      · rfl
      · exact False.elim (hv (Nat.eq_of_beq_eq_true he))
    simpa [hij,hbeq,oneRecord_decode,zeroRecord_decode,evalZ,horner] using h

theorem shifted_matrix_inverse (C : SourceIdentityChecks) (u : ℝ)
    (hA : evalZ (recCoeffs shiftDenominator) u≠0)
    (h23 : evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator 23)) u≠0) :
    shiftedA.eval u*sourceMatrix u=1 := by
  have hG := C.common_nonzero u h23
  ext i j
  change (∑ k : Fin 68,(evalZ (recCoeffs (shiftANumerator i.val k.val)) u/
      evalZ (recCoeffs shiftDenominator) u)*sourceMatrix u k j)=(1 : Matrix (Fin 68) (Fin 68) ℝ) i j
  simp_rw [C.source_common_entry u h23]
  have he : (∑ k : Fin 68,(evalZ (recCoeffs (shiftANumerator i.val k.val)) u/
        evalZ (recCoeffs shiftDenominator) u)*
        (evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowNumerator k.val j.val)) u*
          evalZ (recCoeffs (gamma k.val)) u/evalZ (recCoeffs commonDenominator) u))=
      (∑ k : Fin 68,evalZ (recCoeffs (liftANumerator i.val k.val)) u*
        evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowNumerator k.val j.val)) u)/
        (evalZ (recCoeffs shiftDenominator) u*evalZ (recCoeffs commonDenominator) u) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← C.lift_identity u i k]
    field_simp
    <;> ring
  rw [he,C.inverse_identity]
  by_cases hij : i=j <;> simp [hij,Matrix.one_apply,hA,hG]

theorem shifted_matrix (C : SourceIdentityChecks) (u : ℝ) :
    shiftedA.eval u=Factored.HighData.A.eval (u+83/256) := by
  ext i j
  change evalZ (recCoeffs (shiftANumerator i.val j.val)) u/
      evalZ (recCoeffs shiftDenominator) u=_
  rw [shiftCheck_sound _ _ _ (C.shiftNumerators i j) u,
    shiftCheck_sound _ _ _ C.shiftDenom u]
  have hn : (256:ℝ)^shiftDegree≠0 := by positivity
  rw [mul_div_mul_left _ _ hn]
  rfl

theorem shifted_denominator_nonzero (C : SourceIdentityChecks) (a : ℝ)
    (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    evalZ (recCoeffs shiftDenominator) (a-83/256)≠0 := by
  rw [shiftCheck_sound _ _ _ C.shiftDenom]
  simp only [sub_add_cancel]
  exact mul_ne_zero (by positivity) (Factored.A_regular a ha hb)

theorem matrix_inverse (C : SourceIdentityChecks) (a : ℝ)
    (ha : (5:ℝ)/16≤a) (hb : a<1/3)
    (h23 : evalZ (recCoeffs (ThomsonNegative.Certificate.Correction.Source.rowDenominator 23)) (a-83/256)≠0) :
    Factored.HighData.A.eval a*sourceMatrix (a-83/256)=1 := by
  have h := C.shifted_matrix_inverse (a-83/256) (C.shifted_denominator_nonzero a ha hb) h23
  rw [C.shifted_matrix] at h
  simpa only [sub_add_cancel] using h

end SourceIdentityChecks

#print axioms SourceIdentityChecks.matrix_inverse
end ThomsonNegative.Structure.Concrete
