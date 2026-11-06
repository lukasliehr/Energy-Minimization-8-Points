import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow000_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 0)=[56] := by decide +kernel
theorem functionalRow000_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 0)=[] := by decide +kernel
theorem functionalRow000_den : Factored.FunctionalData.denominator 0=1 := by decide +kernel
theorem functionalRow000_polynomial : familyPolynomial (invariantMonomial (fullTag (0:Fin 102)))=functionalPolynomial 0 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (0:Fin 102)=(0,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow000_decode,functionalRow000_den]
  norm_num [functionalRow000_decode,functionalRow000_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow000_derivative : (functionalPolynomial (0:Fin 102)).derivative=functionalSlopePolynomial 0 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow000_decode,functionalRow000_slope_decode,functionalRow000_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow000_decode,functionalRow000_slope_decode,functionalRow000_den,integerPolynomial] <;> ring

theorem functionalRow001_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 1)=[-24] := by decide +kernel
theorem functionalRow001_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 1)=[] := by decide +kernel
theorem functionalRow001_den : Factored.FunctionalData.denominator 1=1 := by decide +kernel
theorem functionalRow001_polynomial : familyPolynomial (invariantMonomial (fullTag (1:Fin 102)))=functionalPolynomial 1 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (1:Fin 102)=(1,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow001_decode,functionalRow001_den]
  norm_num [functionalRow001_decode,functionalRow001_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow001_derivative : (functionalPolynomial (1:Fin 102)).derivative=functionalSlopePolynomial 1 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow001_decode,functionalRow001_slope_decode,functionalRow001_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow001_decode,functionalRow001_slope_decode,functionalRow001_den,integerPolynomial] <;> ring

theorem functionalRow002_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 2)=[-8,32,-48] := by decide +kernel
theorem functionalRow002_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 2)=[32,-96] := by decide +kernel
theorem functionalRow002_den : Factored.FunctionalData.denominator 2=1 := by decide +kernel
theorem functionalRow002_polynomial : familyPolynomial (invariantMonomial (fullTag (2:Fin 102)))=functionalPolynomial 2 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (2:Fin 102)=(0,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow002_decode,functionalRow002_den]
  norm_num [functionalRow002_decode,functionalRow002_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow002_derivative : (functionalPolynomial (2:Fin 102)).derivative=functionalSlopePolynomial 2 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow002_decode,functionalRow002_slope_decode,functionalRow002_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow002_decode,functionalRow002_slope_decode,functionalRow002_den,integerPolynomial] <;> ring

theorem functionalRow003_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 3)=[56,-128,192] := by decide +kernel
theorem functionalRow003_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 3)=[-128,384] := by decide +kernel
theorem functionalRow003_den : Factored.FunctionalData.denominator 3=1 := by decide +kernel
theorem functionalRow003_polynomial : familyPolynomial (invariantMonomial (fullTag (3:Fin 102)))=functionalPolynomial 3 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (3:Fin 102)=(2,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow003_decode,functionalRow003_den]
  norm_num [functionalRow003_decode,functionalRow003_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow003_derivative : (functionalPolynomial (3:Fin 102)).derivative=functionalSlopePolynomial 3 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow003_decode,functionalRow003_slope_decode,functionalRow003_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow003_decode,functionalRow003_slope_decode,functionalRow003_den,integerPolynomial] <;> ring

theorem functionalRow004_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 4)=[8,-32,16,64] := by decide +kernel
theorem functionalRow004_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 4)=[-32,32,192] := by decide +kernel
theorem functionalRow004_den : Factored.FunctionalData.denominator 4=1 := by decide +kernel
theorem functionalRow004_polynomial : familyPolynomial (invariantMonomial (fullTag (4:Fin 102)))=functionalPolynomial 4 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (4:Fin 102)=(0,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow004_decode,functionalRow004_den]
  norm_num [functionalRow004_decode,functionalRow004_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow004_derivative : (functionalPolynomial (4:Fin 102)).derivative=functionalSlopePolynomial 4 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow004_decode,functionalRow004_slope_decode,functionalRow004_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow004_decode,functionalRow004_slope_decode,functionalRow004_den,integerPolynomial] <;> ring

theorem functionalRow005_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 5)=[8,-32,-48,192] := by decide +kernel
theorem functionalRow005_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 5)=[-32,-96,576] := by decide +kernel
theorem functionalRow005_den : Factored.FunctionalData.denominator 5=1 := by decide +kernel
theorem functionalRow005_polynomial : familyPolynomial (invariantMonomial (fullTag (5:Fin 102)))=functionalPolynomial 5 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (5:Fin 102)=(1,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow005_decode,functionalRow005_den]
  norm_num [functionalRow005_decode,functionalRow005_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow005_derivative : (functionalPolynomial (5:Fin 102)).derivative=functionalSlopePolynomial 5 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow005_decode,functionalRow005_slope_decode,functionalRow005_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow005_decode,functionalRow005_slope_decode,functionalRow005_den,integerPolynomial] <;> ring

theorem functionalRow006_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 6)=[-24,0,-192,384] := by decide +kernel
theorem functionalRow006_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 6)=[0,-384,1152] := by decide +kernel
theorem functionalRow006_den : Factored.FunctionalData.denominator 6=1 := by decide +kernel
theorem functionalRow006_polynomial : familyPolynomial (invariantMonomial (fullTag (6:Fin 102)))=functionalPolynomial 6 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (6:Fin 102)=(3,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow006_decode,functionalRow006_den]
  norm_num [functionalRow006_decode,functionalRow006_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow006_derivative : (functionalPolynomial (6:Fin 102)).derivative=functionalSlopePolynomial 6 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow006_decode,functionalRow006_slope_decode,functionalRow006_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow006_decode,functionalRow006_slope_decode,functionalRow006_den,integerPolynomial] <;> ring

theorem functionalRow007_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 7)=[12,-80,280,-528,436] := by decide +kernel
theorem functionalRow007_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 7)=[-80,560,-1584,1744] := by decide +kernel
theorem functionalRow007_den : Factored.FunctionalData.denominator 7=1 := by decide +kernel
theorem functionalRow007_polynomial : familyPolynomial (invariantMonomial (fullTag (7:Fin 102)))=functionalPolynomial 7 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (7:Fin 102)=(0,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow007_decode,functionalRow007_den]
  norm_num [functionalRow007_decode,functionalRow007_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow007_derivative : (functionalPolynomial (7:Fin 102)).derivative=functionalSlopePolynomial 7 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow007_decode,functionalRow007_slope_decode,functionalRow007_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow007_decode,functionalRow007_slope_decode,functionalRow007_den,integerPolynomial] <;> ring

theorem functionalRow008_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 8)=[-8,32,-48] := by decide +kernel
theorem functionalRow008_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 8)=[32,-96] := by decide +kernel
theorem functionalRow008_den : Factored.FunctionalData.denominator 8=1 := by decide +kernel
theorem functionalRow008_polynomial : familyPolynomial (invariantMonomial (fullTag (8:Fin 102)))=functionalPolynomial 8 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (8:Fin 102)=(1,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow008_decode,functionalRow008_den]
  norm_num [functionalRow008_decode,functionalRow008_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow008_derivative : (functionalPolynomial (8:Fin 102)).derivative=functionalSlopePolynomial 8 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow008_decode,functionalRow008_slope_decode,functionalRow008_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow008_decode,functionalRow008_slope_decode,functionalRow008_den,integerPolynomial] <;> ring

theorem functionalRow009_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 9)=[8,-32,176,-576,592] := by decide +kernel
theorem functionalRow009_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 9)=[-32,352,-1728,2368] := by decide +kernel
theorem functionalRow009_den : Factored.FunctionalData.denominator 9=1 := by decide +kernel
theorem functionalRow009_polynomial : familyPolynomial (invariantMonomial (fullTag (9:Fin 102)))=functionalPolynomial 9 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (9:Fin 102)=(2,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow009_decode,functionalRow009_den]
  norm_num [functionalRow009_decode,functionalRow009_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow009_derivative : (functionalPolynomial (9:Fin 102)).derivative=functionalSlopePolynomial 9 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow009_decode,functionalRow009_slope_decode,functionalRow009_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow009_decode,functionalRow009_slope_decode,functionalRow009_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
