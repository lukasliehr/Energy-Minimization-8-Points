import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow010_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 10)=[88,-384,1344,-2688,2336] := by decide +kernel
theorem functionalRow010_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 10)=[-384,2688,-8064,9344] := by decide +kernel
theorem functionalRow010_den : Factored.FunctionalData.denominator 10=1 := by decide +kernel
theorem functionalRow010_polynomial : familyPolynomial (invariantMonomial (fullTag (10:Fin 102)))=functionalPolynomial 10 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (10:Fin 102)=(4,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow010_decode,functionalRow010_den]
  norm_num [functionalRow010_decode,functionalRow010_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow010_derivative : (functionalPolynomial (10:Fin 102)).derivative=functionalSlopePolynomial 10 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow010_decode,functionalRow010_slope_decode,functionalRow010_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow010_decode,functionalRow010_slope_decode,functionalRow010_den,integerPolynomial] <;> ring

theorem functionalRow011_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 11)=[-4,48,-168,240,-140] := by decide +kernel
theorem functionalRow011_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 11)=[48,-336,720,-560] := by decide +kernel
theorem functionalRow011_den : Factored.FunctionalData.denominator 11=1 := by decide +kernel
theorem functionalRow011_polynomial : familyPolynomial (invariantMonomial (fullTag (11:Fin 102)))=functionalPolynomial 11 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (11:Fin 102)=(0,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow011_decode,functionalRow011_den]
  norm_num [functionalRow011_decode,functionalRow011_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow011_derivative : (functionalPolynomial (11:Fin 102)).derivative=functionalSlopePolynomial 11 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow011_decode,functionalRow011_slope_decode,functionalRow011_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow011_decode,functionalRow011_slope_decode,functionalRow011_den,integerPolynomial] <;> ring

theorem functionalRow012_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 12)=[-4,40,-200,576,-1004,760] := by decide +kernel
theorem functionalRow012_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 12)=[40,-400,1728,-4016,3800] := by decide +kernel
theorem functionalRow012_den : Factored.FunctionalData.denominator 12=1 := by decide +kernel
theorem functionalRow012_polynomial : familyPolynomial (invariantMonomial (fullTag (12:Fin 102)))=functionalPolynomial 12 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (12:Fin 102)=(1,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow012_decode,functionalRow012_den]
  norm_num [functionalRow012_decode,functionalRow012_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow012_derivative : (functionalPolynomial (12:Fin 102)).derivative=functionalSlopePolynomial 12 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow012_decode,functionalRow012_slope_decode,functionalRow012_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow012_decode,functionalRow012_slope_decode,functionalRow012_den,integerPolynomial] <;> ring

theorem functionalRow013_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 13)=[8,-16,-48,288,-512,400] := by decide +kernel
theorem functionalRow013_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 13)=[-16,-96,864,-2048,2000] := by decide +kernel
theorem functionalRow013_den : Factored.FunctionalData.denominator 13=1 := by decide +kernel
theorem functionalRow013_polynomial : familyPolynomial (invariantMonomial (fullTag (13:Fin 102)))=functionalPolynomial 13 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (13:Fin 102)=(2,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow013_decode,functionalRow013_den]
  norm_num [functionalRow013_decode,functionalRow013_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow013_derivative : (functionalPolynomial (13:Fin 102)).derivative=functionalSlopePolynomial 13 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow013_decode,functionalRow013_slope_decode,functionalRow013_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow013_decode,functionalRow013_slope_decode,functionalRow013_den,integerPolynomial] <;> ring

theorem functionalRow014_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 14)=[8,-80,16,1056,-2944,2640] := by decide +kernel
theorem functionalRow014_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 14)=[-80,32,3168,-11776,13200] := by decide +kernel
theorem functionalRow014_den : Factored.FunctionalData.denominator 14=1 := by decide +kernel
theorem functionalRow014_polynomial : familyPolynomial (invariantMonomial (fullTag (14:Fin 102)))=functionalPolynomial 14 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (14:Fin 102)=(3,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow014_decode,functionalRow014_den]
  norm_num [functionalRow014_decode,functionalRow014_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow014_derivative : (functionalPolynomial (14:Fin 102)).derivative=functionalSlopePolynomial 14 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow014_decode,functionalRow014_slope_decode,functionalRow014_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow014_decode,functionalRow014_slope_decode,functionalRow014_den,integerPolynomial] <;> ring

theorem functionalRow015_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 15)=[-24,-160,0,2880,-8320,7520] := by decide +kernel
theorem functionalRow015_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 15)=[-160,0,8640,-33280,37600] := by decide +kernel
theorem functionalRow015_den : Factored.FunctionalData.denominator 15=1 := by decide +kernel
theorem functionalRow015_polynomial : familyPolynomial (invariantMonomial (fullTag (15:Fin 102)))=functionalPolynomial 15 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (15:Fin 102)=(5,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow015_decode,functionalRow015_den]
  norm_num [functionalRow015_decode,functionalRow015_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow015_derivative : (functionalPolynomial (15:Fin 102)).derivative=functionalSlopePolynomial 15 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow015_decode,functionalRow015_slope_decode,functionalRow015_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow015_decode,functionalRow015_slope_decode,functionalRow015_den,integerPolynomial] <;> ring

theorem functionalRow016_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 16)=[4,-32,96,-112,60,-80,120] := by decide +kernel
theorem functionalRow016_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 16)=[-32,192,-336,240,-400,720] := by decide +kernel
theorem functionalRow016_den : Factored.FunctionalData.denominator 16=1 := by decide +kernel
theorem functionalRow016_polynomial : familyPolynomial (invariantMonomial (fullTag (16:Fin 102)))=functionalPolynomial 16 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (16:Fin 102)=(0,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow016_decode,functionalRow016_den]
  norm_num [functionalRow016_decode,functionalRow016_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow016_derivative : (functionalPolynomial (16:Fin 102)).derivative=functionalSlopePolynomial 16 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow016_decode,functionalRow016_slope_decode,functionalRow016_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow016_decode,functionalRow016_slope_decode,functionalRow016_den,integerPolynomial] <;> ring

theorem functionalRow017_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 17)=[-2,36,-282,968,-1470,660,258] := by decide +kernel
theorem functionalRow017_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 17)=[36,-564,2904,-5880,3300,1548] := by decide +kernel
theorem functionalRow017_den : Factored.FunctionalData.denominator 17=1 := by decide +kernel
theorem functionalRow017_polynomial : familyPolynomial (invariantMonomial (fullTag (17:Fin 102)))=functionalPolynomial 17 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (17:Fin 102)=(0,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow017_decode,functionalRow017_den]
  norm_num [functionalRow017_decode,functionalRow017_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow017_derivative : (functionalPolynomial (17:Fin 102)).derivative=functionalSlopePolynomial 17 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow017_decode,functionalRow017_slope_decode,functionalRow017_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow017_decode,functionalRow017_slope_decode,functionalRow017_den,integerPolynomial] <;> ring

theorem functionalRow018_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 18)=[4,-40,112,-96,60,-280,360] := by decide +kernel
theorem functionalRow018_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 18)=[-40,224,-288,240,-1400,2160] := by decide +kernel
theorem functionalRow018_den : Factored.FunctionalData.denominator 18=1 := by decide +kernel
theorem functionalRow018_polynomial : familyPolynomial (invariantMonomial (fullTag (18:Fin 102)))=functionalPolynomial 18 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (18:Fin 102)=(1,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow018_decode,functionalRow018_den]
  norm_num [functionalRow018_decode,functionalRow018_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow018_derivative : (functionalPolynomial (18:Fin 102)).derivative=functionalSlopePolynomial 18 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow018_decode,functionalRow018_slope_decode,functionalRow018_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow018_decode,functionalRow018_slope_decode,functionalRow018_den,integerPolynomial] <;> ring

theorem functionalRow019_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 19)=[12,-96,328,-816,2196,-4176,3248] := by decide +kernel
theorem functionalRow019_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 19)=[-96,656,-2448,8784,-20880,19488] := by decide +kernel
theorem functionalRow019_den : Factored.FunctionalData.denominator 19=1 := by decide +kernel
theorem functionalRow019_polynomial : familyPolynomial (invariantMonomial (fullTag (19:Fin 102)))=functionalPolynomial 19 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (19:Fin 102)=(2,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow019_decode,functionalRow019_den]
  norm_num [functionalRow019_decode,functionalRow019_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow019_derivative : (functionalPolynomial (19:Fin 102)).derivative=functionalSlopePolynomial 19 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow019_decode,functionalRow019_slope_decode,functionalRow019_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow019_decode,functionalRow019_slope_decode,functionalRow019_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
