import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow020_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 20)=[-8,32,-128,320,-288,-448,688] := by decide +kernel
theorem functionalRow020_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 20)=[32,-256,960,-1152,-2240,4128] := by decide +kernel
theorem functionalRow020_den : Factored.FunctionalData.denominator 20=1 := by decide +kernel
theorem functionalRow020_polynomial : familyPolynomial (invariantMonomial (fullTag (20:Fin 102)))=functionalPolynomial 20 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (20:Fin 102)=(3,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow020_decode,functionalRow020_den]
  norm_num [functionalRow020_decode,functionalRow020_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow020_derivative : (functionalPolynomial (20:Fin 102)).derivative=functionalSlopePolynomial 20 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow020_decode,functionalRow020_slope_decode,functionalRow020_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow020_decode,functionalRow020_slope_decode,functionalRow020_den,integerPolynomial] <;> ring

theorem functionalRow021_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 21)=[24,-160,752,-2944,8416,-14272,10080] := by decide +kernel
theorem functionalRow021_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 21)=[-160,1504,-8832,33664,-71360,60480] := by decide +kernel
theorem functionalRow021_den : Factored.FunctionalData.denominator 21=1 := by decide +kernel
theorem functionalRow021_polynomial : familyPolynomial (invariantMonomial (fullTag (21:Fin 102)))=functionalPolynomial 21 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (21:Fin 102)=(4,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow021_decode,functionalRow021_den]
  norm_num [functionalRow021_decode,functionalRow021_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow021_derivative : (functionalPolynomial (21:Fin 102)).derivative=functionalSlopePolynomial 21 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow021_decode,functionalRow021_slope_decode,functionalRow021_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow021_decode,functionalRow021_slope_decode,functionalRow021_den,integerPolynomial] <;> ring

theorem functionalRow022_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 22)=[152,-960,4800,-16640,38880,-54720,34368] := by decide +kernel
theorem functionalRow022_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 22)=[-960,9600,-49920,155520,-273600,206208] := by decide +kernel
theorem functionalRow022_den : Factored.FunctionalData.denominator 22=1 := by decide +kernel
theorem functionalRow022_polynomial : familyPolynomial (invariantMonomial (fullTag (22:Fin 102)))=functionalPolynomial 22 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (22:Fin 102)=(6,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow022_decode,functionalRow022_den]
  norm_num [functionalRow022_decode,functionalRow022_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow022_derivative : (functionalPolynomial (22:Fin 102)).derivative=functionalSlopePolynomial 22 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow022_decode,functionalRow022_slope_decode,functionalRow022_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow022_decode,functionalRow022_slope_decode,functionalRow022_den,integerPolynomial] <;> ring

theorem functionalRow023_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 23)=[2,-32,202,-644,1022,-520,-530,620] := by decide +kernel
theorem functionalRow023_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 23)=[-32,404,-1932,4088,-2600,-3180,4340] := by decide +kernel
theorem functionalRow023_den : Factored.FunctionalData.denominator 23=1 := by decide +kernel
theorem functionalRow023_polynomial : familyPolynomial (invariantMonomial (fullTag (23:Fin 102)))=functionalPolynomial 23 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (23:Fin 102)=(0,2,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow023_decode,functionalRow023_den]
  norm_num [functionalRow023_decode,functionalRow023_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow023_derivative : (functionalPolynomial (23:Fin 102)).derivative=functionalSlopePolynomial 23 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow023_decode,functionalRow023_slope_decode,functionalRow023_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow023_decode,functionalRow023_slope_decode,functionalRow023_den,integerPolynomial] <;> ring

theorem functionalRow024_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 24)=[-4,32,-88,40,180,-320,176,-40] := by decide +kernel
theorem functionalRow024_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 24)=[32,-176,120,720,-1600,1056,-280] := by decide +kernel
theorem functionalRow024_den : Factored.FunctionalData.denominator 24=1 := by decide +kernel
theorem functionalRow024_polynomial : familyPolynomial (invariantMonomial (fullTag (24:Fin 102)))=functionalPolynomial 24 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (24:Fin 102)=(1,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow024_decode,functionalRow024_den]
  norm_num [functionalRow024_decode,functionalRow024_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow024_derivative : (functionalPolynomial (24:Fin 102)).derivative=functionalSlopePolynomial 24 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow024_decode,functionalRow024_slope_decode,functionalRow024_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow024_decode,functionalRow024_slope_decode,functionalRow024_den,integerPolynomial] <;> ring

theorem functionalRow025_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 25)=[2,-36,258,-848,974,1500,-5210,4056] := by decide +kernel
theorem functionalRow025_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 25)=[-36,516,-2544,3896,7500,-31260,28392] := by decide +kernel
theorem functionalRow025_den : Factored.FunctionalData.denominator 25=1 := by decide +kernel
theorem functionalRow025_polynomial : familyPolynomial (invariantMonomial (fullTag (25:Fin 102)))=functionalPolynomial 25 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (25:Fin 102)=(1,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow025_decode,functionalRow025_den]
  norm_num [functionalRow025_decode,functionalRow025_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow025_derivative : (functionalPolynomial (25:Fin 102)).derivative=functionalSlopePolynomial 25 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow025_decode,functionalRow025_slope_decode,functionalRow025_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow025_decode,functionalRow025_slope_decode,functionalRow025_den,integerPolynomial] <;> ring

theorem functionalRow026_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 26)=[-4,48,-184,352,-556,1120,-1808,1200] := by decide +kernel
theorem functionalRow026_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 26)=[48,-368,1056,-2224,5600,-10848,8400] := by decide +kernel
theorem functionalRow026_den : Factored.FunctionalData.denominator 26=1 := by decide +kernel
theorem functionalRow026_polynomial : familyPolynomial (invariantMonomial (fullTag (26:Fin 102)))=functionalPolynomial 26 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (26:Fin 102)=(2,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow026_decode,functionalRow026_den]
  norm_num [functionalRow026_decode,functionalRow026_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow026_derivative : (functionalPolynomial (26:Fin 102)).derivative=functionalSlopePolynomial 26 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow026_decode,functionalRow026_slope_decode,functionalRow026_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow026_decode,functionalRow026_slope_decode,functionalRow026_den,integerPolynomial] <;> ring

theorem functionalRow027_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 27)=[-4,24,-88,608,-3724,12200,-19856,12736] := by decide +kernel
theorem functionalRow027_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 27)=[24,-176,1824,-14896,61000,-119136,89152] := by decide +kernel
theorem functionalRow027_den : Factored.FunctionalData.denominator 27=1 := by decide +kernel
theorem functionalRow027_polynomial : familyPolynomial (invariantMonomial (fullTag (27:Fin 102)))=functionalPolynomial 27 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (27:Fin 102)=(3,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow027_decode,functionalRow027_den]
  norm_num [functionalRow027_decode,functionalRow027_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow027_derivative : (functionalPolynomial (27:Fin 102)).derivative=functionalSlopePolynomial 27 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow027_decode,functionalRow027_slope_decode,functionalRow027_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow027_decode,functionalRow027_slope_decode,functionalRow027_den,integerPolynomial] <;> ring

theorem functionalRow028_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 28)=[8,0,-176,1056,-3328,6880,-8640,4896] := by decide +kernel
theorem functionalRow028_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 28)=[0,-352,3168,-13312,34400,-51840,34272] := by decide +kernel
theorem functionalRow028_den : Factored.FunctionalData.denominator 28=1 := by decide +kernel
theorem functionalRow028_polynomial : familyPolynomial (invariantMonomial (fullTag (28:Fin 102)))=functionalPolynomial 28 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (28:Fin 102)=(4,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow028_decode,functionalRow028_den]
  norm_num [functionalRow028_decode,functionalRow028_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow028_derivative : (functionalPolynomial (28:Fin 102)).derivative=functionalSlopePolynomial 28 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow028_decode,functionalRow028_slope_decode,functionalRow028_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow028_decode,functionalRow028_slope_decode,functionalRow028_den,integerPolynomial] <;> ring

theorem functionalRow029_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 29)=[8,-192,656,1120,-14080,44960,-67904,41312] := by decide +kernel
theorem functionalRow029_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 29)=[-192,1312,3360,-56320,224800,-407424,289184] := by decide +kernel
theorem functionalRow029_den : Factored.FunctionalData.denominator 29=1 := by decide +kernel
theorem functionalRow029_polynomial : familyPolynomial (invariantMonomial (fullTag (29:Fin 102)))=functionalPolynomial 29 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (29:Fin 102)=(5,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow029_decode,functionalRow029_den]
  norm_num [functionalRow029_decode,functionalRow029_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow029_derivative : (functionalPolynomial (29:Fin 102)).derivative=functionalSlopePolynomial 29 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow029_decode,functionalRow029_slope_decode,functionalRow029_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow029_decode,functionalRow029_slope_decode,functionalRow029_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
