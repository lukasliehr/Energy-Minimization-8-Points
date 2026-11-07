import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow090_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 90)=[-2,24,-114,260,-306,432,-2214,7716,-15960,20208,-13776,2592,1308] := by decide +kernel
theorem functionalRow090_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 90)=[24,-228,780,-1224,2160,-13284,54012,-127680,181872,-137760,28512,15696] := by decide +kernel
theorem functionalRow090_den : Factored.FunctionalData.denominator 90=1 := by decide +kernel
theorem functionalRow090_polynomial : familyPolynomial (invariantMonomial (fullTag (90:Fin 102)))=functionalPolynomial 90 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (90:Fin 102)=(3,0,3) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow090_decode,functionalRow090_den]
  norm_num [functionalRow090_decode,functionalRow090_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow090_derivative : (functionalPolynomial (90:Fin 102)).derivative=functionalSlopePolynomial 90 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow090_decode,functionalRow090_slope_decode,functionalRow090_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow090_decode,functionalRow090_slope_decode,functionalRow090_den,integerPolynomial] <;> ring

theorem functionalRow091_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 91)=[1,-22,190,-896,2554,-4488,5680,-14316,62449,-185090,325210,-313460,128068] := by decide +kernel
theorem functionalRow091_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 91)=[-22,380,-2688,10216,-22440,34080,-100212,499592,-1665810,3252100,-3448060,1536816] := by decide +kernel
theorem functionalRow091_den : Factored.FunctionalData.denominator 91=1 := by decide +kernel
theorem functionalRow091_polynomial : familyPolynomial (invariantMonomial (fullTag (91:Fin 102)))=functionalPolynomial 91 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (91:Fin 102)=(3,3,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow091_decode,functionalRow091_den]
  norm_num [functionalRow091_decode,functionalRow091_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow091_derivative : (functionalPolynomial (91:Fin 102)).derivative=functionalSlopePolynomial 91 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow091_decode,functionalRow091_slope_decode,functionalRow091_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow091_decode,functionalRow091_slope_decode,functionalRow091_den,integerPolynomial] <;> ring

theorem functionalRow092_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 92)=[-2,28,-146,336,58,-2660,8914,-19416,36816,-67488,101672,-96016,39800] := by decide +kernel
theorem functionalRow092_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 92)=[28,-292,1008,232,-13300,53484,-135912,294528,-607392,1016720,-1056176,477600] := by decide +kernel
theorem functionalRow092_den : Factored.FunctionalData.denominator 92=1 := by decide +kernel
theorem functionalRow092_polynomial : familyPolynomial (invariantMonomial (fullTag (92:Fin 102)))=functionalPolynomial 92 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (92:Fin 102)=(4,1,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow092_decode,functionalRow092_den]
  norm_num [functionalRow092_decode,functionalRow092_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow092_derivative : (functionalPolynomial (92:Fin 102)).derivative=functionalSlopePolynomial 92 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow092_decode,functionalRow092_slope_decode,functionalRow092_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow092_decode,functionalRow092_slope_decode,functionalRow092_den,integerPolynomial] <;> ring

theorem functionalRow093_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 93)=[5,-72,488,-2048,5824,-13688,49236,-247880,956697,-2405184,3757180,-3328120,1280098] := by decide +kernel
theorem functionalRow093_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 93)=[-72,976,-6144,23296,-68440,295416,-1735160,7653576,-21646656,37571800,-36609320,15361176] := by decide +kernel
theorem functionalRow093_den : Factored.FunctionalData.denominator 93=1 := by decide +kernel
theorem functionalRow093_polynomial : familyPolynomial (invariantMonomial (fullTag (93:Fin 102)))=functionalPolynomial 93 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (93:Fin 102)=(4,4,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow093_decode,functionalRow093_den]
  norm_num [functionalRow093_decode,functionalRow093_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow093_derivative : (functionalPolynomial (93:Fin 102)).derivative=functionalSlopePolynomial 93 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow093_decode,functionalRow093_slope_decode,functionalRow093_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow093_decode,functionalRow093_slope_decode,functionalRow093_den,integerPolynomial] <;> ring

theorem functionalRow094_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 94)=[-2,32,-274,1356,-4222,8408,-4022,-53892,271008,-719808,1154368,-1044608,409104] := by decide +kernel
theorem functionalRow094_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 94)=[32,-548,4068,-16888,42040,-24132,-377244,2168064,-6478272,11543680,-11490688,4909248] := by decide +kernel
theorem functionalRow094_den : Factored.FunctionalData.denominator 94=1 := by decide +kernel
theorem functionalRow094_polynomial : familyPolynomial (invariantMonomial (fullTag (94:Fin 102)))=functionalPolynomial 94 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (94:Fin 102)=(5,2,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow094_decode,functionalRow094_den]
  norm_num [functionalRow094_decode,functionalRow094_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow094_derivative : (functionalPolynomial (94:Fin 102)).derivative=functionalSlopePolynomial 94 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow094_decode,functionalRow094_slope_decode,functionalRow094_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow094_decode,functionalRow094_slope_decode,functionalRow094_den,integerPolynomial] <;> ring

theorem functionalRow095_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 95)=[4,-32,120,-400,2812,-15152,54376,-140368,277840,-434304,513688,-397232,144528] := by decide +kernel
theorem functionalRow095_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 95)=[-32,240,-1200,11248,-75760,326256,-982576,2222720,-3908736,5136880,-4369552,1734336] := by decide +kernel
theorem functionalRow095_den : Factored.FunctionalData.denominator 95=1 := by decide +kernel
theorem functionalRow095_polynomial : familyPolynomial (invariantMonomial (fullTag (95:Fin 102)))=functionalPolynomial 95 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (95:Fin 102)=(6,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow095_decode,functionalRow095_den]
  norm_num [functionalRow095_decode,functionalRow095_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow095_derivative : (functionalPolynomial (95:Fin 102)).derivative=functionalSlopePolynomial 95 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow095_decode,functionalRow095_slope_decode,functionalRow095_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow095_decode,functionalRow095_slope_decode,functionalRow095_den,integerPolynomial] <;> ring

theorem functionalRow096_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 96)=[14,-156,822,-2888,8742,-38124,233906,-1170384,4006632,-9097440,13180128,-11059584,4095748] := by decide +kernel
theorem functionalRow096_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 96)=[-156,1644,-8664,34968,-190620,1403436,-8192688,32053056,-81876960,131801280,-121655424,49148976] := by decide +kernel
theorem functionalRow096_den : Factored.FunctionalData.denominator 96=1 := by decide +kernel
theorem functionalRow096_polynomial : familyPolynomial (invariantMonomial (fullTag (96:Fin 102)))=functionalPolynomial 96 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (96:Fin 102)=(6,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow096_decode,functionalRow096_den]
  norm_num [functionalRow096_decode,functionalRow096_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow096_derivative : (functionalPolynomial (96:Fin 102)).derivative=functionalSlopePolynomial 96 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow096_decode,functionalRow096_slope_decode,functionalRow096_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow096_decode,functionalRow096_slope_decode,functionalRow096_den,integerPolynomial] <;> ring

theorem functionalRow097_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 97)=[4,-40,-216,3328,-16932,48008,-55496,-164304,1017904,-2652672,4046360,-3489712,1316304] := by decide +kernel
theorem functionalRow097_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 97)=[-40,-432,9984,-67728,240040,-332976,-1150128,8143232,-23874048,40463600,-38386832,15795648] := by decide +kernel
theorem functionalRow097_den : Factored.FunctionalData.denominator 97=1 := by decide +kernel
theorem functionalRow097_polynomial : familyPolynomial (invariantMonomial (fullTag (97:Fin 102)))=functionalPolynomial 97 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (97:Fin 102)=(7,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow097_decode,functionalRow097_den]
  norm_num [functionalRow097_decode,functionalRow097_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow097_derivative : (functionalPolynomial (97:Fin 102)).derivative=functionalSlopePolynomial 97 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow097_decode,functionalRow097_slope_decode,functionalRow097_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow097_decode,functionalRow097_slope_decode,functionalRow097_den,integerPolynomial] <;> ring

theorem functionalRow098_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 98)=[68,-816,5096,-22000,78124,-302592,1367520,-5503296,16434088,-33981344,45989840,-36701792,13109544] := by decide +kernel
theorem functionalRow098_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 98)=[-816,10192,-66000,312496,-1512960,8205120,-38523072,131472704,-305832096,459898400,-403719712,157314528] := by decide +kernel
theorem functionalRow098_den : Factored.FunctionalData.denominator 98=1 := by decide +kernel
theorem functionalRow098_polynomial : familyPolynomial (invariantMonomial (fullTag (98:Fin 102)))=functionalPolynomial 98 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (98:Fin 102)=(8,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow098_decode,functionalRow098_den]
  norm_num [functionalRow098_decode,functionalRow098_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow098_derivative : (functionalPolynomial (98:Fin 102)).derivative=functionalSlopePolynomial 98 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow098_decode,functionalRow098_slope_decode,functionalRow098_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow098_decode,functionalRow098_slope_decode,functionalRow098_den,integerPolynomial] <;> ring

theorem functionalRow099_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 99)=[-8,32,-1680,16320,-86592,282624,-509376,2688,2807040,-8403456,13058592,-11138112,4129344] := by decide +kernel
theorem functionalRow099_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 99)=[32,-3360,48960,-346368,1413120,-3056256,18816,22456320,-75631104,130585920,-122519232,49552128] := by decide +kernel
theorem functionalRow099_den : Factored.FunctionalData.denominator 99=1 := by decide +kernel
theorem functionalRow099_polynomial : familyPolynomial (invariantMonomial (fullTag (99:Fin 102)))=functionalPolynomial 99 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (99:Fin 102)=(9,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow099_decode,functionalRow099_den]
  norm_num [functionalRow099_decode,functionalRow099_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow099_derivative : (functionalPolynomial (99:Fin 102)).derivative=functionalSlopePolynomial 99 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow099_decode,functionalRow099_slope_decode,functionalRow099_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow099_decode,functionalRow099_slope_decode,functionalRow099_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
