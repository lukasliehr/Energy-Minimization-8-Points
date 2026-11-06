import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow050_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 50)=[8,32,-496,3392,-14144,41680,-92224,148576,-151104,70160] := by decide +kernel
theorem functionalRow050_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 50)=[32,-992,10176,-56576,208400,-553344,1040032,-1208832,631440] := by decide +kernel
theorem functionalRow050_den : Factored.FunctionalData.denominator 50=1 := by decide +kernel
theorem functionalRow050_polynomial : familyPolynomial (invariantMonomial (fullTag (50:Fin 102)))=functionalPolynomial 50 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (50:Fin 102)=(6,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow050_decode,functionalRow050_den]
  norm_num [functionalRow050_decode,functionalRow050_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow050_derivative : (functionalPolynomial (50:Fin 102)).derivative=functionalSlopePolynomial 50 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow050_decode,functionalRow050_slope_decode,functionalRow050_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow050_decode,functionalRow050_slope_decode,functionalRow050_den,integerPolynomial] <;> ring

theorem functionalRow051_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 51)=[8,-480,3152,-6272,-22848,200144,-680512,1315104,-1413056,657296] := by decide +kernel
theorem functionalRow051_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 51)=[-480,6304,-18816,-91392,1000720,-4083072,9205728,-11304448,5915664] := by decide +kernel
theorem functionalRow051_den : Factored.FunctionalData.denominator 51=1 := by decide +kernel
theorem functionalRow051_polynomial : familyPolynomial (invariantMonomial (fullTag (51:Fin 102)))=functionalPolynomial 51 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (51:Fin 102)=(7,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow051_decode,functionalRow051_den]
  norm_num [functionalRow051_decode,functionalRow051_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow051_derivative : (functionalPolynomial (51:Fin 102)).derivative=functionalSlopePolynomial 51 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow051_decode,functionalRow051_slope_decode,functionalRow051_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow051_decode,functionalRow051_slope_decode,functionalRow051_den,integerPolynomial] <;> ring

theorem functionalRow052_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 52)=[-24,-2016,13824,-32256,-64512,701568,-2376192,4443264,-4601088,2074848] := by decide +kernel
theorem functionalRow052_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 52)=[-2016,27648,-96768,-258048,3507840,-14257152,31102848,-36808704,18673632] := by decide +kernel
theorem functionalRow052_den : Factored.FunctionalData.denominator 52=1 := by decide +kernel
theorem functionalRow052_polynomial : familyPolynomial (invariantMonomial (fullTag (52:Fin 102)))=functionalPolynomial 52 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (52:Fin 102)=(9,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow052_decode,functionalRow052_den]
  norm_num [functionalRow052_decode,functionalRow052_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow052_derivative : (functionalPolynomial (52:Fin 102)).derivative=functionalSlopePolynomial 52 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow052_decode,functionalRow052_slope_decode,functionalRow052_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow052_decode,functionalRow052_slope_decode,functionalRow052_den,integerPolynomial] <;> ring

theorem functionalRow053_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 53)=[1,-20,170,-784,2118,-3304,2512,-208,-263,-1124,1022] := by decide +kernel
theorem functionalRow053_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 53)=[-20,340,-2352,8472,-16520,15072,-1456,-2104,-10116,10220] := by decide +kernel
theorem functionalRow053_den : Factored.FunctionalData.denominator 53=1 := by decide +kernel
theorem functionalRow053_polynomial : familyPolynomial (invariantMonomial (fullTag (53:Fin 102)))=functionalPolynomial 53 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (53:Fin 102)=(0,2,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow053_decode,functionalRow053_den]
  norm_num [functionalRow053_decode,functionalRow053_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow053_derivative : (functionalPolynomial (53:Fin 102)).derivative=functionalSlopePolynomial 53 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow053_decode,functionalRow053_slope_decode,functionalRow053_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow053_decode,functionalRow053_slope_decode,functionalRow053_den,integerPolynomial] <;> ring

theorem functionalRow054_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 54)=[-1,30,-415,3160,-15090,47444,-96870,116760,-57005,-27170,32949] := by decide +kernel
theorem functionalRow054_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 54)=[30,-830,9480,-60360,237220,-581220,817320,-456040,-244530,329490] := by decide +kernel
theorem functionalRow054_den : Factored.FunctionalData.denominator 54=2 := by decide +kernel
theorem functionalRow054_polynomial : familyPolynomial (invariantMonomial (fullTag (54:Fin 102)))=functionalPolynomial 54 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (54:Fin 102)=(0,5,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow054_decode,functionalRow054_den]
  norm_num [functionalRow054_decode,functionalRow054_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow054_derivative : (functionalPolynomial (54:Fin 102)).derivative=functionalSlopePolynomial 54 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow054_decode,functionalRow054_slope_decode,functionalRow054_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow054_decode,functionalRow054_slope_decode,functionalRow054_den,integerPolynomial] <;> ring

theorem functionalRow055_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 55)=[-2,24,-114,260,-270,96,-374,1316,-1728,992,-224] := by decide +kernel
theorem functionalRow055_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 55)=[24,-228,780,-1080,480,-2244,9212,-13824,8928,-2240] := by decide +kernel
theorem functionalRow055_den : Factored.FunctionalData.denominator 55=1 := by decide +kernel
theorem functionalRow055_polynomial : familyPolynomial (invariantMonomial (fullTag (55:Fin 102)))=functionalPolynomial 55 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (55:Fin 102)=(1,0,3) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow055_decode,functionalRow055_den]
  norm_num [functionalRow055_decode,functionalRow055_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow055_derivative : (functionalPolynomial (55:Fin 102)).derivative=functionalSlopePolynomial 55 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow055_decode,functionalRow055_slope_decode,functionalRow055_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow055_decode,functionalRow055_slope_decode,functionalRow055_den,integerPolynomial] <;> ring

theorem functionalRow056_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 56)=[1,-22,198,-988,2982,-5512,6400,-6756,11241,-14882,8034] := by decide +kernel
theorem functionalRow056_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 56)=[-22,396,-2964,11928,-27560,38400,-47292,89928,-133938,80340] := by decide +kernel
theorem functionalRow056_den : Factored.FunctionalData.denominator 56=1 := by decide +kernel
theorem functionalRow056_polynomial : familyPolynomial (invariantMonomial (fullTag (56:Fin 102)))=functionalPolynomial 56 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (56:Fin 102)=(1,3,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow056_decode,functionalRow056_den]
  norm_num [functionalRow056_decode,functionalRow056_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow056_derivative : (functionalPolynomial (56:Fin 102)).derivative=functionalSlopePolynomial 56 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow056_decode,functionalRow056_slope_decode,functionalRow056_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow056_decode,functionalRow056_slope_decode,functionalRow056_den,integerPolynomial] <;> ring

theorem functionalRow057_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 57)=[-2,28,-150,384,-350,-500,1770,-2872,4224,-4720,2356] := by decide +kernel
theorem functionalRow057_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 57)=[28,-300,1152,-1400,-2500,10620,-20104,33792,-42480,23560] := by decide +kernel
theorem functionalRow057_den : Factored.FunctionalData.denominator 57=1 := by decide +kernel
theorem functionalRow057_polynomial : familyPolynomial (invariantMonomial (fullTag (57:Fin 102)))=functionalPolynomial 57 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (57:Fin 102)=(2,1,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow057_decode,functionalRow057_den]
  norm_num [functionalRow057_decode,functionalRow057_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow057_derivative : (functionalPolynomial (57:Fin 102)).derivative=functionalSlopePolynomial 57 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow057_decode,functionalRow057_slope_decode,functionalRow057_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow057_decode,functionalRow057_slope_decode,functionalRow057_den,integerPolynomial] <;> ring

theorem functionalRow058_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 58)=[3,-44,320,-1496,4818,-11888,29188,-75464,148555,-168196,80084] := by decide +kernel
theorem functionalRow058_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 58)=[-44,640,-4488,19272,-59440,175128,-528248,1188440,-1513764,800840] := by decide +kernel
theorem functionalRow058_den : Factored.FunctionalData.denominator 58=1 := by decide +kernel
theorem functionalRow058_polynomial : familyPolynomial (invariantMonomial (fullTag (58:Fin 102)))=functionalPolynomial 58 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (58:Fin 102)=(2,4,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow058_decode,functionalRow058_den]
  norm_num [functionalRow058_decode,functionalRow058_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow058_derivative : (functionalPolynomial (58:Fin 102)).derivative=functionalSlopePolynomial 58 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow058_decode,functionalRow058_slope_decode,functionalRow058_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow058_decode,functionalRow058_slope_decode,functionalRow058_den,integerPolynomial] <;> ring

theorem functionalRow059_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 59)=[-2,32,-230,860,-1710,1272,3874,-19700,44608,-52608,25500] := by decide +kernel
theorem functionalRow059_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 59)=[32,-460,2580,-6840,6360,23244,-137900,356864,-473472,255000] := by decide +kernel
theorem functionalRow059_den : Factored.FunctionalData.denominator 59=1 := by decide +kernel
theorem functionalRow059_polynomial : familyPolynomial (invariantMonomial (fullTag (59:Fin 102)))=functionalPolynomial 59 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (59:Fin 102)=(3,2,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow059_decode,functionalRow059_den]
  norm_num [functionalRow059_decode,functionalRow059_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow059_derivative : (functionalPolynomial (59:Fin 102)).derivative=functionalSlopePolynomial 59 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow059_decode,functionalRow059_slope_decode,functionalRow059_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow059_decode,functionalRow059_slope_decode,functionalRow059_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
