import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow070_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 70)=[1,-30,395,-2980,14370,-45764,92142,-87840,-74275,349490,-433993,200244] := by decide +kernel
theorem functionalRow070_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 70)=[-30,790,-8940,57480,-228820,552852,-614880,-594200,3145410,-4339930,2202684] := by decide +kernel
theorem functionalRow070_den : Factored.FunctionalData.denominator 70=2 := by decide +kernel
theorem functionalRow070_polynomial : familyPolynomial (invariantMonomial (fullTag (70:Fin 102)))=functionalPolynomial 70 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (70:Fin 102)=(1,5,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow070_decode,functionalRow070_den]
  norm_num [functionalRow070_decode,functionalRow070_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow070_derivative : (functionalPolynomial (70:Fin 102)).derivative=functionalSlopePolynomial 70 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow070_decode,functionalRow070_slope_decode,functionalRow070_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow070_decode,functionalRow070_slope_decode,functionalRow070_den,integerPolynomial] <;> ring

theorem functionalRow071_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 71)=[2,-24,114,-256,214,328,-1450,3556,-6648,8360,-6256,2180] := by decide +kernel
theorem functionalRow071_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 71)=[-24,228,-768,856,1640,-8700,24892,-53184,75240,-62560,23980] := by decide +kernel
theorem functionalRow071_den : Factored.FunctionalData.denominator 71=1 := by decide +kernel
theorem functionalRow071_polynomial : familyPolynomial (invariantMonomial (fullTag (71:Fin 102)))=functionalPolynomial 71 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (71:Fin 102)=(2,0,3) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow071_decode,functionalRow071_den]
  norm_num [functionalRow071_decode,functionalRow071_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow071_derivative : (functionalPolynomial (71:Fin 102)).derivative=functionalSlopePolynomial 71 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow071_decode,functionalRow071_slope_decode,functionalRow071_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow071_decode,functionalRow071_slope_decode,functionalRow071_den,integerPolynomial] <;> ring

theorem functionalRow072_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 72)=[-1,24,-224,1128,-3382,6132,-7092,10228,-29577,63172,-70468,31956] := by decide +kernel
theorem functionalRow072_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 72)=[24,-448,3384,-13528,30660,-42552,71596,-236616,568548,-704680,351516] := by decide +kernel
theorem functionalRow072_den : Factored.FunctionalData.denominator 72=1 := by decide +kernel
theorem functionalRow072_polynomial : familyPolynomial (invariantMonomial (fullTag (72:Fin 102)))=functionalPolynomial 72 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (72:Fin 102)=(2,3,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow072_decode,functionalRow072_den]
  norm_num [functionalRow072_decode,functionalRow072_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow072_derivative : (functionalPolynomial (72:Fin 102)).derivative=functionalSlopePolynomial 72 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow072_decode,functionalRow072_slope_decode,functionalRow072_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow072_decode,functionalRow072_slope_decode,functionalRow072_den,integerPolynomial] <;> ring

theorem functionalRow073_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 73)=[2,-28,154,-460,886,-1556,2942,-2896,-4360,17960,-22672,10724] := by decide +kernel
theorem functionalRow073_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 73)=[-28,308,-1380,3544,-7780,17652,-20272,-34880,161640,-226720,117964] := by decide +kernel
theorem functionalRow073_den : Factored.FunctionalData.denominator 73=1 := by decide +kernel
theorem functionalRow073_polynomial : familyPolynomial (invariantMonomial (fullTag (73:Fin 102)))=functionalPolynomial 73 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (73:Fin 102)=(3,1,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow073_decode,functionalRow073_den]
  norm_num [functionalRow073_decode,functionalRow073_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow073_derivative : (functionalPolynomial (73:Fin 102)).derivative=functionalSlopePolynomial 73 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow073_decode,functionalRow073_slope_decode,functionalRow073_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow073_decode,functionalRow073_slope_decode,functionalRow073_den,integerPolynomial] <;> ring

theorem functionalRow074_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 74)=[-1,18,-184,1144,-4390,12276,-38460,143408,-415273,750826,-751828,319912] := by decide +kernel
theorem functionalRow074_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 74)=[18,-368,3432,-17560,61380,-230760,1003856,-3322184,6757434,-7518280,3519032] := by decide +kernel
theorem functionalRow074_den : Factored.FunctionalData.denominator 74=1 := by decide +kernel
theorem functionalRow074_polynomial : familyPolynomial (invariantMonomial (fullTag (74:Fin 102)))=functionalPolynomial 74 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (74:Fin 102)=(3,4,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow074_decode,functionalRow074_den]
  norm_num [functionalRow074_decode,functionalRow074_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow074_derivative : (functionalPolynomial (74:Fin 102)).derivative=functionalSlopePolynomial 74 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow074_decode,functionalRow074_slope_decode,functionalRow074_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow074_decode,functionalRow074_slope_decode,functionalRow074_den,integerPolynomial] <;> ring

theorem functionalRow075_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 75)=[2,-24,122,-204,-546,3432,-11442,40860,-121120,227528,-235344,102616] := by decide +kernel
theorem functionalRow075_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 75)=[-24,244,-612,-2184,17160,-68652,286020,-968960,2047752,-2353440,1128776] := by decide +kernel
theorem functionalRow075_den : Factored.FunctionalData.denominator 75=1 := by decide +kernel
theorem functionalRow075_polynomial : familyPolynomial (invariantMonomial (fullTag (75:Fin 102)))=functionalPolynomial 75 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (75:Fin 102)=(4,2,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow075_decode,functionalRow075_den]
  norm_num [functionalRow075_decode,functionalRow075_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow075_derivative : (functionalPolynomial (75:Fin 102)).derivative=functionalSlopePolynomial 75 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow075_decode,functionalRow075_slope_decode,functionalRow075_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow075_decode,functionalRow075_slope_decode,functionalRow075_den,integerPolynomial] <;> ring

theorem functionalRow076_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 76)=[-4,32,-88,-128,1684,-7616,21296,-35448,25440,17728,-48192,27192] := by decide +kernel
theorem functionalRow076_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 76)=[32,-176,-384,6736,-38080,127776,-248136,203520,159552,-481920,299112] := by decide +kernel
theorem functionalRow076_den : Factored.FunctionalData.denominator 76=1 := by decide +kernel
theorem functionalRow076_polynomial : familyPolynomial (invariantMonomial (fullTag (76:Fin 102)))=functionalPolynomial 76 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (76:Fin 102)=(5,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow076_decode,functionalRow076_den]
  norm_num [functionalRow076_decode,functionalRow076_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow076_derivative : (functionalPolynomial (76:Fin 102)).derivative=functionalSlopePolynomial 76 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow076_decode,functionalRow076_slope_decode,functionalRow076_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow076_decode,functionalRow076_slope_decode,functionalRow076_den,integerPolynomial] <;> ring

theorem functionalRow077_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 77)=[2,-76,658,-2472,3246,16236,-141754,602984,-1608992,2667224,-2508656,1024136] := by decide +kernel
theorem functionalRow077_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 77)=[-76,1316,-7416,12984,81180,-850524,4220888,-12871936,24005016,-25086560,11265496] := by decide +kernel
theorem functionalRow077_den : Factored.FunctionalData.denominator 77=1 := by decide +kernel
theorem functionalRow077_polynomial : familyPolynomial (invariantMonomial (fullTag (77:Fin 102)))=functionalPolynomial 77 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (77:Fin 102)=(5,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow077_decode,functionalRow077_den]
  norm_num [functionalRow077_decode,functionalRow077_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow077_derivative : (functionalPolynomial (77:Fin 102)).derivative=functionalSlopePolynomial 77 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow077_decode,functionalRow077_slope_decode,functionalRow077_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow077_decode,functionalRow077_slope_decode,functionalRow077_den,integerPolynomial] <;> ring

theorem functionalRow078_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 78)=[-4,72,-456,2256,-9324,29648,-81872,219024,-504704,818488,-781040,325360] := by decide +kernel
theorem functionalRow078_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 78)=[72,-912,6768,-37296,148240,-491232,1533168,-4037632,7366392,-7810400,3578960] := by decide +kernel
theorem functionalRow078_den : Factored.FunctionalData.denominator 78=1 := by decide +kernel
theorem functionalRow078_polynomial : familyPolynomial (invariantMonomial (fullTag (78:Fin 102)))=functionalPolynomial 78 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (78:Fin 102)=(6,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow078_decode,functionalRow078_den]
  norm_num [functionalRow078_decode,functionalRow078_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow078_derivative : (functionalPolynomial (78:Fin 102)).derivative=functionalSlopePolynomial 78 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow078_decode,functionalRow078_slope_decode,functionalRow078_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow078_decode,functionalRow078_slope_decode,functionalRow078_den,integerPolynomial] <;> ring

theorem functionalRow079_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 79)=[-4,-176,2008,-8352,8564,94584,-681744,2562272,-6159296,9419448,-8355696,3275808] := by decide +kernel
theorem functionalRow079_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 79)=[-176,4016,-25056,34256,472920,-4090464,17935904,-49274368,84775032,-83556960,36033888] := by decide +kernel
theorem functionalRow079_den : Factored.FunctionalData.denominator 79=1 := by decide +kernel
theorem functionalRow079_polynomial : familyPolynomial (invariantMonomial (fullTag (79:Fin 102)))=functionalPolynomial 79 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (79:Fin 102)=(7,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow079_decode,functionalRow079_den]
  norm_num [functionalRow079_decode,functionalRow079_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow079_derivative : (functionalPolynomial (79:Fin 102)).derivative=functionalSlopePolynomial 79 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow079_decode,functionalRow079_slope_decode,functionalRow079_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow079_decode,functionalRow079_slope_decode,functionalRow079_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
