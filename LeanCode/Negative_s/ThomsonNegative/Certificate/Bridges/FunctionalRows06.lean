import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow060_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 60)=[4,-32,104,-208,924,-3984,11176,-21600,29408,-25600,10504] := by decide +kernel
theorem functionalRow060_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 60)=[-32,208,-624,3696,-19920,67056,-151200,235264,-230400,105040] := by decide +kernel
theorem functionalRow060_den : Factored.FunctionalData.denominator 60=1 := by decide +kernel
theorem functionalRow060_polynomial : familyPolynomial (invariantMonomial (fullTag (60:Fin 102)))=functionalPolynomial 60 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (60:Fin 102)=(4,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow060_decode,functionalRow060_den]
  norm_num [functionalRow060_decode,functionalRow060_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow060_derivative : (functionalPolynomial (60:Fin 102)).derivative=functionalSlopePolynomial 60 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow060_decode,functionalRow060_slope_decode,functionalRow060_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow060_decode,functionalRow060_slope_decode,functionalRow060_den,integerPolynomial] <;> ring

theorem functionalRow061_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 61)=[6,-44,78,104,658,-13644,81458,-269920,526056,-563216,255912] := by decide +kernel
theorem functionalRow061_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 61)=[-44,156,312,2632,-68220,488748,-1889440,4208448,-5068944,2559120] := by decide +kernel
theorem functionalRow061_den : Factored.FunctionalData.denominator 61=1 := by decide +kernel
theorem functionalRow061_polynomial : familyPolynomial (invariantMonomial (fullTag (61:Fin 102)))=functionalPolynomial 61 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (61:Fin 102)=(4,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow061_decode,functionalRow061_den]
  norm_num [functionalRow061_decode,functionalRow061_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow061_derivative : (functionalPolynomial (61:Fin 102)).derivative=functionalSlopePolynomial 61 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow061_decode,functionalRow061_slope_decode,functionalRow061_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow061_decode,functionalRow061_slope_decode,functionalRow061_den,integerPolynomial] <;> ring

theorem functionalRow062_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 62)=[4,-40,-8,960,-3876,5672,10072,-69344,157344,-177792,82888] := by decide +kernel
theorem functionalRow062_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 62)=[-40,-16,2880,-15504,28360,60432,-485408,1258752,-1600128,828880] := by decide +kernel
theorem functionalRow062_den : Factored.FunctionalData.denominator 62=1 := by decide +kernel
theorem functionalRow062_polynomial : familyPolynomial (invariantMonomial (fullTag (62:Fin 102)))=functionalPolynomial 62 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (62:Fin 102)=(5,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow062_decode,functionalRow062_den]
  norm_num [functionalRow062_decode,functionalRow062_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow062_derivative : (functionalPolynomial (62:Fin 102)).derivative=functionalSlopePolynomial 62 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow062_decode,functionalRow062_slope_decode,functionalRow062_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow062_decode,functionalRow062_slope_decode,functionalRow062_den,integerPolynomial] <;> ring

theorem functionalRow063_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 63)=[36,-368,1784,-6000,21060,-94224,380048,-1064832,1879416,-1884016,819632] := by decide +kernel
theorem functionalRow063_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 63)=[-368,3568,-18000,84240,-471120,2280288,-7453824,15035328,-16956144,8196320] := by decide +kernel
theorem functionalRow063_den : Factored.FunctionalData.denominator 63=1 := by decide +kernel
theorem functionalRow063_polynomial : familyPolynomial (invariantMonomial (fullTag (63:Fin 102)))=functionalPolynomial 63 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (63:Fin 102)=(6,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow063_decode,functionalRow063_den]
  norm_num [functionalRow063_decode,functionalRow063_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow063_derivative : (functionalPolynomial (63:Fin 102)).derivative=functionalSlopePolynomial 63 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow063_decode,functionalRow063_slope_decode,functionalRow063_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow063_decode,functionalRow063_slope_decode,functionalRow063_den,integerPolynomial] <;> ring

theorem functionalRow064_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 64)=[-8,32,-720,5376,-21280,44352,-17136,-162624,453376,-534912,250992] := by decide +kernel
theorem functionalRow064_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 64)=[32,-1440,16128,-85120,221760,-102816,-1138368,3627008,-4814208,2509920] := by decide +kernel
theorem functionalRow064_den : Factored.FunctionalData.denominator 64=1 := by decide +kernel
theorem functionalRow064_polynomial : familyPolynomial (invariantMonomial (fullTag (64:Fin 102)))=functionalPolynomial 64 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (64:Fin 102)=(7,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow064_decode,functionalRow064_den]
  norm_num [functionalRow064_decode,functionalRow064_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow064_derivative : (functionalPolynomial (64:Fin 102)).derivative=functionalSlopePolynomial 64 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow064_decode,functionalRow064_slope_decode,functionalRow064_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow064_decode,functionalRow064_slope_decode,functionalRow064_den,integerPolynomial] <;> ring

theorem functionalRow065_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 65)=[120,-1248,7792,-36096,143808,-540288,1744512,-4187136,6688192,-6279040,2616800] := by decide +kernel
theorem functionalRow065_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 65)=[-1248,15584,-108288,575232,-2701440,10467072,-29309952,53505536,-56511360,26168000] := by decide +kernel
theorem functionalRow065_den : Factored.FunctionalData.denominator 65=1 := by decide +kernel
theorem functionalRow065_polynomial : familyPolynomial (invariantMonomial (fullTag (65:Fin 102)))=functionalPolynomial 65 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (65:Fin 102)=(8,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow065_decode,functionalRow065_den]
  norm_num [functionalRow065_decode,functionalRow065_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow065_derivative : (functionalPolynomial (65:Fin 102)).derivative=functionalSlopePolynomial 65 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow065_decode,functionalRow065_slope_decode,functionalRow065_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow065_decode,functionalRow065_slope_decode,functionalRow065_den,integerPolynomial] <;> ring

theorem functionalRow066_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 66)=[536,-5440,40320,-215040,887040,-2999808,8211840,-17026560,24423840,-21286720,8442432] := by decide +kernel
theorem functionalRow066_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 66)=[-5440,80640,-645120,3548160,-14999040,49271040,-119185920,195390720,-191580480,84424320] := by decide +kernel
theorem functionalRow066_den : Factored.FunctionalData.denominator 66=1 := by decide +kernel
theorem functionalRow066_polynomial : familyPolynomial (invariantMonomial (fullTag (66:Fin 102)))=functionalPolynomial 66 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (66:Fin 102)=(10,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow066_decode,functionalRow066_den]
  norm_num [functionalRow066_decode,functionalRow066_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow066_derivative : (functionalPolynomial (66:Fin 102)).derivative=functionalSlopePolynomial 66 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow066_decode,functionalRow066_slope_decode,functionalRow066_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow066_decode,functionalRow066_slope_decode,functionalRow066_den,integerPolynomial] <;> ring

theorem functionalRow067_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 67)=[-1,18,-136,558,-1318,1704,-868,-288,7,918,-780,162] := by decide +kernel
theorem functionalRow067_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 67)=[18,-272,1674,-5272,8520,-5208,-2016,56,8262,-7800,1782] := by decide +kernel
theorem functionalRow067_den : Factored.FunctionalData.denominator 67=1 := by decide +kernel
theorem functionalRow067_polynomial : familyPolynomial (invariantMonomial (fullTag (67:Fin 102)))=functionalPolynomial 67 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (67:Fin 102)=(0,1,3) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow067_decode,functionalRow067_den]
  norm_num [functionalRow067_decode,functionalRow067_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow067_derivative : (functionalPolynomial (67:Fin 102)).derivative=functionalSlopePolynomial 67 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow067_decode,functionalRow067_slope_decode,functionalRow067_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow067_decode,functionalRow067_slope_decode,functionalRow067_den,integerPolynomial] <;> ring

theorem functionalRow068_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 68)=[1,-28,343,-2426,10866,-31984,61782,-73292,37869,24668,-51293,24886] := by decide +kernel
theorem functionalRow068_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 68)=[-28,686,-7278,43464,-159920,370692,-513044,302952,222012,-512930,273746] := by decide +kernel
theorem functionalRow068_den : Factored.FunctionalData.denominator 68=2 := by decide +kernel
theorem functionalRow068_polynomial : familyPolynomial (invariantMonomial (fullTag (68:Fin 102)))=functionalPolynomial 68 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (68:Fin 102)=(0,4,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow068_decode,functionalRow068_den]
  norm_num [functionalRow068_decode,functionalRow068_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow068_derivative : (functionalPolynomial (68:Fin 102)).derivative=functionalSlopePolynomial 68 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow068_decode,functionalRow068_slope_decode,functionalRow068_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow068_decode,functionalRow068_slope_decode,functionalRow068_den,integerPolynomial] <;> ring

theorem functionalRow069_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 69)=[-1,20,-168,758,-1974,2872,-1788,-244,-889,5284,-6852,3150] := by decide +kernel
theorem functionalRow069_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 69)=[20,-336,2274,-7896,14360,-10728,-1708,-7112,47556,-68520,34650] := by decide +kernel
theorem functionalRow069_den : Factored.FunctionalData.denominator 69=1 := by decide +kernel
theorem functionalRow069_polynomial : familyPolynomial (invariantMonomial (fullTag (69:Fin 102)))=functionalPolynomial 69 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (69:Fin 102)=(1,2,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow069_decode,functionalRow069_den]
  norm_num [functionalRow069_decode,functionalRow069_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow069_derivative : (functionalPolynomial (69:Fin 102)).derivative=functionalSlopePolynomial 69 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow069_decode,functionalRow069_slope_decode,functionalRow069_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow069_decode,functionalRow069_slope_decode,functionalRow069_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
