import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow040_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 40)=[280,-2304,14336,-64512,219520,-562688,1006208,-1091840,533536] := by decide +kernel
theorem functionalRow040_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 40)=[-2304,28672,-193536,878080,-2813440,6037248,-7642880,4268288] := by decide +kernel
theorem functionalRow040_den : Factored.FunctionalData.denominator 40=1 := by decide +kernel
theorem functionalRow040_polynomial : familyPolynomial (invariantMonomial (fullTag (40:Fin 102)))=functionalPolynomial 40 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (40:Fin 102)=(8,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow040_decode,functionalRow040_den]
  norm_num [functionalRow040_decode,functionalRow040_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow040_derivative : (functionalPolynomial (40:Fin 102)).derivative=functionalSlopePolynomial 40 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow040_decode,functionalRow040_slope_decode,functionalRow040_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow040_decode,functionalRow040_slope_decode,functionalRow040_den,integerPolynomial] <;> ring

theorem functionalRow041_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 41)=[2,-24,114,-260,246,120,-506,588,-504,280] := by decide +kernel
theorem functionalRow041_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 41)=[-24,228,-780,984,600,-3036,4116,-4032,2520] := by decide +kernel
theorem functionalRow041_den : Factored.FunctionalData.denominator 41=1 := by decide +kernel
theorem functionalRow041_polynomial : familyPolynomial (invariantMonomial (fullTag (41:Fin 102)))=functionalPolynomial 41 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (41:Fin 102)=(0,0,3) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow041_decode,functionalRow041_den]
  norm_num [functionalRow041_decode,functionalRow041_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow041_derivative : (functionalPolynomial (41:Fin 102)).derivative=functionalSlopePolynomial 41 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow041_decode,functionalRow041_slope_decode,functionalRow041_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow041_decode,functionalRow041_slope_decode,functionalRow041_den,integerPolynomial] <;> ring

theorem functionalRow042_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 42)=[-1,24,-220,1092,-3238,5844,-6364,4428,-2681,1284] := by decide +kernel
theorem functionalRow042_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 42)=[24,-440,3276,-12952,29220,-38184,30996,-21448,11556] := by decide +kernel
theorem functionalRow042_den : Factored.FunctionalData.denominator 42=1 := by decide +kernel
theorem functionalRow042_polynomial : familyPolynomial (invariantMonomial (fullTag (42:Fin 102)))=functionalPolynomial 42 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (42:Fin 102)=(0,3,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow042_decode,functionalRow042_den]
  norm_num [functionalRow042_decode,functionalRow042_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow042_derivative : (functionalPolynomial (42:Fin 102)).derivative=functionalSlopePolynomial 42 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow042_decode,functionalRow042_slope_decode,functionalRow042_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow042_decode,functionalRow042_slope_decode,functionalRow042_den,integerPolynomial] <;> ring

theorem functionalRow043_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 43)=[2,-28,154,-432,630,-420,14,472,-1000,728] := by decide +kernel
theorem functionalRow043_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 43)=[-28,308,-1296,2520,-2100,84,3304,-8000,6552] := by decide +kernel
theorem functionalRow043_den : Factored.FunctionalData.denominator 43=1 := by decide +kernel
theorem functionalRow043_polynomial : familyPolynomial (invariantMonomial (fullTag (43:Fin 102)))=functionalPolynomial 43 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (43:Fin 102)=(1,1,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow043_decode,functionalRow043_den]
  norm_num [functionalRow043_decode,functionalRow043_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow043_derivative : (functionalPolynomial (43:Fin 102)).derivative=functionalSlopePolynomial 43 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow043_decode,functionalRow043_slope_decode,functionalRow043_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow043_decode,functionalRow043_slope_decode,functionalRow043_den,integerPolynomial] <;> ring

theorem functionalRow044_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 44)=[-1,22,-228,1312,-4630,11180,-21572,35088,-39193,19918] := by decide +kernel
theorem functionalRow044_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 44)=[22,-456,3936,-18520,55900,-129432,245616,-313544,179262] := by decide +kernel
theorem functionalRow044_den : Factored.FunctionalData.denominator 44=1 := by decide +kernel
theorem functionalRow044_polynomial : familyPolynomial (invariantMonomial (fullTag (44:Fin 102)))=functionalPolynomial 44 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (44:Fin 102)=(1,4,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow044_decode,functionalRow044_den]
  norm_num [functionalRow044_decode,functionalRow044_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow044_derivative : (functionalPolynomial (44:Fin 102)).derivative=functionalSlopePolynomial 44 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow044_decode,functionalRow044_slope_decode,functionalRow044_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow044_decode,functionalRow044_slope_decode,functionalRow044_den,integerPolynomial] <;> ring

theorem functionalRow045_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 45)=[2,-28,170,-516,718,96,-2898,8140,-11440,6452] := by decide +kernel
theorem functionalRow045_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 45)=[-28,340,-1548,2872,480,-17388,56980,-91520,58068] := by decide +kernel
theorem functionalRow045_den : Factored.FunctionalData.denominator 45=1 := by decide +kernel
theorem functionalRow045_polynomial : familyPolynomial (invariantMonomial (fullTag (45:Fin 102)))=functionalPolynomial 45 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (45:Fin 102)=(2,2,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow045_decode,functionalRow045_den]
  norm_num [functionalRow045_decode,functionalRow045_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow045_derivative : (functionalPolynomial (45:Fin 102)).derivative=functionalSlopePolynomial 45 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow045_decode,functionalRow045_slope_decode,functionalRow045_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow045_decode,functionalRow045_slope_decode,functionalRow045_den,integerPolynomial] <;> ring

theorem functionalRow046_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 46)=[-4,32,-88,-8,548,-1760,3024,-2328,-336,1088] := by decide +kernel
theorem functionalRow046_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 46)=[32,-176,-24,2192,-8800,18144,-16296,-2688,9792] := by decide +kernel
theorem functionalRow046_den : Factored.FunctionalData.denominator 46=1 := by decide +kernel
theorem functionalRow046_polynomial : familyPolynomial (invariantMonomial (fullTag (46:Fin 102)))=functionalPolynomial 46 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (46:Fin 102)=(3,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow046_decode,functionalRow046_den]
  norm_num [functionalRow046_decode,functionalRow046_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow046_derivative : (functionalPolynomial (46:Fin 102)).derivative=functionalSlopePolynomial 46 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow046_decode,functionalRow046_slope_decode,functionalRow046_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow046_decode,functionalRow046_slope_decode,functionalRow046_den,integerPolynomial] <;> ring

theorem functionalRow047_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 47)=[2,-48,354,-1136,798,8388,-42138,100440,-124848,64068] := by decide +kernel
theorem functionalRow047_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 47)=[-48,708,-3408,3192,41940,-252828,703080,-998784,576612] := by decide +kernel
theorem functionalRow047_den : Factored.FunctionalData.denominator 47=1 := by decide +kernel
theorem functionalRow047_polynomial : familyPolynomial (invariantMonomial (fullTag (47:Fin 102)))=functionalPolynomial 47 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (47:Fin 102)=(3,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow047_decode,functionalRow047_den]
  norm_num [functionalRow047_decode,functionalRow047_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow047_derivative : (functionalPolynomial (47:Fin 102)).derivative=functionalSlopePolynomial 47 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow047_decode,functionalRow047_slope_decode,functionalRow047_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow047_decode,functionalRow047_slope_decode,functionalRow047_den,integerPolynomial] <;> ring

theorem functionalRow048_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 48)=[-4,56,-264,816,-2316,6224,-15712,31488,-38464,20072] := by decide +kernel
theorem functionalRow048_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 48)=[56,-528,2448,-9264,31120,-94272,220416,-307712,180648] := by decide +kernel
theorem functionalRow048_den : Factored.FunctionalData.denominator 48=1 := by decide +kernel
theorem functionalRow048_polynomial : familyPolynomial (invariantMonomial (fullTag (48:Fin 102)))=functionalPolynomial 48 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (48:Fin 102)=(4,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow048_decode,functionalRow048_den]
  norm_num [functionalRow048_decode,functionalRow048_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow048_derivative : (functionalPolynomial (48:Fin 102)).derivative=functionalSlopePolynomial 48 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow048_decode,functionalRow048_slope_decode,functionalRow048_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow048_decode,functionalRow048_slope_decode,functionalRow048_den,integerPolynomial] <;> ring

theorem functionalRow049_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 49)=[-4,-32,408,-864,-5676,48072,-175648,366560,-419968,204600] := by decide +kernel
theorem functionalRow049_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 49)=[-32,816,-2592,-22704,240360,-1053888,2565920,-3359744,1841400] := by decide +kernel
theorem functionalRow049_den : Factored.FunctionalData.denominator 49=1 := by decide +kernel
theorem functionalRow049_polynomial : familyPolynomial (invariantMonomial (fullTag (49:Fin 102)))=functionalPolynomial 49 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (49:Fin 102)=(5,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow049_decode,functionalRow049_den]
  norm_num [functionalRow049_decode,functionalRow049_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow049_derivative : (functionalPolynomial (49:Fin 102)).derivative=functionalSlopePolynomial 49 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow049_decode,functionalRow049_slope_decode,functionalRow049_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow049_decode,functionalRow049_slope_decode,functionalRow049_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
