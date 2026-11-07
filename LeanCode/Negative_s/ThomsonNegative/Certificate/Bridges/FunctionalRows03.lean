import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow030_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 30)=[-24,-672,2688,2240,-44800,144480,-213696,127232] := by decide +kernel
theorem functionalRow030_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 30)=[-672,5376,6720,-179200,722400,-1282176,890624] := by decide +kernel
theorem functionalRow030_den : Factored.FunctionalData.denominator 30=1 := by decide +kernel
theorem functionalRow030_polynomial : familyPolynomial (invariantMonomial (fullTag (30:Fin 102)))=functionalPolynomial 30 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (30:Fin 102)=(7,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow030_decode,functionalRow030_den]
  norm_num [functionalRow030_decode,functionalRow030_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow030_derivative : (functionalPolynomial (30:Fin 102)).derivative=functionalSlopePolynomial 30 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow030_decode,functionalRow030_slope_decode,functionalRow030_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow030_decode,functionalRow030_slope_decode,functionalRow030_den,integerPolynomial] <;> ring

theorem functionalRow031_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 31)=[-2,28,-154,416,-510,60,450,-376,64] := by decide +kernel
theorem functionalRow031_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 31)=[28,-308,1248,-2040,300,2700,-2632,512] := by decide +kernel
theorem functionalRow031_den : Factored.FunctionalData.denominator 31=1 := by decide +kernel
theorem functionalRow031_polynomial : familyPolynomial (invariantMonomial (fullTag (31:Fin 102)))=functionalPolynomial 31 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (31:Fin 102)=(0,1,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow031_decode,functionalRow031_den]
  norm_num [functionalRow031_decode,functionalRow031_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow031_derivative : (functionalPolynomial (31:Fin 102)).derivative=functionalSlopePolynomial 31 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow031_decode,functionalRow031_slope_decode,functionalRow031_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow031_decode,functionalRow031_slope_decode,functionalRow031_den,integerPolynomial] <;> ring

theorem functionalRow032_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 32)=[3,-40,300,-1480,4930,-11160,17100,-16440,7483] := by decide +kernel
theorem functionalRow032_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 32)=[-40,600,-4440,19720,-55800,102600,-115080,59864] := by decide +kernel
theorem functionalRow032_den : Factored.FunctionalData.denominator 32=1 := by decide +kernel
theorem functionalRow032_polynomial : familyPolynomial (invariantMonomial (fullTag (32:Fin 102)))=functionalPolynomial 32 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (32:Fin 102)=(0,4,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow032_decode,functionalRow032_den]
  norm_num [functionalRow032_decode,functionalRow032_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow032_derivative : (functionalPolynomial (32:Fin 102)).derivative=functionalSlopePolynomial 32 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow032_decode,functionalRow032_slope_decode,functionalRow032_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow032_decode,functionalRow032_slope_decode,functionalRow032_den,integerPolynomial] <;> ring

theorem functionalRow033_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 33)=[-2,32,-210,684,-1070,344,1546,-2724,1568] := by decide +kernel
theorem functionalRow033_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 33)=[32,-420,2052,-4280,1720,9276,-19068,12544] := by decide +kernel
theorem functionalRow033_den : Factored.FunctionalData.denominator 33=1 := by decide +kernel
theorem functionalRow033_polynomial : familyPolynomial (invariantMonomial (fullTag (33:Fin 102)))=functionalPolynomial 33 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (33:Fin 102)=(1,2,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow033_decode,functionalRow033_den]
  norm_num [functionalRow033_decode,functionalRow033_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow033_derivative : (functionalPolynomial (33:Fin 102)).derivative=functionalSlopePolynomial 33 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow033_decode,functionalRow033_slope_decode,functionalRow033_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow033_decode,functionalRow033_slope_decode,functionalRow033_den,integerPolynomial] <;> ring

theorem functionalRow034_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 34)=[4,-32,96,-128,268,-880,1752,-1872,912] := by decide +kernel
theorem functionalRow034_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 34)=[-32,192,-384,1072,-4400,10512,-13104,7296] := by decide +kernel
theorem functionalRow034_den : Factored.FunctionalData.denominator 34=1 := by decide +kernel
theorem functionalRow034_polynomial : familyPolynomial (invariantMonomial (fullTag (34:Fin 102)))=functionalPolynomial 34 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (34:Fin 102)=(2,0,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow034_decode,functionalRow034_den]
  norm_num [functionalRow034_decode,functionalRow034_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow034_derivative : (functionalPolynomial (34:Fin 102)).derivative=functionalSlopePolynomial 34 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow034_decode,functionalRow034_slope_decode,functionalRow034_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow034_decode,functionalRow034_slope_decode,functionalRow034_den,integerPolynomial] <;> ring

theorem functionalRow035_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 35)=[2,4,-170,792,-870,-4140,17458,-27120,15940] := by decide +kernel
theorem functionalRow035_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 35)=[4,-340,2376,-3480,-20700,104748,-189840,127520] := by decide +kernel
theorem functionalRow035_den : Factored.FunctionalData.denominator 35=1 := by decide +kernel
theorem functionalRow035_polynomial : familyPolynomial (invariantMonomial (fullTag (35:Fin 102)))=functionalPolynomial 35 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (35:Fin 102)=(2,3,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow035_decode,functionalRow035_den]
  norm_num [functionalRow035_decode,functionalRow035_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow035_derivative : (functionalPolynomial (35:Fin 102)).derivative=functionalSlopePolynomial 35 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow035_decode,functionalRow035_slope_decode,functionalRow035_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow035_decode,functionalRow035_slope_decode,functionalRow035_den,integerPolynomial] <;> ring

theorem functionalRow036_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 36)=[4,-40,80,144,-532,-568,4840,-8528,5296] := by decide +kernel
theorem functionalRow036_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 36)=[-40,160,432,-2128,-2840,29040,-59696,42368] := by decide +kernel
theorem functionalRow036_den : Factored.FunctionalData.denominator 36=1 := by decide +kernel
theorem functionalRow036_polynomial : familyPolynomial (invariantMonomial (fullTag (36:Fin 102)))=functionalPolynomial 36 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (36:Fin 102)=(3,1,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow036_decode,functionalRow036_den]
  norm_num [functionalRow036_decode,functionalRow036_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow036_derivative : (functionalPolynomial (36:Fin 102)).derivative=functionalSlopePolynomial 36 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow036_decode,functionalRow036_slope_decode,functionalRow036_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow036_decode,functionalRow036_slope_decode,functionalRow036_den,integerPolynomial] <;> ring

theorem functionalRow037_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 37)=[20,-176,664,-1808,6788,-26848,68032,-92096,51304] := by decide +kernel
theorem functionalRow037_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 37)=[-176,1328,-5424,27152,-134240,408192,-644672,410432] := by decide +kernel
theorem functionalRow037_den : Factored.FunctionalData.denominator 37=1 := by decide +kernel
theorem functionalRow037_polynomial : familyPolynomial (invariantMonomial (fullTag (37:Fin 102)))=functionalPolynomial 37 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (37:Fin 102)=(4,2,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow037_decode,functionalRow037_den]
  norm_num [functionalRow037_decode,functionalRow037_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow037_derivative : (functionalPolynomial (37:Fin 102)).derivative=functionalSlopePolynomial 37 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow037_decode,functionalRow037_slope_decode,functionalRow037_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow037_decode,functionalRow037_slope_decode,functionalRow037_den,integerPolynomial] <;> ring

theorem functionalRow038_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 38)=[-8,32,-304,1536,-3840,2560,8960,-21504,14464] := by decide +kernel
theorem functionalRow038_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 38)=[32,-608,4608,-15360,12800,53760,-150528,115712] := by decide +kernel
theorem functionalRow038_den : Factored.FunctionalData.denominator 38=1 := by decide +kernel
theorem functionalRow038_polynomial : familyPolynomial (invariantMonomial (fullTag (38:Fin 102)))=functionalPolynomial 38 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (38:Fin 102)=(5,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow038_decode,functionalRow038_den]
  norm_num [functionalRow038_decode,functionalRow038_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow038_derivative : (functionalPolynomial (38:Fin 102)).derivative=functionalSlopePolynomial 38 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow038_decode,functionalRow038_slope_decode,functionalRow038_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow038_decode,functionalRow038_slope_decode,functionalRow038_den,integerPolynomial] <;> ring

theorem functionalRow039_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 39)=[56,-480,2512,-10496,39120,-120384,254176,-310080,163024] := by decide +kernel
theorem functionalRow039_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 39)=[-480,5024,-31488,156480,-601920,1525056,-2170560,1304192] := by decide +kernel
theorem functionalRow039_den : Factored.FunctionalData.denominator 39=1 := by decide +kernel
theorem functionalRow039_polynomial : familyPolynomial (invariantMonomial (fullTag (39:Fin 102)))=functionalPolynomial 39 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (39:Fin 102)=(6,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow039_decode,functionalRow039_den]
  norm_num [functionalRow039_decode,functionalRow039_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow039_derivative : (functionalPolynomial (39:Fin 102)).derivative=functionalSlopePolynomial 39 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow039_decode,functionalRow039_slope_decode,functionalRow039_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow039_decode,functionalRow039_slope_decode,functionalRow039_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
