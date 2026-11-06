import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow100_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 100)=[248,-3040,22768,-121920,516480,-2015232,7651392,-25596288,66911760,-126168640,159834496,-121531008,41916112] := by decide +kernel
theorem functionalRow100_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 100)=[-3040,45536,-365760,2065920,-10076160,45908352,-179174016,535294080,-1135517760,1598344960,-1336841088,502993344] := by decide +kernel
theorem functionalRow100_den : Factored.FunctionalData.denominator 100=1 := by decide +kernel
theorem functionalRow100_polynomial : familyPolynomial (invariantMonomial (fullTag (100:Fin 102)))=functionalPolynomial 100 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (100:Fin 102)=(10,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow100_decode,functionalRow100_den]
  norm_num [functionalRow100_decode,functionalRow100_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow100_derivative : (functionalPolynomial (100:Fin 102)).derivative=functionalSlopePolynomial 100 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow100_decode,functionalRow100_slope_decode,functionalRow100_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow100_decode,functionalRow100_slope_decode,functionalRow100_den,integerPolynomial] <;> ring

theorem functionalRow101_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 101)=[1048,-12672,109824,-675840,3168000,-12367872,41986560,-120941568,277801920,-475242240,560750784,-404857728,134531360] := by decide +kernel
theorem functionalRow101_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 101)=[-12672,219648,-2027520,12672000,-61839360,251919360,-846590976,2222415360,-4277180160,5607507840,-4453435008,1614376320] := by decide +kernel
theorem functionalRow101_den : Factored.FunctionalData.denominator 101=1 := by decide +kernel
theorem functionalRow101_polynomial : familyPolynomial (invariantMonomial (fullTag (101:Fin 102)))=functionalPolynomial 101 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (101:Fin 102)=(12,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow101_decode,functionalRow101_den]
  norm_num [functionalRow101_decode,functionalRow101_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow101_derivative : (functionalPolynomial (101:Fin 102)).derivative=functionalSlopePolynomial 101 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow101_decode,functionalRow101_slope_decode,functionalRow101_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow101_decode,functionalRow101_slope_decode,functionalRow101_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
