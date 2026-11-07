import AllS.Units.N_F.N_kernels

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def rawStandardPairing (P Q : Fin 3 → Poly3) : Poly3 :=
  P 0*Q 0+MvPolynomial.C (1/3 : ℝ)*(P 1-P 2)*(Q 1-Q 2)

theorem raw_delta_square :
    deltaPoly^2=sigma^2*e2^2-4*e2^3-4*sigma^3*e3-27*e3^2+18*sigma*e2*e3 := by
  simp only [deltaPoly,sigma,e2,e3]
  ring

theorem raw_standard_PP :
    rawStandardPairing standardPPoly standardPPoly=
      MvPolynomial.C (4/9 : ℝ)*sigma^2-MvPolynomial.C (4/3 : ℝ)*e2 := by
  apply MvPolynomial.funext
  intro x
  norm_num [rawStandardPairing,standardPPoly,sigma,e2]
  ring

theorem raw_standard_PQ :
    rawStandardPairing standardPPoly standardQPoly=
      MvPolynomial.C (4/27 : ℝ)*sigma^3-MvPolynomial.C (2/3 : ℝ)*sigma*e2+2*e3 := by
  apply MvPolynomial.funext
  intro x
  norm_num [rawStandardPairing,standardPPoly,standardQPoly,sigma,e2,e3,Fin.sum_univ_succ]
  ring

theorem raw_standard_QQ :
    rawStandardPairing standardQPoly standardQPoly=
      MvPolynomial.C (4/81 : ℝ)*sigma^4-MvPolynomial.C (8/27 : ℝ)*sigma^2*e2+
        MvPolynomial.C (4/9 : ℝ)*e2^2 := by
  apply MvPolynomial.funext
  intro x
  norm_num [rawStandardPairing,standardPPoly,standardQPoly,sigma,e2,e3,Fin.sum_univ_succ]
  ring

def RawSignStandardContract : Prop :=
  (deltaPoly^2=sigma^2*e2^2-4*e2^3-4*sigma^3*e3-27*e3^2+18*sigma*e2*e3) ∧
  (rawStandardPairing standardPPoly standardPPoly=
      MvPolynomial.C (4/9 : ℝ)*sigma^2-MvPolynomial.C (4/3 : ℝ)*e2) ∧
  (rawStandardPairing standardPPoly standardQPoly=
      MvPolynomial.C (4/27 : ℝ)*sigma^3-MvPolynomial.C (2/3 : ℝ)*sigma*e2+2*e3) ∧
  (rawStandardPairing standardQPoly standardQPoly=
      MvPolynomial.C (4/81 : ℝ)*sigma^4-MvPolynomial.C (8/27 : ℝ)*sigma^2*e2+
        MvPolynomial.C (4/9 : ℝ)*e2^2)

theorem raw_projection_sign_standard : RawSignStandardContract :=
  ⟨raw_delta_square,raw_standard_PP,raw_standard_PQ,raw_standard_QQ⟩

#print axioms raw_projection_sign_standard
end Blueprint.Thomson.Finite
