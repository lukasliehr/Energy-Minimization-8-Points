import ThomsonNegative.Structure.Kernels
import ThomsonNegative.Structure.Rational

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure

structure CanonicalBasis where
  moment : (k : Fin 6) → Matrix (Fin (7-k.val)) (Fin (6-k.val)) ℝ
  plus : Matrix (Fin 16) (Fin 11) ℝ
  standard : Matrix (Fin 18) (Fin 11) ℝ

structure RFBasis where
  moment : (k : Fin 6) → RFMatrix (7-k.val) (6-k.val)
  plus : RFMatrix 16 11
  standard : RFMatrix 18 11

def RFBasis.eval (B : RFBasis) (a : ℝ) : CanonicalBasis where
  moment := fun k => (B.moment k).eval a
  plus := B.plus.eval a
  standard := B.standard.eval a

def plusTag : Fin 16 → Tag := ![(0,0,0), (1,0,0), (0,1,0), (2,0,0), (0,0,1), (1,1,0), (3,0,0), (0,2,0), (1,0,1), (2,1,0), (4,0,0), (0,1,1), (1,2,0), (2,0,1), (3,1,0), (5,0,0)]

def standardTag : Fin 18 → Bool × Tag := ![(false,(0,0,0)), (false,(1,0,0)), (false,(0,1,0)), (false,(2,0,0)), (false,(0,0,1)), (false,(1,1,0)), (false,(3,0,0)), (false,(0,2,0)), (false,(1,0,1)), (false,(2,1,0)), (false,(4,0,0)), (true,(0,0,0)), (true,(1,0,0)), (true,(0,1,0)), (true,(2,0,0)), (true,(0,0,1)), (true,(1,1,0)), (true,(3,0,0))]

def covariantP (i : Fin 3) : Poly3 := MvPolynomial.X i - MvPolynomial.C (1/3 : ℝ) * sigma

def covariantQ (i : Fin 3) : Poly3 := covariantP i ^ 2 -
  MvPolynomial.C (1/3 : ℝ) * ∑ r : Fin 3, covariantP r ^ 2

def standardRawA (r : Fin 18) : Poly3 :=
  (if (standardTag r).1 then covariantQ 0 else covariantP 0) *
    invariantMonomial (standardTag r).2

def standardRawB (r : Fin 18) : Poly3 :=
  (if (standardTag r).1 then covariantQ 1-covariantQ 2 else covariantP 1-covariantP 2) *
    invariantMonomial (standardTag r).2

def plusFeature (B : Matrix (Fin 16) (Fin 11) ℝ) (i : Fin 11) : Poly3 :=
  ∑ r, MvPolynomial.C (B r i) * invariantMonomial (plusTag r)

def standardFeature (B : Matrix (Fin 18) (Fin 11) ℝ) (c : Fin 2) (i : Fin 11) : Poly3 :=
  ∑ r, MvPolynomial.C (B r i) * (if c=0 then standardRawA r else standardRawB r)

def plusPolynomial (B : Matrix (Fin 16) (Fin 11) ℝ) :
    Matrix (Fin 11) (Fin 11) Poly3 :=
  squarePolynomial (fun _ : Fin 6 => (1/6 : ℝ))
    (fun r i => MvPolynomial.rename (coordinatePerm r) (plusFeature B i))

def standardPolynomial (B : Matrix (Fin 18) (Fin 11) ℝ) :
    Matrix (Fin 11) (Fin 11) Poly3 :=
  squarePolynomial (fun r : Fin 2 × Fin 6 => if r.1=0 then (1/6 : ℝ) else 1/18)
    (fun r i => MvPolynomial.rename (coordinatePerm r.2) (standardFeature B r.1 i))

theorem plusPolynomial_realization (B : Matrix (Fin 16) (Fin 11) ℝ) :
    ThomsonNegative.Geometry.BlockRealization (plusPolynomial B) := by
  apply squarePolynomial_realization
  intro r
  norm_num

theorem standardPolynomial_realization (B : Matrix (Fin 18) (Fin 11) ℝ) :
    ThomsonNegative.Geometry.BlockRealization (standardPolynomial B) := by
  apply squarePolynomial_realization
  intro r
  split_ifs <;> norm_num

def canonicalPolynomialFamily (B : CanonicalBasis) : PolynomialFamily :=
  Fin.cases (momentPolynomial 0 (B.moment 0))
    (Fin.cases (momentPolynomial 1 (B.moment 1))
      (Fin.cases (momentPolynomial 2 (B.moment 2))
        (Fin.cases (momentPolynomial 3 (B.moment 3))
          (Fin.cases (momentPolynomial 4 (B.moment 4))
            (Fin.cases (momentPolynomial 5 (B.moment 5))
              (Fin.cases (plusPolynomial B.plus)
                (Fin.cases (standardPolynomial B.standard) (fun i => Fin.elim0 i))))))))

theorem canonicalPolynomialFamily_realization (B : CanonicalBasis) (b : Block) :
    ThomsonNegative.Geometry.BlockRealization (canonicalPolynomialFamily B b) := by
  fin_cases b
  · exact momentPolynomial_realization 0 (B.moment 0)
  · exact momentPolynomial_realization 1 (B.moment 1)
  · exact momentPolynomial_realization 2 (B.moment 2)
  · exact momentPolynomial_realization 3 (B.moment 3)
  · exact momentPolynomial_realization 4 (B.moment 4)
  · exact momentPolynomial_realization 5 (B.moment 5)
  · exact plusPolynomial_realization B.plus
  · exact standardPolynomial_realization B.standard

end ThomsonNegative.Structure
