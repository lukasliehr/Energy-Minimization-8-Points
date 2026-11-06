import AllS.Units.N_FI.N_raw_projection.RawTensorSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

def coordinateMonomial (t : Tag) : Poly3 :=
  MvPolynomial.X 0^t.1*MvPolynomial.X 1^t.2.1*MvPolynomial.X 2^t.2.2

def rawTagAdd (t u : Tag) : Tag := (t.1+u.1,t.2.1+u.2.1,t.2.2+u.2.2)

theorem coordinateMonomial_subst (t : Tag) :
    invariantSubst (coordinateMonomial t)=invariantMonomial t := by
  simp [coordinateMonomial,invariantMonomial,invariantSubst]

theorem invariantMonomial_mul (t u : Tag) :
    invariantMonomial t*invariantMonomial u=invariantMonomial (rawTagAdd t u) := by
  simp only [invariantMonomial,rawTagAdd,pow_add]
  ring

theorem parityMonomial_mul (t u : Tag) :
    parityMonomial t*parityMonomial u=parityMonomial (rawTagAdd t u) := by
  simp only [parityMonomial,rawTagAdd,pow_add]
  ring

def rawInvariantPairPowerSum : ℕ → Poly3
  | 0 => 3
  | 1 => MvPolynomial.X 1
  | 2 => MvPolynomial.X 1^2-2*MvPolynomial.X 0*MvPolynomial.X 2
  | n+3 => MvPolynomial.X 1*rawInvariantPairPowerSum (n+2)-
      MvPolynomial.X 0*MvPolynomial.X 2*rawInvariantPairPowerSum (n+1)+
      MvPolynomial.X 2^2*rawInvariantPairPowerSum n

theorem rawInvariantPairPowerSum_subst (n : ℕ) :
    invariantSubst (rawInvariantPairPowerSum n)=rawPairPowerSum n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · simp only [rawInvariantPairPowerSum,rawPairPowerSum,map_ofNat,pow_zero]
      ring
    · simp [rawInvariantPairPowerSum,rawPairPowerSum,invariantSubst,e2]
    · simp only [rawInvariantPairPowerSum,map_sub,map_mul,map_pow,map_ofNat]
      simpa [invariantSubst] using rawPairPowerSum_initial.2.2.symm
    · rw [rawInvariantPairPowerSum]
      simp only [map_add,map_sub,map_mul,map_pow,
        ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      simpa [invariantSubst] using (rawPairPowerSum_recurrence n).symm

def rawParityCoordinates (i j k : ℕ) : Poly3 :=
  MvPolynomial.C (1/3 : ℝ)*∑ l ∈ Finset.range (j+1),
    (-1:Poly3)^l*(j.choose l:Poly3)*MvPolynomial.X 0^(j-l)*
      (if k ≤ i + l then MvPolynomial.X 2^k*rawInvariantPowerSum (i+l-k)
       else MvPolynomial.X 2^(i+l)*rawInvariantPairPowerSum (k-(i+l)))

theorem rawParityCoordinates_subst (i j k : ℕ) :
    invariantSubst (rawParityCoordinates i j k)=reynolds (parityMonomial (i,j,k)) := by
  rw [raw_projection_parity_formula]
  simp only [rawParityCoordinates,rawParityInvariant,map_mul,map_sum,map_pow,map_neg,
    map_one,map_natCast,apply_ite,rawInvariantPowerSum_subst,rawInvariantPairPowerSum_subst]
  simp [invariantSubst]

def rawEvenCoordinates (t : Tag) : Poly3 :=
  rawParityCoordinates t.1 t.2.1 t.2.2-rawParityCoordinates (t.1+2) t.2.1 t.2.2

def rawOddCoordinates (t : Tag) : Poly3 :=
  rawEvenCoordinates (t.1,t.2.1+2,t.2.2)-4*rawEvenCoordinates (t.1,t.2.1,t.2.2+1)

theorem rawEvenCoordinates_subst (t : Tag) :
    invariantSubst (rawEvenCoordinates t)=reynolds (edgeWeightPoly*parityMonomial t) := by
  rw [rawEvenCoordinates,map_sub,rawParityCoordinates_subst,rawParityCoordinates_subst,
    ← map_sub]
  congr 1
  simp only [parityMonomial,edgeWeightPoly,pow_add]
  ring

theorem reynolds_C_mul (c : ℝ) (p : Poly3) :
    reynolds (MvPolynomial.C c*p)=MvPolynomial.C c*reynolds p := by
  simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using reynolds.map_smul c p

theorem rawOddCoordinates_subst (t : Tag) :
    invariantSubst (rawOddCoordinates t)=
      reynolds (edgeWeightPoly*(parityOdd^2*parityMonomial t)) := by
  simp only [rawOddCoordinates,map_sub,map_mul,map_ofNat,rawEvenCoordinates_subst]
  rw [show (4:Poly3)=MvPolynomial.C (4:ℝ) by simp only [map_ofNat],← reynolds_C_mul,← map_sub]
  congr 1
  simp only [parityMonomial,parityOdd,parityZ,parityW,pow_add,map_ofNat]
  ring

def rawDiscriminantCoordinates : Poly3 :=
  MvPolynomial.X 0^2*MvPolynomial.X 1^2-4*MvPolynomial.X 1^3-
    4*MvPolynomial.X 0^3*MvPolynomial.X 2-27*MvPolynomial.X 2^2+
    18*MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 2

def rawDeterminantCoordinates : Poly3 :=
  1-MvPolynomial.X 0^2+2*MvPolynomial.X 1+2*MvPolynomial.X 2

theorem rawDiscriminantCoordinates_subst :
    invariantSubst rawDiscriminantCoordinates=deltaPoly^2 := by
  rw [raw_delta_square]
  simp only [rawDiscriminantCoordinates,map_sub,map_add,map_mul,map_pow,map_ofNat]
  simp [invariantSubst]

theorem rawDeterminantCoordinates_subst :
    invariantSubst rawDeterminantCoordinates=determinantWeightPoly := by
  simp only [rawDeterminantCoordinates,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]
  simp [invariantSubst,determinantWeightPoly,sigma,e2,e3]
  ring

def rawStandardCoordinates (p q : Bool) : Poly3 :=
  if p && q then
    MvPolynomial.C (4/81 : ℝ)*MvPolynomial.X 0^4-
      MvPolynomial.C (8/27 : ℝ)*MvPolynomial.X 0^2*MvPolynomial.X 1+
      MvPolynomial.C (4/9 : ℝ)*MvPolynomial.X 1^2
  else if p || q then
    MvPolynomial.C (4/27 : ℝ)*MvPolynomial.X 0^3-
      MvPolynomial.C (2/3 : ℝ)*MvPolynomial.X 0*MvPolynomial.X 1+2*MvPolynomial.X 2
  else MvPolynomial.C (4/9 : ℝ)*MvPolynomial.X 0^2-
    MvPolynomial.C (4/3 : ℝ)*MvPolynomial.X 1

theorem rawStandardCoordinates_subst (p q : Bool) :
    invariantSubst (rawStandardCoordinates p q)=
      rawStandardPairing (if p then standardQPoly else standardPPoly)
        (if q then standardQPoly else standardPPoly) := by
  have hc : rawStandardPairing standardQPoly standardPPoly=
      rawStandardPairing standardPPoly standardQPoly := by unfold rawStandardPairing;ring
  cases p <;> cases q <;>
    simp only [rawStandardCoordinates,Bool.and_false,Bool.and_true,Bool.or_false,Bool.or_true,
      Bool.false_eq_true,ite_false,ite_true,map_add,map_sub,map_mul,map_pow,map_ofNat] <;>
    simp [invariantSubst,hc,raw_standard_PP,raw_standard_PQ,raw_standard_QQ]

theorem rawEvenBilinear (t u : Tag) :
    invariantSubst (rawEvenCoordinates (rawTagAdd t u))=
      reynolds (edgeWeightPoly*(parityMonomial t*parityMonomial u)) := by
  rw [parityMonomial_mul,rawEvenCoordinates_subst]

theorem rawOddBilinear (t u : Tag) :
    invariantSubst (rawOddCoordinates (rawTagAdd t u))=
      reynolds (edgeWeightPoly*((parityOdd*parityMonomial t)*(parityOdd*parityMonomial u))) := by
  rw [rawOddCoordinates_subst,← parityMonomial_mul]
  congr 1
  ring

def rawSymmetricWeight (det : Bool) : Poly3 :=
  if det then rawDeterminantCoordinates else 1

theorem rawSymmetricWeight_subst (det : Bool) :
    invariantSubst (rawSymmetricWeight det)=(if det then determinantWeightPoly else 1) := by
  cases det <;> simp [rawSymmetricWeight,rawDeterminantCoordinates_subst]

theorem rawPlusBilinear (det : Bool) (t u : Tag) :
    invariantSubst (rawSymmetricWeight det*coordinateMonomial (rawTagAdd t u))=
      reynolds ((if det then determinantWeightPoly else 1)*
        (invariantMonomial t*invariantMonomial u)) := by
  have h : invariantSubst (rawSymmetricWeight det*coordinateMonomial (rawTagAdd t u))=
      (if det then determinantWeightPoly else 1)*(invariantMonomial t*invariantMonomial u) := by
    rw [map_mul,rawSymmetricWeight_subst,coordinateMonomial_subst,invariantMonomial_mul]
  rw [← h,reynolds_of_symmetric _ (invariantSubst_symmetric _)]

theorem rawSignBilinear (det : Bool) (t u : Tag) :
    invariantSubst (rawSymmetricWeight det*rawDiscriminantCoordinates*
      coordinateMonomial (rawTagAdd t u))=
      reynolds ((if det then determinantWeightPoly else 1)*
        ((deltaPoly*invariantMonomial t)*(deltaPoly*invariantMonomial u))) := by
  have h : invariantSubst (rawSymmetricWeight det*rawDiscriminantCoordinates*
      coordinateMonomial (rawTagAdd t u))=
      (if det then determinantWeightPoly else 1)*
        ((deltaPoly*invariantMonomial t)*(deltaPoly*invariantMonomial u)) := by
    simp only [map_mul,rawSymmetricWeight_subst,rawDiscriminantCoordinates_subst,
      coordinateMonomial_subst,← invariantMonomial_mul]
    ring
  rw [← h,reynolds_of_symmetric _ (invariantSubst_symmetric _)]

theorem rawStandardBilinear (det : Bool) (t u : StandardTag) :
    invariantSubst (rawSymmetricWeight det*rawStandardCoordinates t.1 u.1*
      coordinateMonomial (rawTagAdd t.2 u.2))=
      reynolds ((if det then determinantWeightPoly else 1)*
        (standardRawFeature false t*standardRawFeature false u+
          MvPolynomial.C (1/3 : ℝ)*standardRawFeature true t*standardRawFeature true u)) := by
  have h : invariantSubst (rawSymmetricWeight det*rawStandardCoordinates t.1 u.1*
      coordinateMonomial (rawTagAdd t.2 u.2))=
      (if det then determinantWeightPoly else 1)*
        (standardRawFeature false t*standardRawFeature false u+
          MvPolynomial.C (1/3 : ℝ)*standardRawFeature true t*standardRawFeature true u) := by
    simp only [map_mul,rawSymmetricWeight_subst,rawStandardCoordinates_subst,
      coordinateMonomial_subst,← invariantMonomial_mul]
    cases ht : t.1 <;> cases hu : u.1 <;>
      simp only [ht,hu,standardRawFeature,rawStandardPairing,Bool.false_eq_true,ite_false,ite_true] <;> ring
  rw [← h,reynolds_of_symmetric _ (invariantSubst_symmetric _)]

#print axioms rawEvenBilinear
#print axioms rawOddBilinear
#print axioms rawStandardCoordinates_subst
#print axioms rawPlusBilinear
#print axioms rawSignBilinear
#print axioms rawStandardBilinear
end Blueprint.Thomson.Finite
