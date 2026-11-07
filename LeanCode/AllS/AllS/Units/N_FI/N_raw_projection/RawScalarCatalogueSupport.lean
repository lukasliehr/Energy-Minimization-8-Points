import AllS.Units.N_FI.N_raw_projection.RawScalarSupport
import AllS.Units.N_FI.N_raw_projection.PowerSumCatalogue
import AllS.Units.N_FI.N_raw_projection.PairPowerSumCatalogue

noncomputable section
namespace Blueprint.Thomson.Finite

/-- Family numbers are plus, sign, standard, even, odd, respectively.
The exported matrices also check their source tags and these family labels. -/
structure RawScalarSpec where
  family : ℕ
  det : Bool
  leftQ : Bool
  rightQ : Bool
  tag : Tag
  deriving DecidableEq

def rawScalarCoordinates (s : RawScalarSpec) : Poly3 :=
  match s.family with
  | 0 => rawSymmetricWeight s.det*coordinateMonomial s.tag
  | 1 => rawSymmetricWeight s.det*rawDiscriminantCoordinates*coordinateMonomial s.tag
  | 2 => rawSymmetricWeight s.det*rawStandardCoordinates s.leftQ s.rightQ*coordinateMonomial s.tag
  | 3 => rawEvenCoordinates s.tag
  | 4 => rawOddCoordinates s.tag
  | _ => 0

def normalizeIntegerRawEntry (den : ℕ) (p : List (Tag × ℤ)) : RawCatalogue.SparsePoly :=
  p.map (fun x => (x.1,(x.2:ℚ)/den))

theorem integerRawEntry_subst (den : ℕ) (p : List (Tag × ℤ)) (q : RawCatalogue.SparsePoly)
    (s : RawScalarSpec) (h : normalizeIntegerRawEntry den p=q)
    (hq : RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial q)=rawScalarCoordinates s) :
    sparseInvariantPolynomial (normalizeIntegerRawEntry den p)=invariantSubst (rawScalarCoordinates s) := by
  rw [h,sparseInvariantPolynomial,hq]

#print axioms integerRawEntry_subst
end Blueprint.Thomson.Finite
