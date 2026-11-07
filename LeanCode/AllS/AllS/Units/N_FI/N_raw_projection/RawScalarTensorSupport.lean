import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
import AllS.Units.N_FI.N_gram_map.N_family_and_map

noncomputable section
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

def rawScalarTagList (b : ScalarBlockName) (d : ℕ) : List StandardTag :=
  match b with
  | .m0Plus => (invariantTagList d).map (false,·)
  | .m0Sign => (invariantTagList (d-3)).map (false,·)
  | .m0Standard => standardTagList d
  | .m1Even => (parityTagList (d-1)).map (false,·)
  | .m1Odd => (parityTagList (d-1-1)).map (false,·)
  | .mdetPlus => (invariantTagList (d-2)).map (false,·)
  | .mdetSign => (invariantTagList (d-2-3)).map (false,·)
  | .mdetStandard => standardTagList (d-2)

def rawScalarBasis (b : ScalarBlockName) (minus : Bool) (t : StandardTag) : Poly3 :=
  match b with
  | .m0Plus | .mdetPlus => if minus then 0 else invariantMonomial t.2
  | .m0Sign | .mdetSign => if minus then 0 else deltaPoly*invariantMonomial t.2
  | .m0Standard | .mdetStandard => standardRawFeature minus t
  | .m1Even => if minus then 0 else parityMonomial t.2
  | .m1Odd => if minus then 0 else parityOdd*parityMonomial t.2

def rawScalarProductSpec (b : ScalarBlockName) (t u : StandardTag) : RawScalarSpec :=
  let v := rawTagAdd t.2 u.2
  match b with
  | .m0Plus => ⟨0,false,false,false,v⟩
  | .m0Sign => ⟨1,false,false,false,v⟩
  | .m0Standard => ⟨2,false,t.1 && u.1,t.1 || u.1,v⟩
  | .m1Even => ⟨3,false,false,false,v⟩
  | .m1Odd => ⟨4,false,false,false,v⟩
  | .mdetPlus => ⟨0,true,false,false,v⟩
  | .mdetSign => ⟨1,true,false,false,v⟩
  | .mdetStandard => ⟨2,true,t.1 && u.1,t.1 || u.1,v⟩

def rawScalarBilinear (b : ScalarBlockName) (t u : StandardTag) : Poly3 :=
  reynolds (scalarWeightPoly b*(rawScalarBasis b false t*rawScalarBasis b false u+
    MvPolynomial.C (if scalarBlockStandard b then (1/3 : ℝ) else 0)*
      rawScalarBasis b true t*rawScalarBasis b true u))

theorem rawStandardCoordinates_boolean_sort (p q : Bool) :
    rawStandardCoordinates (p && q) (p || q)=rawStandardCoordinates p q := by
  cases p <;> cases q <;> rfl

theorem rawScalarProductSpec_subst (b : ScalarBlockName) (t u : StandardTag) :
    invariantSubst (rawScalarCoordinates (rawScalarProductSpec b t u))=
      rawScalarBilinear b t u := by
  cases b <;>
    simp only [rawScalarProductSpec,rawScalarCoordinates,rawScalarBilinear,
      rawScalarBasis,scalarWeightPoly,scalarBlockStandard,Bool.false_eq_true,ite_false,ite_true,
      MvPolynomial.C_0,mul_zero,zero_mul,add_zero,rawStandardCoordinates_boolean_sort]
  · simpa only [Bool.false_eq_true,ite_false] using rawPlusBilinear false t.2 u.2
  · simpa only [Bool.false_eq_true,ite_false] using rawSignBilinear false t.2 u.2
  · simpa only [Bool.false_eq_true,ite_false] using rawStandardBilinear false t u
  · exact rawEvenBilinear t.2 u.2
  · exact rawOddBilinear t.2 u.2
  · simpa only [ite_true] using rawPlusBilinear true t.2 u.2
  · simpa only [ite_true] using rawSignBilinear true t.2 u.2
  · simpa only [ite_true] using rawStandardBilinear true t u

theorem rawScalarTensor_entry {n : ℕ} (b : ScalarBlockName) (tags : Fin n → StandardTag)
    (Q : Matrix (Fin n) (Fin n) Poly3)
    (hQ : ∀ i j,Q i j=rawScalarCoordinates (rawScalarProductSpec b (tags i) (tags j))) :
    ∀ i j,invariantSubst (Q i j)=rawScalarBilinear b (tags i) (tags j) := by
  intro i j
  rw [hQ,rawScalarProductSpec_subst]

#print axioms rawScalarProductSpec_subst
end Blueprint.Thomson.Finite
