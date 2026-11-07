import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment8_0_0
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment8_0_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment8_1_1
import AllS.Units.N_FI.N_gram_map.N_physical_entries
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentTensors.D18_F8
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def denominator : ℕ := RawMomentCatalogue.Moment8_0_0.denominator18
def source : Matrix (Fin 2) (Fin 2) (List (Tag × ℤ)) := ![![RawMomentCatalogue.Moment8_0_0.raw18,RawMomentCatalogue.Moment8_0_1.raw18],![RawMomentCatalogue.Moment8_0_1.raw18,RawMomentCatalogue.Moment8_1_1.raw18]]
def coordinatePolynomial (i j : Fin 2) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem subst_coordinatePolynomial (i j : Fin 2) :
    invariantSubst (coordinatePolynomial i j)=kernelRPoly 8 i.val j.val := by
  fin_cases i <;> fin_cases j
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment8_0_0.denominator18)) RawMomentCatalogue.Moment8_0_0.raw18)=kernelRPoly 8 0 0
    rw [RawMomentCatalogue.Moment8_0_0.normalize_18]
    exact RawMomentCatalogue.Moment8_0_0.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment8_0_1.denominator18)) RawMomentCatalogue.Moment8_0_1.raw18)=kernelRPoly 8 0 1
    rw [RawMomentCatalogue.Moment8_0_1.normalize_18]
    exact RawMomentCatalogue.Moment8_0_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment8_0_1.denominator18)) RawMomentCatalogue.Moment8_0_1.raw18)=kernelRPoly 8 1 0
    rw [RawMomentCatalogue.Moment8_0_1.normalize_18]
    exact RawMomentCatalogue.Moment8_0_1.identity.trans (kernelRPoly_transpose 8 0 1)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment8_1_1.denominator18)) RawMomentCatalogue.Moment8_1_1.raw18)=kernelRPoly 8 1 1
    rw [RawMomentCatalogue.Moment8_1_1.normalize_18]
    exact RawMomentCatalogue.Moment8_1_1.identity
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawMomentTensors.D18_F8
