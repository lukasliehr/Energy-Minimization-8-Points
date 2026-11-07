import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment6_0_0
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment6_0_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment6_0_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment6_1_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment6_1_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment6_2_2
import AllS.Units.N_FI.N_gram_map.N_physical_entries
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentTensors.D16_F6
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def denominator : ℕ := RawMomentCatalogue.Moment6_0_0.denominator16
def source : Matrix (Fin 3) (Fin 3) (List (Tag × ℤ)) := ![![RawMomentCatalogue.Moment6_0_0.raw16,RawMomentCatalogue.Moment6_0_1.raw16,RawMomentCatalogue.Moment6_0_2.raw16],![RawMomentCatalogue.Moment6_0_1.raw16,RawMomentCatalogue.Moment6_1_1.raw16,RawMomentCatalogue.Moment6_1_2.raw16],![RawMomentCatalogue.Moment6_0_2.raw16,RawMomentCatalogue.Moment6_1_2.raw16,RawMomentCatalogue.Moment6_2_2.raw16]]
def coordinatePolynomial (i j : Fin 3) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem subst_coordinatePolynomial (i j : Fin 3) :
    invariantSubst (coordinatePolynomial i j)=kernelRPoly 6 i.val j.val := by
  fin_cases i <;> fin_cases j
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_0_0.denominator16)) RawMomentCatalogue.Moment6_0_0.raw16)=kernelRPoly 6 0 0
    rw [RawMomentCatalogue.Moment6_0_0.normalize_16]
    exact RawMomentCatalogue.Moment6_0_0.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_0_1.denominator16)) RawMomentCatalogue.Moment6_0_1.raw16)=kernelRPoly 6 0 1
    rw [RawMomentCatalogue.Moment6_0_1.normalize_16]
    exact RawMomentCatalogue.Moment6_0_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_0_2.denominator16)) RawMomentCatalogue.Moment6_0_2.raw16)=kernelRPoly 6 0 2
    rw [RawMomentCatalogue.Moment6_0_2.normalize_16]
    exact RawMomentCatalogue.Moment6_0_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_0_1.denominator16)) RawMomentCatalogue.Moment6_0_1.raw16)=kernelRPoly 6 1 0
    rw [RawMomentCatalogue.Moment6_0_1.normalize_16]
    exact RawMomentCatalogue.Moment6_0_1.identity.trans (kernelRPoly_transpose 6 0 1)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_1_1.denominator16)) RawMomentCatalogue.Moment6_1_1.raw16)=kernelRPoly 6 1 1
    rw [RawMomentCatalogue.Moment6_1_1.normalize_16]
    exact RawMomentCatalogue.Moment6_1_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_1_2.denominator16)) RawMomentCatalogue.Moment6_1_2.raw16)=kernelRPoly 6 1 2
    rw [RawMomentCatalogue.Moment6_1_2.normalize_16]
    exact RawMomentCatalogue.Moment6_1_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_0_2.denominator16)) RawMomentCatalogue.Moment6_0_2.raw16)=kernelRPoly 6 2 0
    rw [RawMomentCatalogue.Moment6_0_2.normalize_16]
    exact RawMomentCatalogue.Moment6_0_2.identity.trans (kernelRPoly_transpose 6 0 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_1_2.denominator16)) RawMomentCatalogue.Moment6_1_2.raw16)=kernelRPoly 6 2 1
    rw [RawMomentCatalogue.Moment6_1_2.normalize_16]
    exact RawMomentCatalogue.Moment6_1_2.identity.trans (kernelRPoly_transpose 6 1 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment6_2_2.denominator16)) RawMomentCatalogue.Moment6_2_2.raw16)=kernelRPoly 6 2 2
    rw [RawMomentCatalogue.Moment6_2_2.normalize_16]
    exact RawMomentCatalogue.Moment6_2_2.identity
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawMomentTensors.D16_F6
