import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_0
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_3_3
import AllS.Units.N_FI.N_gram_map.N_physical_entries
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentTensors.D12_F3
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def denominator : ℕ := RawMomentCatalogue.Moment3_0_0.denominator12
def source : Matrix (Fin 4) (Fin 4) (List (Tag × ℤ)) := ![![RawMomentCatalogue.Moment3_0_0.raw12,RawMomentCatalogue.Moment3_0_1.raw12,RawMomentCatalogue.Moment3_0_2.raw12,RawMomentCatalogue.Moment3_0_3.raw12],![RawMomentCatalogue.Moment3_0_1.raw12,RawMomentCatalogue.Moment3_1_1.raw12,RawMomentCatalogue.Moment3_1_2.raw12,RawMomentCatalogue.Moment3_1_3.raw12],![RawMomentCatalogue.Moment3_0_2.raw12,RawMomentCatalogue.Moment3_1_2.raw12,RawMomentCatalogue.Moment3_2_2.raw12,RawMomentCatalogue.Moment3_2_3.raw12],![RawMomentCatalogue.Moment3_0_3.raw12,RawMomentCatalogue.Moment3_1_3.raw12,RawMomentCatalogue.Moment3_2_3.raw12,RawMomentCatalogue.Moment3_3_3.raw12]]
def coordinatePolynomial (i j : Fin 4) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem subst_coordinatePolynomial (i j : Fin 4) :
    invariantSubst (coordinatePolynomial i j)=kernelRPoly 3 i.val j.val := by
  fin_cases i <;> fin_cases j
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_0.denominator12)) RawMomentCatalogue.Moment3_0_0.raw12)=kernelRPoly 3 0 0
    rw [RawMomentCatalogue.Moment3_0_0.normalize_12]
    exact RawMomentCatalogue.Moment3_0_0.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_1.denominator12)) RawMomentCatalogue.Moment3_0_1.raw12)=kernelRPoly 3 0 1
    rw [RawMomentCatalogue.Moment3_0_1.normalize_12]
    exact RawMomentCatalogue.Moment3_0_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_2.denominator12)) RawMomentCatalogue.Moment3_0_2.raw12)=kernelRPoly 3 0 2
    rw [RawMomentCatalogue.Moment3_0_2.normalize_12]
    exact RawMomentCatalogue.Moment3_0_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_3.denominator12)) RawMomentCatalogue.Moment3_0_3.raw12)=kernelRPoly 3 0 3
    rw [RawMomentCatalogue.Moment3_0_3.normalize_12]
    exact RawMomentCatalogue.Moment3_0_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_1.denominator12)) RawMomentCatalogue.Moment3_0_1.raw12)=kernelRPoly 3 1 0
    rw [RawMomentCatalogue.Moment3_0_1.normalize_12]
    exact RawMomentCatalogue.Moment3_0_1.identity.trans (kernelRPoly_transpose 3 0 1)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_1.denominator12)) RawMomentCatalogue.Moment3_1_1.raw12)=kernelRPoly 3 1 1
    rw [RawMomentCatalogue.Moment3_1_1.normalize_12]
    exact RawMomentCatalogue.Moment3_1_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_2.denominator12)) RawMomentCatalogue.Moment3_1_2.raw12)=kernelRPoly 3 1 2
    rw [RawMomentCatalogue.Moment3_1_2.normalize_12]
    exact RawMomentCatalogue.Moment3_1_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_3.denominator12)) RawMomentCatalogue.Moment3_1_3.raw12)=kernelRPoly 3 1 3
    rw [RawMomentCatalogue.Moment3_1_3.normalize_12]
    exact RawMomentCatalogue.Moment3_1_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_2.denominator12)) RawMomentCatalogue.Moment3_0_2.raw12)=kernelRPoly 3 2 0
    rw [RawMomentCatalogue.Moment3_0_2.normalize_12]
    exact RawMomentCatalogue.Moment3_0_2.identity.trans (kernelRPoly_transpose 3 0 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_2.denominator12)) RawMomentCatalogue.Moment3_1_2.raw12)=kernelRPoly 3 2 1
    rw [RawMomentCatalogue.Moment3_1_2.normalize_12]
    exact RawMomentCatalogue.Moment3_1_2.identity.trans (kernelRPoly_transpose 3 1 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_2.denominator12)) RawMomentCatalogue.Moment3_2_2.raw12)=kernelRPoly 3 2 2
    rw [RawMomentCatalogue.Moment3_2_2.normalize_12]
    exact RawMomentCatalogue.Moment3_2_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_3.denominator12)) RawMomentCatalogue.Moment3_2_3.raw12)=kernelRPoly 3 2 3
    rw [RawMomentCatalogue.Moment3_2_3.normalize_12]
    exact RawMomentCatalogue.Moment3_2_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_3.denominator12)) RawMomentCatalogue.Moment3_0_3.raw12)=kernelRPoly 3 3 0
    rw [RawMomentCatalogue.Moment3_0_3.normalize_12]
    exact RawMomentCatalogue.Moment3_0_3.identity.trans (kernelRPoly_transpose 3 0 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_3.denominator12)) RawMomentCatalogue.Moment3_1_3.raw12)=kernelRPoly 3 3 1
    rw [RawMomentCatalogue.Moment3_1_3.normalize_12]
    exact RawMomentCatalogue.Moment3_1_3.identity.trans (kernelRPoly_transpose 3 1 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_3.denominator12)) RawMomentCatalogue.Moment3_2_3.raw12)=kernelRPoly 3 3 2
    rw [RawMomentCatalogue.Moment3_2_3.normalize_12]
    exact RawMomentCatalogue.Moment3_2_3.identity.trans (kernelRPoly_transpose 3 2 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_3.denominator12)) RawMomentCatalogue.Moment3_3_3.raw12)=kernelRPoly 3 3 3
    rw [RawMomentCatalogue.Moment3_3_3.normalize_12]
    exact RawMomentCatalogue.Moment3_3_3.identity
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawMomentTensors.D12_F3
