import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_0_0
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_0_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_0_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_0_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_0_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_1_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_1_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_1_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_1_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_2_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_2_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_2_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_3_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_3_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment5_4_4
import AllS.Units.N_FI.N_gram_map.N_physical_entries
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentTensors.D18_F5
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def denominator : ℕ := RawMomentCatalogue.Moment5_0_0.denominator18
def source : Matrix (Fin 5) (Fin 5) (List (Tag × ℤ)) := ![![RawMomentCatalogue.Moment5_0_0.raw18,RawMomentCatalogue.Moment5_0_1.raw18,RawMomentCatalogue.Moment5_0_2.raw18,RawMomentCatalogue.Moment5_0_3.raw18,RawMomentCatalogue.Moment5_0_4.raw18],![RawMomentCatalogue.Moment5_0_1.raw18,RawMomentCatalogue.Moment5_1_1.raw18,RawMomentCatalogue.Moment5_1_2.raw18,RawMomentCatalogue.Moment5_1_3.raw18,RawMomentCatalogue.Moment5_1_4.raw18],![RawMomentCatalogue.Moment5_0_2.raw18,RawMomentCatalogue.Moment5_1_2.raw18,RawMomentCatalogue.Moment5_2_2.raw18,RawMomentCatalogue.Moment5_2_3.raw18,RawMomentCatalogue.Moment5_2_4.raw18],![RawMomentCatalogue.Moment5_0_3.raw18,RawMomentCatalogue.Moment5_1_3.raw18,RawMomentCatalogue.Moment5_2_3.raw18,RawMomentCatalogue.Moment5_3_3.raw18,RawMomentCatalogue.Moment5_3_4.raw18],![RawMomentCatalogue.Moment5_0_4.raw18,RawMomentCatalogue.Moment5_1_4.raw18,RawMomentCatalogue.Moment5_2_4.raw18,RawMomentCatalogue.Moment5_3_4.raw18,RawMomentCatalogue.Moment5_4_4.raw18]]
def coordinatePolynomial (i j : Fin 5) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem subst_coordinatePolynomial (i j : Fin 5) :
    invariantSubst (coordinatePolynomial i j)=kernelRPoly 5 i.val j.val := by
  fin_cases i <;> fin_cases j
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_0.denominator18)) RawMomentCatalogue.Moment5_0_0.raw18)=kernelRPoly 5 0 0
    rw [RawMomentCatalogue.Moment5_0_0.normalize_18]
    exact RawMomentCatalogue.Moment5_0_0.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_1.denominator18)) RawMomentCatalogue.Moment5_0_1.raw18)=kernelRPoly 5 0 1
    rw [RawMomentCatalogue.Moment5_0_1.normalize_18]
    exact RawMomentCatalogue.Moment5_0_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_2.denominator18)) RawMomentCatalogue.Moment5_0_2.raw18)=kernelRPoly 5 0 2
    rw [RawMomentCatalogue.Moment5_0_2.normalize_18]
    exact RawMomentCatalogue.Moment5_0_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_3.denominator18)) RawMomentCatalogue.Moment5_0_3.raw18)=kernelRPoly 5 0 3
    rw [RawMomentCatalogue.Moment5_0_3.normalize_18]
    exact RawMomentCatalogue.Moment5_0_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_4.denominator18)) RawMomentCatalogue.Moment5_0_4.raw18)=kernelRPoly 5 0 4
    rw [RawMomentCatalogue.Moment5_0_4.normalize_18]
    exact RawMomentCatalogue.Moment5_0_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_1.denominator18)) RawMomentCatalogue.Moment5_0_1.raw18)=kernelRPoly 5 1 0
    rw [RawMomentCatalogue.Moment5_0_1.normalize_18]
    exact RawMomentCatalogue.Moment5_0_1.identity.trans (kernelRPoly_transpose 5 0 1)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_1.denominator18)) RawMomentCatalogue.Moment5_1_1.raw18)=kernelRPoly 5 1 1
    rw [RawMomentCatalogue.Moment5_1_1.normalize_18]
    exact RawMomentCatalogue.Moment5_1_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_2.denominator18)) RawMomentCatalogue.Moment5_1_2.raw18)=kernelRPoly 5 1 2
    rw [RawMomentCatalogue.Moment5_1_2.normalize_18]
    exact RawMomentCatalogue.Moment5_1_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_3.denominator18)) RawMomentCatalogue.Moment5_1_3.raw18)=kernelRPoly 5 1 3
    rw [RawMomentCatalogue.Moment5_1_3.normalize_18]
    exact RawMomentCatalogue.Moment5_1_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_4.denominator18)) RawMomentCatalogue.Moment5_1_4.raw18)=kernelRPoly 5 1 4
    rw [RawMomentCatalogue.Moment5_1_4.normalize_18]
    exact RawMomentCatalogue.Moment5_1_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_2.denominator18)) RawMomentCatalogue.Moment5_0_2.raw18)=kernelRPoly 5 2 0
    rw [RawMomentCatalogue.Moment5_0_2.normalize_18]
    exact RawMomentCatalogue.Moment5_0_2.identity.trans (kernelRPoly_transpose 5 0 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_2.denominator18)) RawMomentCatalogue.Moment5_1_2.raw18)=kernelRPoly 5 2 1
    rw [RawMomentCatalogue.Moment5_1_2.normalize_18]
    exact RawMomentCatalogue.Moment5_1_2.identity.trans (kernelRPoly_transpose 5 1 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_2_2.denominator18)) RawMomentCatalogue.Moment5_2_2.raw18)=kernelRPoly 5 2 2
    rw [RawMomentCatalogue.Moment5_2_2.normalize_18]
    exact RawMomentCatalogue.Moment5_2_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_2_3.denominator18)) RawMomentCatalogue.Moment5_2_3.raw18)=kernelRPoly 5 2 3
    rw [RawMomentCatalogue.Moment5_2_3.normalize_18]
    exact RawMomentCatalogue.Moment5_2_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_2_4.denominator18)) RawMomentCatalogue.Moment5_2_4.raw18)=kernelRPoly 5 2 4
    rw [RawMomentCatalogue.Moment5_2_4.normalize_18]
    exact RawMomentCatalogue.Moment5_2_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_3.denominator18)) RawMomentCatalogue.Moment5_0_3.raw18)=kernelRPoly 5 3 0
    rw [RawMomentCatalogue.Moment5_0_3.normalize_18]
    exact RawMomentCatalogue.Moment5_0_3.identity.trans (kernelRPoly_transpose 5 0 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_3.denominator18)) RawMomentCatalogue.Moment5_1_3.raw18)=kernelRPoly 5 3 1
    rw [RawMomentCatalogue.Moment5_1_3.normalize_18]
    exact RawMomentCatalogue.Moment5_1_3.identity.trans (kernelRPoly_transpose 5 1 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_2_3.denominator18)) RawMomentCatalogue.Moment5_2_3.raw18)=kernelRPoly 5 3 2
    rw [RawMomentCatalogue.Moment5_2_3.normalize_18]
    exact RawMomentCatalogue.Moment5_2_3.identity.trans (kernelRPoly_transpose 5 2 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_3_3.denominator18)) RawMomentCatalogue.Moment5_3_3.raw18)=kernelRPoly 5 3 3
    rw [RawMomentCatalogue.Moment5_3_3.normalize_18]
    exact RawMomentCatalogue.Moment5_3_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_3_4.denominator18)) RawMomentCatalogue.Moment5_3_4.raw18)=kernelRPoly 5 3 4
    rw [RawMomentCatalogue.Moment5_3_4.normalize_18]
    exact RawMomentCatalogue.Moment5_3_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_0_4.denominator18)) RawMomentCatalogue.Moment5_0_4.raw18)=kernelRPoly 5 4 0
    rw [RawMomentCatalogue.Moment5_0_4.normalize_18]
    exact RawMomentCatalogue.Moment5_0_4.identity.trans (kernelRPoly_transpose 5 0 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_1_4.denominator18)) RawMomentCatalogue.Moment5_1_4.raw18)=kernelRPoly 5 4 1
    rw [RawMomentCatalogue.Moment5_1_4.normalize_18]
    exact RawMomentCatalogue.Moment5_1_4.identity.trans (kernelRPoly_transpose 5 1 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_2_4.denominator18)) RawMomentCatalogue.Moment5_2_4.raw18)=kernelRPoly 5 4 2
    rw [RawMomentCatalogue.Moment5_2_4.normalize_18]
    exact RawMomentCatalogue.Moment5_2_4.identity.trans (kernelRPoly_transpose 5 2 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_3_4.denominator18)) RawMomentCatalogue.Moment5_3_4.raw18)=kernelRPoly 5 4 3
    rw [RawMomentCatalogue.Moment5_3_4.normalize_18]
    exact RawMomentCatalogue.Moment5_3_4.identity.trans (kernelRPoly_transpose 5 3 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment5_4_4.denominator18)) RawMomentCatalogue.Moment5_4_4.raw18)=kernelRPoly 5 4 4
    rw [RawMomentCatalogue.Moment5_4_4.normalize_18]
    exact RawMomentCatalogue.Moment5_4_4.identity
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawMomentTensors.D18_F5
