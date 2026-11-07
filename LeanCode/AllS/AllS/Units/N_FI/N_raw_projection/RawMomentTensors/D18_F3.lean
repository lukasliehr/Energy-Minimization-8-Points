import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_0
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_0_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_1_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_2_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_3_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_3_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_3_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_3_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_4_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_4_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_4_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_5_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_5_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment3_6_6
import AllS.Units.N_FI.N_gram_map.N_physical_entries
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentTensors.D18_F3
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def denominator : ℕ := RawMomentCatalogue.Moment3_0_0.denominator18
def source : Matrix (Fin 7) (Fin 7) (List (Tag × ℤ)) := ![![RawMomentCatalogue.Moment3_0_0.raw18,RawMomentCatalogue.Moment3_0_1.raw18,RawMomentCatalogue.Moment3_0_2.raw18,RawMomentCatalogue.Moment3_0_3.raw18,RawMomentCatalogue.Moment3_0_4.raw18,RawMomentCatalogue.Moment3_0_5.raw18,RawMomentCatalogue.Moment3_0_6.raw18],![RawMomentCatalogue.Moment3_0_1.raw18,RawMomentCatalogue.Moment3_1_1.raw18,RawMomentCatalogue.Moment3_1_2.raw18,RawMomentCatalogue.Moment3_1_3.raw18,RawMomentCatalogue.Moment3_1_4.raw18,RawMomentCatalogue.Moment3_1_5.raw18,RawMomentCatalogue.Moment3_1_6.raw18],![RawMomentCatalogue.Moment3_0_2.raw18,RawMomentCatalogue.Moment3_1_2.raw18,RawMomentCatalogue.Moment3_2_2.raw18,RawMomentCatalogue.Moment3_2_3.raw18,RawMomentCatalogue.Moment3_2_4.raw18,RawMomentCatalogue.Moment3_2_5.raw18,RawMomentCatalogue.Moment3_2_6.raw18],![RawMomentCatalogue.Moment3_0_3.raw18,RawMomentCatalogue.Moment3_1_3.raw18,RawMomentCatalogue.Moment3_2_3.raw18,RawMomentCatalogue.Moment3_3_3.raw18,RawMomentCatalogue.Moment3_3_4.raw18,RawMomentCatalogue.Moment3_3_5.raw18,RawMomentCatalogue.Moment3_3_6.raw18],![RawMomentCatalogue.Moment3_0_4.raw18,RawMomentCatalogue.Moment3_1_4.raw18,RawMomentCatalogue.Moment3_2_4.raw18,RawMomentCatalogue.Moment3_3_4.raw18,RawMomentCatalogue.Moment3_4_4.raw18,RawMomentCatalogue.Moment3_4_5.raw18,RawMomentCatalogue.Moment3_4_6.raw18],![RawMomentCatalogue.Moment3_0_5.raw18,RawMomentCatalogue.Moment3_1_5.raw18,RawMomentCatalogue.Moment3_2_5.raw18,RawMomentCatalogue.Moment3_3_5.raw18,RawMomentCatalogue.Moment3_4_5.raw18,RawMomentCatalogue.Moment3_5_5.raw18,RawMomentCatalogue.Moment3_5_6.raw18],![RawMomentCatalogue.Moment3_0_6.raw18,RawMomentCatalogue.Moment3_1_6.raw18,RawMomentCatalogue.Moment3_2_6.raw18,RawMomentCatalogue.Moment3_3_6.raw18,RawMomentCatalogue.Moment3_4_6.raw18,RawMomentCatalogue.Moment3_5_6.raw18,RawMomentCatalogue.Moment3_6_6.raw18]]
def coordinatePolynomial (i j : Fin 7) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem subst_coordinatePolynomial (i j : Fin 7) :
    invariantSubst (coordinatePolynomial i j)=kernelRPoly 3 i.val j.val := by
  fin_cases i <;> fin_cases j
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_0.denominator18)) RawMomentCatalogue.Moment3_0_0.raw18)=kernelRPoly 3 0 0
    rw [RawMomentCatalogue.Moment3_0_0.normalize_18]
    exact RawMomentCatalogue.Moment3_0_0.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_1.denominator18)) RawMomentCatalogue.Moment3_0_1.raw18)=kernelRPoly 3 0 1
    rw [RawMomentCatalogue.Moment3_0_1.normalize_18]
    exact RawMomentCatalogue.Moment3_0_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_2.denominator18)) RawMomentCatalogue.Moment3_0_2.raw18)=kernelRPoly 3 0 2
    rw [RawMomentCatalogue.Moment3_0_2.normalize_18]
    exact RawMomentCatalogue.Moment3_0_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_3.denominator18)) RawMomentCatalogue.Moment3_0_3.raw18)=kernelRPoly 3 0 3
    rw [RawMomentCatalogue.Moment3_0_3.normalize_18]
    exact RawMomentCatalogue.Moment3_0_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_4.denominator18)) RawMomentCatalogue.Moment3_0_4.raw18)=kernelRPoly 3 0 4
    rw [RawMomentCatalogue.Moment3_0_4.normalize_18]
    exact RawMomentCatalogue.Moment3_0_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_5.denominator18)) RawMomentCatalogue.Moment3_0_5.raw18)=kernelRPoly 3 0 5
    rw [RawMomentCatalogue.Moment3_0_5.normalize_18]
    exact RawMomentCatalogue.Moment3_0_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_6.denominator18)) RawMomentCatalogue.Moment3_0_6.raw18)=kernelRPoly 3 0 6
    rw [RawMomentCatalogue.Moment3_0_6.normalize_18]
    exact RawMomentCatalogue.Moment3_0_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_1.denominator18)) RawMomentCatalogue.Moment3_0_1.raw18)=kernelRPoly 3 1 0
    rw [RawMomentCatalogue.Moment3_0_1.normalize_18]
    exact RawMomentCatalogue.Moment3_0_1.identity.trans (kernelRPoly_transpose 3 0 1)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_1.denominator18)) RawMomentCatalogue.Moment3_1_1.raw18)=kernelRPoly 3 1 1
    rw [RawMomentCatalogue.Moment3_1_1.normalize_18]
    exact RawMomentCatalogue.Moment3_1_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_2.denominator18)) RawMomentCatalogue.Moment3_1_2.raw18)=kernelRPoly 3 1 2
    rw [RawMomentCatalogue.Moment3_1_2.normalize_18]
    exact RawMomentCatalogue.Moment3_1_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_3.denominator18)) RawMomentCatalogue.Moment3_1_3.raw18)=kernelRPoly 3 1 3
    rw [RawMomentCatalogue.Moment3_1_3.normalize_18]
    exact RawMomentCatalogue.Moment3_1_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_4.denominator18)) RawMomentCatalogue.Moment3_1_4.raw18)=kernelRPoly 3 1 4
    rw [RawMomentCatalogue.Moment3_1_4.normalize_18]
    exact RawMomentCatalogue.Moment3_1_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_5.denominator18)) RawMomentCatalogue.Moment3_1_5.raw18)=kernelRPoly 3 1 5
    rw [RawMomentCatalogue.Moment3_1_5.normalize_18]
    exact RawMomentCatalogue.Moment3_1_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_6.denominator18)) RawMomentCatalogue.Moment3_1_6.raw18)=kernelRPoly 3 1 6
    rw [RawMomentCatalogue.Moment3_1_6.normalize_18]
    exact RawMomentCatalogue.Moment3_1_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_2.denominator18)) RawMomentCatalogue.Moment3_0_2.raw18)=kernelRPoly 3 2 0
    rw [RawMomentCatalogue.Moment3_0_2.normalize_18]
    exact RawMomentCatalogue.Moment3_0_2.identity.trans (kernelRPoly_transpose 3 0 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_2.denominator18)) RawMomentCatalogue.Moment3_1_2.raw18)=kernelRPoly 3 2 1
    rw [RawMomentCatalogue.Moment3_1_2.normalize_18]
    exact RawMomentCatalogue.Moment3_1_2.identity.trans (kernelRPoly_transpose 3 1 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_2.denominator18)) RawMomentCatalogue.Moment3_2_2.raw18)=kernelRPoly 3 2 2
    rw [RawMomentCatalogue.Moment3_2_2.normalize_18]
    exact RawMomentCatalogue.Moment3_2_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_3.denominator18)) RawMomentCatalogue.Moment3_2_3.raw18)=kernelRPoly 3 2 3
    rw [RawMomentCatalogue.Moment3_2_3.normalize_18]
    exact RawMomentCatalogue.Moment3_2_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_4.denominator18)) RawMomentCatalogue.Moment3_2_4.raw18)=kernelRPoly 3 2 4
    rw [RawMomentCatalogue.Moment3_2_4.normalize_18]
    exact RawMomentCatalogue.Moment3_2_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_5.denominator18)) RawMomentCatalogue.Moment3_2_5.raw18)=kernelRPoly 3 2 5
    rw [RawMomentCatalogue.Moment3_2_5.normalize_18]
    exact RawMomentCatalogue.Moment3_2_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_6.denominator18)) RawMomentCatalogue.Moment3_2_6.raw18)=kernelRPoly 3 2 6
    rw [RawMomentCatalogue.Moment3_2_6.normalize_18]
    exact RawMomentCatalogue.Moment3_2_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_3.denominator18)) RawMomentCatalogue.Moment3_0_3.raw18)=kernelRPoly 3 3 0
    rw [RawMomentCatalogue.Moment3_0_3.normalize_18]
    exact RawMomentCatalogue.Moment3_0_3.identity.trans (kernelRPoly_transpose 3 0 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_3.denominator18)) RawMomentCatalogue.Moment3_1_3.raw18)=kernelRPoly 3 3 1
    rw [RawMomentCatalogue.Moment3_1_3.normalize_18]
    exact RawMomentCatalogue.Moment3_1_3.identity.trans (kernelRPoly_transpose 3 1 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_3.denominator18)) RawMomentCatalogue.Moment3_2_3.raw18)=kernelRPoly 3 3 2
    rw [RawMomentCatalogue.Moment3_2_3.normalize_18]
    exact RawMomentCatalogue.Moment3_2_3.identity.trans (kernelRPoly_transpose 3 2 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_3.denominator18)) RawMomentCatalogue.Moment3_3_3.raw18)=kernelRPoly 3 3 3
    rw [RawMomentCatalogue.Moment3_3_3.normalize_18]
    exact RawMomentCatalogue.Moment3_3_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_4.denominator18)) RawMomentCatalogue.Moment3_3_4.raw18)=kernelRPoly 3 3 4
    rw [RawMomentCatalogue.Moment3_3_4.normalize_18]
    exact RawMomentCatalogue.Moment3_3_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_5.denominator18)) RawMomentCatalogue.Moment3_3_5.raw18)=kernelRPoly 3 3 5
    rw [RawMomentCatalogue.Moment3_3_5.normalize_18]
    exact RawMomentCatalogue.Moment3_3_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_6.denominator18)) RawMomentCatalogue.Moment3_3_6.raw18)=kernelRPoly 3 3 6
    rw [RawMomentCatalogue.Moment3_3_6.normalize_18]
    exact RawMomentCatalogue.Moment3_3_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_4.denominator18)) RawMomentCatalogue.Moment3_0_4.raw18)=kernelRPoly 3 4 0
    rw [RawMomentCatalogue.Moment3_0_4.normalize_18]
    exact RawMomentCatalogue.Moment3_0_4.identity.trans (kernelRPoly_transpose 3 0 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_4.denominator18)) RawMomentCatalogue.Moment3_1_4.raw18)=kernelRPoly 3 4 1
    rw [RawMomentCatalogue.Moment3_1_4.normalize_18]
    exact RawMomentCatalogue.Moment3_1_4.identity.trans (kernelRPoly_transpose 3 1 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_4.denominator18)) RawMomentCatalogue.Moment3_2_4.raw18)=kernelRPoly 3 4 2
    rw [RawMomentCatalogue.Moment3_2_4.normalize_18]
    exact RawMomentCatalogue.Moment3_2_4.identity.trans (kernelRPoly_transpose 3 2 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_4.denominator18)) RawMomentCatalogue.Moment3_3_4.raw18)=kernelRPoly 3 4 3
    rw [RawMomentCatalogue.Moment3_3_4.normalize_18]
    exact RawMomentCatalogue.Moment3_3_4.identity.trans (kernelRPoly_transpose 3 3 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_4_4.denominator18)) RawMomentCatalogue.Moment3_4_4.raw18)=kernelRPoly 3 4 4
    rw [RawMomentCatalogue.Moment3_4_4.normalize_18]
    exact RawMomentCatalogue.Moment3_4_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_4_5.denominator18)) RawMomentCatalogue.Moment3_4_5.raw18)=kernelRPoly 3 4 5
    rw [RawMomentCatalogue.Moment3_4_5.normalize_18]
    exact RawMomentCatalogue.Moment3_4_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_4_6.denominator18)) RawMomentCatalogue.Moment3_4_6.raw18)=kernelRPoly 3 4 6
    rw [RawMomentCatalogue.Moment3_4_6.normalize_18]
    exact RawMomentCatalogue.Moment3_4_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_5.denominator18)) RawMomentCatalogue.Moment3_0_5.raw18)=kernelRPoly 3 5 0
    rw [RawMomentCatalogue.Moment3_0_5.normalize_18]
    exact RawMomentCatalogue.Moment3_0_5.identity.trans (kernelRPoly_transpose 3 0 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_5.denominator18)) RawMomentCatalogue.Moment3_1_5.raw18)=kernelRPoly 3 5 1
    rw [RawMomentCatalogue.Moment3_1_5.normalize_18]
    exact RawMomentCatalogue.Moment3_1_5.identity.trans (kernelRPoly_transpose 3 1 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_5.denominator18)) RawMomentCatalogue.Moment3_2_5.raw18)=kernelRPoly 3 5 2
    rw [RawMomentCatalogue.Moment3_2_5.normalize_18]
    exact RawMomentCatalogue.Moment3_2_5.identity.trans (kernelRPoly_transpose 3 2 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_5.denominator18)) RawMomentCatalogue.Moment3_3_5.raw18)=kernelRPoly 3 5 3
    rw [RawMomentCatalogue.Moment3_3_5.normalize_18]
    exact RawMomentCatalogue.Moment3_3_5.identity.trans (kernelRPoly_transpose 3 3 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_4_5.denominator18)) RawMomentCatalogue.Moment3_4_5.raw18)=kernelRPoly 3 5 4
    rw [RawMomentCatalogue.Moment3_4_5.normalize_18]
    exact RawMomentCatalogue.Moment3_4_5.identity.trans (kernelRPoly_transpose 3 4 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_5_5.denominator18)) RawMomentCatalogue.Moment3_5_5.raw18)=kernelRPoly 3 5 5
    rw [RawMomentCatalogue.Moment3_5_5.normalize_18]
    exact RawMomentCatalogue.Moment3_5_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_5_6.denominator18)) RawMomentCatalogue.Moment3_5_6.raw18)=kernelRPoly 3 5 6
    rw [RawMomentCatalogue.Moment3_5_6.normalize_18]
    exact RawMomentCatalogue.Moment3_5_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_0_6.denominator18)) RawMomentCatalogue.Moment3_0_6.raw18)=kernelRPoly 3 6 0
    rw [RawMomentCatalogue.Moment3_0_6.normalize_18]
    exact RawMomentCatalogue.Moment3_0_6.identity.trans (kernelRPoly_transpose 3 0 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_1_6.denominator18)) RawMomentCatalogue.Moment3_1_6.raw18)=kernelRPoly 3 6 1
    rw [RawMomentCatalogue.Moment3_1_6.normalize_18]
    exact RawMomentCatalogue.Moment3_1_6.identity.trans (kernelRPoly_transpose 3 1 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_2_6.denominator18)) RawMomentCatalogue.Moment3_2_6.raw18)=kernelRPoly 3 6 2
    rw [RawMomentCatalogue.Moment3_2_6.normalize_18]
    exact RawMomentCatalogue.Moment3_2_6.identity.trans (kernelRPoly_transpose 3 2 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_3_6.denominator18)) RawMomentCatalogue.Moment3_3_6.raw18)=kernelRPoly 3 6 3
    rw [RawMomentCatalogue.Moment3_3_6.normalize_18]
    exact RawMomentCatalogue.Moment3_3_6.identity.trans (kernelRPoly_transpose 3 3 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_4_6.denominator18)) RawMomentCatalogue.Moment3_4_6.raw18)=kernelRPoly 3 6 4
    rw [RawMomentCatalogue.Moment3_4_6.normalize_18]
    exact RawMomentCatalogue.Moment3_4_6.identity.trans (kernelRPoly_transpose 3 4 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_5_6.denominator18)) RawMomentCatalogue.Moment3_5_6.raw18)=kernelRPoly 3 6 5
    rw [RawMomentCatalogue.Moment3_5_6.normalize_18]
    exact RawMomentCatalogue.Moment3_5_6.identity.trans (kernelRPoly_transpose 3 5 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment3_6_6.denominator18)) RawMomentCatalogue.Moment3_6_6.raw18)=kernelRPoly 3 6 6
    rw [RawMomentCatalogue.Moment3_6_6.normalize_18]
    exact RawMomentCatalogue.Moment3_6_6.identity
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawMomentTensors.D18_F3
