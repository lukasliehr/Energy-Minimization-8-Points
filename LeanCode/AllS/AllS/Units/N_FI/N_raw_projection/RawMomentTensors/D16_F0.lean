import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_0
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_0_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_1
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_1_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_2
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_2_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_3_3
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_3_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_3_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_3_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_3_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_3_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_4_4
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_4_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_4_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_4_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_4_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_5_5
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_5_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_5_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_5_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_6_6
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_6_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_6_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_7_7
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_7_8
import AllS.Units.N_FI.N_raw_projection.RawMomentCatalogue.Moment0_8_8
import AllS.Units.N_FI.N_gram_map.N_physical_entries
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
noncomputable section
namespace Blueprint.Thomson.Finite.RawMomentTensors.D16_F0
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def denominator : ℕ := RawMomentCatalogue.Moment0_0_0.denominator16
def source : Matrix (Fin 9) (Fin 9) (List (Tag × ℤ)) := ![![RawMomentCatalogue.Moment0_0_0.raw16,RawMomentCatalogue.Moment0_0_1.raw16,RawMomentCatalogue.Moment0_0_2.raw16,RawMomentCatalogue.Moment0_0_3.raw16,RawMomentCatalogue.Moment0_0_4.raw16,RawMomentCatalogue.Moment0_0_5.raw16,RawMomentCatalogue.Moment0_0_6.raw16,RawMomentCatalogue.Moment0_0_7.raw16,RawMomentCatalogue.Moment0_0_8.raw16],![RawMomentCatalogue.Moment0_0_1.raw16,RawMomentCatalogue.Moment0_1_1.raw16,RawMomentCatalogue.Moment0_1_2.raw16,RawMomentCatalogue.Moment0_1_3.raw16,RawMomentCatalogue.Moment0_1_4.raw16,RawMomentCatalogue.Moment0_1_5.raw16,RawMomentCatalogue.Moment0_1_6.raw16,RawMomentCatalogue.Moment0_1_7.raw16,RawMomentCatalogue.Moment0_1_8.raw16],![RawMomentCatalogue.Moment0_0_2.raw16,RawMomentCatalogue.Moment0_1_2.raw16,RawMomentCatalogue.Moment0_2_2.raw16,RawMomentCatalogue.Moment0_2_3.raw16,RawMomentCatalogue.Moment0_2_4.raw16,RawMomentCatalogue.Moment0_2_5.raw16,RawMomentCatalogue.Moment0_2_6.raw16,RawMomentCatalogue.Moment0_2_7.raw16,RawMomentCatalogue.Moment0_2_8.raw16],![RawMomentCatalogue.Moment0_0_3.raw16,RawMomentCatalogue.Moment0_1_3.raw16,RawMomentCatalogue.Moment0_2_3.raw16,RawMomentCatalogue.Moment0_3_3.raw16,RawMomentCatalogue.Moment0_3_4.raw16,RawMomentCatalogue.Moment0_3_5.raw16,RawMomentCatalogue.Moment0_3_6.raw16,RawMomentCatalogue.Moment0_3_7.raw16,RawMomentCatalogue.Moment0_3_8.raw16],![RawMomentCatalogue.Moment0_0_4.raw16,RawMomentCatalogue.Moment0_1_4.raw16,RawMomentCatalogue.Moment0_2_4.raw16,RawMomentCatalogue.Moment0_3_4.raw16,RawMomentCatalogue.Moment0_4_4.raw16,RawMomentCatalogue.Moment0_4_5.raw16,RawMomentCatalogue.Moment0_4_6.raw16,RawMomentCatalogue.Moment0_4_7.raw16,RawMomentCatalogue.Moment0_4_8.raw16],![RawMomentCatalogue.Moment0_0_5.raw16,RawMomentCatalogue.Moment0_1_5.raw16,RawMomentCatalogue.Moment0_2_5.raw16,RawMomentCatalogue.Moment0_3_5.raw16,RawMomentCatalogue.Moment0_4_5.raw16,RawMomentCatalogue.Moment0_5_5.raw16,RawMomentCatalogue.Moment0_5_6.raw16,RawMomentCatalogue.Moment0_5_7.raw16,RawMomentCatalogue.Moment0_5_8.raw16],![RawMomentCatalogue.Moment0_0_6.raw16,RawMomentCatalogue.Moment0_1_6.raw16,RawMomentCatalogue.Moment0_2_6.raw16,RawMomentCatalogue.Moment0_3_6.raw16,RawMomentCatalogue.Moment0_4_6.raw16,RawMomentCatalogue.Moment0_5_6.raw16,RawMomentCatalogue.Moment0_6_6.raw16,RawMomentCatalogue.Moment0_6_7.raw16,RawMomentCatalogue.Moment0_6_8.raw16],![RawMomentCatalogue.Moment0_0_7.raw16,RawMomentCatalogue.Moment0_1_7.raw16,RawMomentCatalogue.Moment0_2_7.raw16,RawMomentCatalogue.Moment0_3_7.raw16,RawMomentCatalogue.Moment0_4_7.raw16,RawMomentCatalogue.Moment0_5_7.raw16,RawMomentCatalogue.Moment0_6_7.raw16,RawMomentCatalogue.Moment0_7_7.raw16,RawMomentCatalogue.Moment0_7_8.raw16],![RawMomentCatalogue.Moment0_0_8.raw16,RawMomentCatalogue.Moment0_1_8.raw16,RawMomentCatalogue.Moment0_2_8.raw16,RawMomentCatalogue.Moment0_3_8.raw16,RawMomentCatalogue.Moment0_4_8.raw16,RawMomentCatalogue.Moment0_5_8.raw16,RawMomentCatalogue.Moment0_6_8.raw16,RawMomentCatalogue.Moment0_7_8.raw16,RawMomentCatalogue.Moment0_8_8.raw16]]
def coordinatePolynomial (i j : Fin 9) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry denominator (source i j)))
theorem denominator_positive : 0<denominator := by decide
theorem subst_coordinatePolynomial (i j : Fin 9) :
    invariantSubst (coordinatePolynomial i j)=kernelRPoly 0 i.val j.val := by
  fin_cases i <;> fin_cases j
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_0.denominator16)) RawMomentCatalogue.Moment0_0_0.raw16)=kernelRPoly 0 0 0
    rw [RawMomentCatalogue.Moment0_0_0.normalize_16]
    exact RawMomentCatalogue.Moment0_0_0.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_1.denominator16)) RawMomentCatalogue.Moment0_0_1.raw16)=kernelRPoly 0 0 1
    rw [RawMomentCatalogue.Moment0_0_1.normalize_16]
    exact RawMomentCatalogue.Moment0_0_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_2.denominator16)) RawMomentCatalogue.Moment0_0_2.raw16)=kernelRPoly 0 0 2
    rw [RawMomentCatalogue.Moment0_0_2.normalize_16]
    exact RawMomentCatalogue.Moment0_0_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_3.denominator16)) RawMomentCatalogue.Moment0_0_3.raw16)=kernelRPoly 0 0 3
    rw [RawMomentCatalogue.Moment0_0_3.normalize_16]
    exact RawMomentCatalogue.Moment0_0_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_4.denominator16)) RawMomentCatalogue.Moment0_0_4.raw16)=kernelRPoly 0 0 4
    rw [RawMomentCatalogue.Moment0_0_4.normalize_16]
    exact RawMomentCatalogue.Moment0_0_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_5.denominator16)) RawMomentCatalogue.Moment0_0_5.raw16)=kernelRPoly 0 0 5
    rw [RawMomentCatalogue.Moment0_0_5.normalize_16]
    exact RawMomentCatalogue.Moment0_0_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_6.denominator16)) RawMomentCatalogue.Moment0_0_6.raw16)=kernelRPoly 0 0 6
    rw [RawMomentCatalogue.Moment0_0_6.normalize_16]
    exact RawMomentCatalogue.Moment0_0_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_7.denominator16)) RawMomentCatalogue.Moment0_0_7.raw16)=kernelRPoly 0 0 7
    rw [RawMomentCatalogue.Moment0_0_7.normalize_16]
    exact RawMomentCatalogue.Moment0_0_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_8.denominator16)) RawMomentCatalogue.Moment0_0_8.raw16)=kernelRPoly 0 0 8
    rw [RawMomentCatalogue.Moment0_0_8.normalize_16]
    exact RawMomentCatalogue.Moment0_0_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_1.denominator16)) RawMomentCatalogue.Moment0_0_1.raw16)=kernelRPoly 0 1 0
    rw [RawMomentCatalogue.Moment0_0_1.normalize_16]
    exact RawMomentCatalogue.Moment0_0_1.identity.trans (kernelRPoly_transpose 0 0 1)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_1.denominator16)) RawMomentCatalogue.Moment0_1_1.raw16)=kernelRPoly 0 1 1
    rw [RawMomentCatalogue.Moment0_1_1.normalize_16]
    exact RawMomentCatalogue.Moment0_1_1.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_2.denominator16)) RawMomentCatalogue.Moment0_1_2.raw16)=kernelRPoly 0 1 2
    rw [RawMomentCatalogue.Moment0_1_2.normalize_16]
    exact RawMomentCatalogue.Moment0_1_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_3.denominator16)) RawMomentCatalogue.Moment0_1_3.raw16)=kernelRPoly 0 1 3
    rw [RawMomentCatalogue.Moment0_1_3.normalize_16]
    exact RawMomentCatalogue.Moment0_1_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_4.denominator16)) RawMomentCatalogue.Moment0_1_4.raw16)=kernelRPoly 0 1 4
    rw [RawMomentCatalogue.Moment0_1_4.normalize_16]
    exact RawMomentCatalogue.Moment0_1_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_5.denominator16)) RawMomentCatalogue.Moment0_1_5.raw16)=kernelRPoly 0 1 5
    rw [RawMomentCatalogue.Moment0_1_5.normalize_16]
    exact RawMomentCatalogue.Moment0_1_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_6.denominator16)) RawMomentCatalogue.Moment0_1_6.raw16)=kernelRPoly 0 1 6
    rw [RawMomentCatalogue.Moment0_1_6.normalize_16]
    exact RawMomentCatalogue.Moment0_1_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_7.denominator16)) RawMomentCatalogue.Moment0_1_7.raw16)=kernelRPoly 0 1 7
    rw [RawMomentCatalogue.Moment0_1_7.normalize_16]
    exact RawMomentCatalogue.Moment0_1_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_8.denominator16)) RawMomentCatalogue.Moment0_1_8.raw16)=kernelRPoly 0 1 8
    rw [RawMomentCatalogue.Moment0_1_8.normalize_16]
    exact RawMomentCatalogue.Moment0_1_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_2.denominator16)) RawMomentCatalogue.Moment0_0_2.raw16)=kernelRPoly 0 2 0
    rw [RawMomentCatalogue.Moment0_0_2.normalize_16]
    exact RawMomentCatalogue.Moment0_0_2.identity.trans (kernelRPoly_transpose 0 0 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_2.denominator16)) RawMomentCatalogue.Moment0_1_2.raw16)=kernelRPoly 0 2 1
    rw [RawMomentCatalogue.Moment0_1_2.normalize_16]
    exact RawMomentCatalogue.Moment0_1_2.identity.trans (kernelRPoly_transpose 0 1 2)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_2.denominator16)) RawMomentCatalogue.Moment0_2_2.raw16)=kernelRPoly 0 2 2
    rw [RawMomentCatalogue.Moment0_2_2.normalize_16]
    exact RawMomentCatalogue.Moment0_2_2.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_3.denominator16)) RawMomentCatalogue.Moment0_2_3.raw16)=kernelRPoly 0 2 3
    rw [RawMomentCatalogue.Moment0_2_3.normalize_16]
    exact RawMomentCatalogue.Moment0_2_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_4.denominator16)) RawMomentCatalogue.Moment0_2_4.raw16)=kernelRPoly 0 2 4
    rw [RawMomentCatalogue.Moment0_2_4.normalize_16]
    exact RawMomentCatalogue.Moment0_2_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_5.denominator16)) RawMomentCatalogue.Moment0_2_5.raw16)=kernelRPoly 0 2 5
    rw [RawMomentCatalogue.Moment0_2_5.normalize_16]
    exact RawMomentCatalogue.Moment0_2_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_6.denominator16)) RawMomentCatalogue.Moment0_2_6.raw16)=kernelRPoly 0 2 6
    rw [RawMomentCatalogue.Moment0_2_6.normalize_16]
    exact RawMomentCatalogue.Moment0_2_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_7.denominator16)) RawMomentCatalogue.Moment0_2_7.raw16)=kernelRPoly 0 2 7
    rw [RawMomentCatalogue.Moment0_2_7.normalize_16]
    exact RawMomentCatalogue.Moment0_2_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_8.denominator16)) RawMomentCatalogue.Moment0_2_8.raw16)=kernelRPoly 0 2 8
    rw [RawMomentCatalogue.Moment0_2_8.normalize_16]
    exact RawMomentCatalogue.Moment0_2_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_3.denominator16)) RawMomentCatalogue.Moment0_0_3.raw16)=kernelRPoly 0 3 0
    rw [RawMomentCatalogue.Moment0_0_3.normalize_16]
    exact RawMomentCatalogue.Moment0_0_3.identity.trans (kernelRPoly_transpose 0 0 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_3.denominator16)) RawMomentCatalogue.Moment0_1_3.raw16)=kernelRPoly 0 3 1
    rw [RawMomentCatalogue.Moment0_1_3.normalize_16]
    exact RawMomentCatalogue.Moment0_1_3.identity.trans (kernelRPoly_transpose 0 1 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_3.denominator16)) RawMomentCatalogue.Moment0_2_3.raw16)=kernelRPoly 0 3 2
    rw [RawMomentCatalogue.Moment0_2_3.normalize_16]
    exact RawMomentCatalogue.Moment0_2_3.identity.trans (kernelRPoly_transpose 0 2 3)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_3.denominator16)) RawMomentCatalogue.Moment0_3_3.raw16)=kernelRPoly 0 3 3
    rw [RawMomentCatalogue.Moment0_3_3.normalize_16]
    exact RawMomentCatalogue.Moment0_3_3.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_4.denominator16)) RawMomentCatalogue.Moment0_3_4.raw16)=kernelRPoly 0 3 4
    rw [RawMomentCatalogue.Moment0_3_4.normalize_16]
    exact RawMomentCatalogue.Moment0_3_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_5.denominator16)) RawMomentCatalogue.Moment0_3_5.raw16)=kernelRPoly 0 3 5
    rw [RawMomentCatalogue.Moment0_3_5.normalize_16]
    exact RawMomentCatalogue.Moment0_3_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_6.denominator16)) RawMomentCatalogue.Moment0_3_6.raw16)=kernelRPoly 0 3 6
    rw [RawMomentCatalogue.Moment0_3_6.normalize_16]
    exact RawMomentCatalogue.Moment0_3_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_7.denominator16)) RawMomentCatalogue.Moment0_3_7.raw16)=kernelRPoly 0 3 7
    rw [RawMomentCatalogue.Moment0_3_7.normalize_16]
    exact RawMomentCatalogue.Moment0_3_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_8.denominator16)) RawMomentCatalogue.Moment0_3_8.raw16)=kernelRPoly 0 3 8
    rw [RawMomentCatalogue.Moment0_3_8.normalize_16]
    exact RawMomentCatalogue.Moment0_3_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_4.denominator16)) RawMomentCatalogue.Moment0_0_4.raw16)=kernelRPoly 0 4 0
    rw [RawMomentCatalogue.Moment0_0_4.normalize_16]
    exact RawMomentCatalogue.Moment0_0_4.identity.trans (kernelRPoly_transpose 0 0 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_4.denominator16)) RawMomentCatalogue.Moment0_1_4.raw16)=kernelRPoly 0 4 1
    rw [RawMomentCatalogue.Moment0_1_4.normalize_16]
    exact RawMomentCatalogue.Moment0_1_4.identity.trans (kernelRPoly_transpose 0 1 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_4.denominator16)) RawMomentCatalogue.Moment0_2_4.raw16)=kernelRPoly 0 4 2
    rw [RawMomentCatalogue.Moment0_2_4.normalize_16]
    exact RawMomentCatalogue.Moment0_2_4.identity.trans (kernelRPoly_transpose 0 2 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_4.denominator16)) RawMomentCatalogue.Moment0_3_4.raw16)=kernelRPoly 0 4 3
    rw [RawMomentCatalogue.Moment0_3_4.normalize_16]
    exact RawMomentCatalogue.Moment0_3_4.identity.trans (kernelRPoly_transpose 0 3 4)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_4.denominator16)) RawMomentCatalogue.Moment0_4_4.raw16)=kernelRPoly 0 4 4
    rw [RawMomentCatalogue.Moment0_4_4.normalize_16]
    exact RawMomentCatalogue.Moment0_4_4.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_5.denominator16)) RawMomentCatalogue.Moment0_4_5.raw16)=kernelRPoly 0 4 5
    rw [RawMomentCatalogue.Moment0_4_5.normalize_16]
    exact RawMomentCatalogue.Moment0_4_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_6.denominator16)) RawMomentCatalogue.Moment0_4_6.raw16)=kernelRPoly 0 4 6
    rw [RawMomentCatalogue.Moment0_4_6.normalize_16]
    exact RawMomentCatalogue.Moment0_4_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_7.denominator16)) RawMomentCatalogue.Moment0_4_7.raw16)=kernelRPoly 0 4 7
    rw [RawMomentCatalogue.Moment0_4_7.normalize_16]
    exact RawMomentCatalogue.Moment0_4_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_8.denominator16)) RawMomentCatalogue.Moment0_4_8.raw16)=kernelRPoly 0 4 8
    rw [RawMomentCatalogue.Moment0_4_8.normalize_16]
    exact RawMomentCatalogue.Moment0_4_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_5.denominator16)) RawMomentCatalogue.Moment0_0_5.raw16)=kernelRPoly 0 5 0
    rw [RawMomentCatalogue.Moment0_0_5.normalize_16]
    exact RawMomentCatalogue.Moment0_0_5.identity.trans (kernelRPoly_transpose 0 0 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_5.denominator16)) RawMomentCatalogue.Moment0_1_5.raw16)=kernelRPoly 0 5 1
    rw [RawMomentCatalogue.Moment0_1_5.normalize_16]
    exact RawMomentCatalogue.Moment0_1_5.identity.trans (kernelRPoly_transpose 0 1 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_5.denominator16)) RawMomentCatalogue.Moment0_2_5.raw16)=kernelRPoly 0 5 2
    rw [RawMomentCatalogue.Moment0_2_5.normalize_16]
    exact RawMomentCatalogue.Moment0_2_5.identity.trans (kernelRPoly_transpose 0 2 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_5.denominator16)) RawMomentCatalogue.Moment0_3_5.raw16)=kernelRPoly 0 5 3
    rw [RawMomentCatalogue.Moment0_3_5.normalize_16]
    exact RawMomentCatalogue.Moment0_3_5.identity.trans (kernelRPoly_transpose 0 3 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_5.denominator16)) RawMomentCatalogue.Moment0_4_5.raw16)=kernelRPoly 0 5 4
    rw [RawMomentCatalogue.Moment0_4_5.normalize_16]
    exact RawMomentCatalogue.Moment0_4_5.identity.trans (kernelRPoly_transpose 0 4 5)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_5.denominator16)) RawMomentCatalogue.Moment0_5_5.raw16)=kernelRPoly 0 5 5
    rw [RawMomentCatalogue.Moment0_5_5.normalize_16]
    exact RawMomentCatalogue.Moment0_5_5.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_6.denominator16)) RawMomentCatalogue.Moment0_5_6.raw16)=kernelRPoly 0 5 6
    rw [RawMomentCatalogue.Moment0_5_6.normalize_16]
    exact RawMomentCatalogue.Moment0_5_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_7.denominator16)) RawMomentCatalogue.Moment0_5_7.raw16)=kernelRPoly 0 5 7
    rw [RawMomentCatalogue.Moment0_5_7.normalize_16]
    exact RawMomentCatalogue.Moment0_5_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_8.denominator16)) RawMomentCatalogue.Moment0_5_8.raw16)=kernelRPoly 0 5 8
    rw [RawMomentCatalogue.Moment0_5_8.normalize_16]
    exact RawMomentCatalogue.Moment0_5_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_6.denominator16)) RawMomentCatalogue.Moment0_0_6.raw16)=kernelRPoly 0 6 0
    rw [RawMomentCatalogue.Moment0_0_6.normalize_16]
    exact RawMomentCatalogue.Moment0_0_6.identity.trans (kernelRPoly_transpose 0 0 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_6.denominator16)) RawMomentCatalogue.Moment0_1_6.raw16)=kernelRPoly 0 6 1
    rw [RawMomentCatalogue.Moment0_1_6.normalize_16]
    exact RawMomentCatalogue.Moment0_1_6.identity.trans (kernelRPoly_transpose 0 1 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_6.denominator16)) RawMomentCatalogue.Moment0_2_6.raw16)=kernelRPoly 0 6 2
    rw [RawMomentCatalogue.Moment0_2_6.normalize_16]
    exact RawMomentCatalogue.Moment0_2_6.identity.trans (kernelRPoly_transpose 0 2 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_6.denominator16)) RawMomentCatalogue.Moment0_3_6.raw16)=kernelRPoly 0 6 3
    rw [RawMomentCatalogue.Moment0_3_6.normalize_16]
    exact RawMomentCatalogue.Moment0_3_6.identity.trans (kernelRPoly_transpose 0 3 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_6.denominator16)) RawMomentCatalogue.Moment0_4_6.raw16)=kernelRPoly 0 6 4
    rw [RawMomentCatalogue.Moment0_4_6.normalize_16]
    exact RawMomentCatalogue.Moment0_4_6.identity.trans (kernelRPoly_transpose 0 4 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_6.denominator16)) RawMomentCatalogue.Moment0_5_6.raw16)=kernelRPoly 0 6 5
    rw [RawMomentCatalogue.Moment0_5_6.normalize_16]
    exact RawMomentCatalogue.Moment0_5_6.identity.trans (kernelRPoly_transpose 0 5 6)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_6_6.denominator16)) RawMomentCatalogue.Moment0_6_6.raw16)=kernelRPoly 0 6 6
    rw [RawMomentCatalogue.Moment0_6_6.normalize_16]
    exact RawMomentCatalogue.Moment0_6_6.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_6_7.denominator16)) RawMomentCatalogue.Moment0_6_7.raw16)=kernelRPoly 0 6 7
    rw [RawMomentCatalogue.Moment0_6_7.normalize_16]
    exact RawMomentCatalogue.Moment0_6_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_6_8.denominator16)) RawMomentCatalogue.Moment0_6_8.raw16)=kernelRPoly 0 6 8
    rw [RawMomentCatalogue.Moment0_6_8.normalize_16]
    exact RawMomentCatalogue.Moment0_6_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_7.denominator16)) RawMomentCatalogue.Moment0_0_7.raw16)=kernelRPoly 0 7 0
    rw [RawMomentCatalogue.Moment0_0_7.normalize_16]
    exact RawMomentCatalogue.Moment0_0_7.identity.trans (kernelRPoly_transpose 0 0 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_7.denominator16)) RawMomentCatalogue.Moment0_1_7.raw16)=kernelRPoly 0 7 1
    rw [RawMomentCatalogue.Moment0_1_7.normalize_16]
    exact RawMomentCatalogue.Moment0_1_7.identity.trans (kernelRPoly_transpose 0 1 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_7.denominator16)) RawMomentCatalogue.Moment0_2_7.raw16)=kernelRPoly 0 7 2
    rw [RawMomentCatalogue.Moment0_2_7.normalize_16]
    exact RawMomentCatalogue.Moment0_2_7.identity.trans (kernelRPoly_transpose 0 2 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_7.denominator16)) RawMomentCatalogue.Moment0_3_7.raw16)=kernelRPoly 0 7 3
    rw [RawMomentCatalogue.Moment0_3_7.normalize_16]
    exact RawMomentCatalogue.Moment0_3_7.identity.trans (kernelRPoly_transpose 0 3 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_7.denominator16)) RawMomentCatalogue.Moment0_4_7.raw16)=kernelRPoly 0 7 4
    rw [RawMomentCatalogue.Moment0_4_7.normalize_16]
    exact RawMomentCatalogue.Moment0_4_7.identity.trans (kernelRPoly_transpose 0 4 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_7.denominator16)) RawMomentCatalogue.Moment0_5_7.raw16)=kernelRPoly 0 7 5
    rw [RawMomentCatalogue.Moment0_5_7.normalize_16]
    exact RawMomentCatalogue.Moment0_5_7.identity.trans (kernelRPoly_transpose 0 5 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_6_7.denominator16)) RawMomentCatalogue.Moment0_6_7.raw16)=kernelRPoly 0 7 6
    rw [RawMomentCatalogue.Moment0_6_7.normalize_16]
    exact RawMomentCatalogue.Moment0_6_7.identity.trans (kernelRPoly_transpose 0 6 7)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_7_7.denominator16)) RawMomentCatalogue.Moment0_7_7.raw16)=kernelRPoly 0 7 7
    rw [RawMomentCatalogue.Moment0_7_7.normalize_16]
    exact RawMomentCatalogue.Moment0_7_7.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_7_8.denominator16)) RawMomentCatalogue.Moment0_7_8.raw16)=kernelRPoly 0 7 8
    rw [RawMomentCatalogue.Moment0_7_8.normalize_16]
    exact RawMomentCatalogue.Moment0_7_8.identity
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_0_8.denominator16)) RawMomentCatalogue.Moment0_0_8.raw16)=kernelRPoly 0 8 0
    rw [RawMomentCatalogue.Moment0_0_8.normalize_16]
    exact RawMomentCatalogue.Moment0_0_8.identity.trans (kernelRPoly_transpose 0 0 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_1_8.denominator16)) RawMomentCatalogue.Moment0_1_8.raw16)=kernelRPoly 0 8 1
    rw [RawMomentCatalogue.Moment0_1_8.normalize_16]
    exact RawMomentCatalogue.Moment0_1_8.identity.trans (kernelRPoly_transpose 0 1 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_2_8.denominator16)) RawMomentCatalogue.Moment0_2_8.raw16)=kernelRPoly 0 8 2
    rw [RawMomentCatalogue.Moment0_2_8.normalize_16]
    exact RawMomentCatalogue.Moment0_2_8.identity.trans (kernelRPoly_transpose 0 2 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_3_8.denominator16)) RawMomentCatalogue.Moment0_3_8.raw16)=kernelRPoly 0 8 3
    rw [RawMomentCatalogue.Moment0_3_8.normalize_16]
    exact RawMomentCatalogue.Moment0_3_8.identity.trans (kernelRPoly_transpose 0 3 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_4_8.denominator16)) RawMomentCatalogue.Moment0_4_8.raw16)=kernelRPoly 0 8 4
    rw [RawMomentCatalogue.Moment0_4_8.normalize_16]
    exact RawMomentCatalogue.Moment0_4_8.identity.trans (kernelRPoly_transpose 0 4 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_5_8.denominator16)) RawMomentCatalogue.Moment0_5_8.raw16)=kernelRPoly 0 8 5
    rw [RawMomentCatalogue.Moment0_5_8.normalize_16]
    exact RawMomentCatalogue.Moment0_5_8.identity.trans (kernelRPoly_transpose 0 5 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_6_8.denominator16)) RawMomentCatalogue.Moment0_6_8.raw16)=kernelRPoly 0 8 6
    rw [RawMomentCatalogue.Moment0_6_8.normalize_16]
    exact RawMomentCatalogue.Moment0_6_8.identity.trans (kernelRPoly_transpose 0 6 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_7_8.denominator16)) RawMomentCatalogue.Moment0_7_8.raw16)=kernelRPoly 0 8 7
    rw [RawMomentCatalogue.Moment0_7_8.normalize_16]
    exact RawMomentCatalogue.Moment0_7_8.identity.trans (kernelRPoly_transpose 0 7 8)
  · change sparseInvariantPolynomial (List.map (fun x => (x.1,(x.2:ℚ)/RawMomentCatalogue.Moment0_8_8.denominator16)) RawMomentCatalogue.Moment0_8_8.raw16)=kernelRPoly 0 8 8
    rw [RawMomentCatalogue.Moment0_8_8.normalize_16]
    exact RawMomentCatalogue.Moment0_8_8.identity
#print axioms subst_coordinatePolynomial
end Blueprint.Thomson.Finite.RawMomentTensors.D16_F0
