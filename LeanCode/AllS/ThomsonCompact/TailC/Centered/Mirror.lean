import ThomsonCompact.TailC.Centered.Defs
import ThomsonCompact.TailC.StageReal
import AllS.Units.N_GI.N_centered_quadratic.N_synthesis_helpers
import AllS.Units.N_GI.N_centered_quadratic.N_projected_identity

/-!
# TailC.Centered: the integer mirror evaluates to the real Gram (workstream TC1)

`ι : AZ → ℝ`, `(u, v) ↦ κ u + κ v · packingZHeight`. Primitive mirrors (`fin_cases` over ≤ 8 values), the generic
bilinear lemma `ι_gZ7` (for any coordinates), and `ι_gramZ : ι (gramZ j k) = 17210368 · centeredContactRawGram …`.
-/

namespace ThomsonCompact.TailC.Centered
open ThomsonCompact.TailC Finset
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

/-! ## Evaluation -/

noncomputable def ι (x : AZ) : ℝ := κ x.1 + κ x.2 * packingZHeight

theorem hH2 : packingZHeight ^ 2 = packingHeight := packing_parameters.2.2.1
theorem hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem κ_mk (a b : ℤ) : κ ⟨a, b⟩ = a + b * Real.sqrt 2 := by rw [κ_apply]

theorem κ2 : κ 2 = 2 := by simpa using (map_ofNat κ 2)
theorem κ4 : κ 4 = 4 := by simpa using (map_ofNat κ 4)
theorem κ7 : κ 7 = 7 := by simpa using (map_ofNat κ 7)
theorem κ8 : κ 8 = 8 := by simpa using (map_ofNat κ 8)
theorem κ14 : κ 14 = 14 := by simpa using (map_ofNat κ 14)

theorem hs2' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem ι_add (x y : AZ) : ι (x + y) = ι x + ι y := by
  simp only [ι, Prod.fst_add, Prod.snd_add, map_add]; ring
theorem ι_sub (x y : AZ) : ι (x - y) = ι x - ι y := by
  simp only [ι, Prod.fst_sub, Prod.snd_sub, map_sub]; ring
theorem ι_zero : ι 0 = 0 := by simp [ι]
theorem ι_zs (z : ℤ√2) (x : AZ) : ι (zs z x) = κ z * ι x := by
  simp only [ι, zs, map_mul]; ring
theorem ι_em (z : ℤ√2) : ι (em z) = κ z := by simp [ι, em]
theorem ι_hZ1 : ι hZ1 = packingZHeight := by simp [ι, hZ1]
theorem κ_aZ : κ aZ = 7 * packingHeight := by
  rw [aZ, κ_mk, packingHeight]; push_cast; ring
theorem ι_mul7 (x y : AZ) : ι (mul7 x y) = 7 * ι x * ι y := by
  have h : κ ⟨-1, 2⟩ = 7 * packingZHeight ^ 2 := by rw [κ_mk, hH2, packingHeight]; push_cast; ring
  simp only [ι, mul7, map_add, map_mul, κ7, h]
  ring

/-- `ι` as an additive map. -/
noncomputable def ιH : AZ →+ ℝ where
  toFun := ι
  map_zero' := ι_zero
  map_add' := ι_add

theorem ι_sum {α : Type*} (s : Finset α) (f : α → AZ) : ι (∑ a ∈ s, f a) = ∑ a ∈ s, ι (f a) :=
  map_sum ιH f s

theorem κ_int (n : ℤ) : κ (n : ℤ√2) = n := map_intCast κ n
theorem κ_nat (n : ℕ) : κ ((OfNat.ofNat n : ℕ) : ℤ√2) = n := map_natCast κ n

/-! ## Primitive tables -/

theorem hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  field_simp; rw [hs2']

theorem κ_acZ (i : Fin 8) : κ (acZ i) = 2 * angularCos i := by
  fin_cases i <;> simp [acZ, angularCos, κ_mk, hinv] <;> ring
theorem κ_asZ (i : Fin 8) : κ (asZ i) = 2 * angularSin i := by
  fin_cases i <;> simp [asZ, angularSin, κ_mk, hinv] <;> ring
theorem κ_lsZ (i : Fin 8) : κ (lsZ i) = layerSign i := by
  fin_cases i <;> simp [lsZ, layerSign]
theorem κ_c2Z (i : Fin 8) : κ (c2Z i) = boundaryCos2 i := by
  fin_cases i <;> simp [c2Z, boundaryCos2]
theorem κ_s2Z (i : Fin 8) : κ (s2Z i) = boundarySin2 i := by
  fin_cases i <;> simp [s2Z, boundarySin2]

theorem κ_msrZ (j i : Fin 8) : κ (msrZ j i) = 2 * meanScalarRaw j i := by
  fin_cases j <;> simp [msrZ, meanScalarRaw, κ_acZ, κ_asZ, κ_lsZ, κ_c2Z, κ_s2Z, boundaryCos3, boundarySin3, κ2] <;> ring

theorem mtr_apply (j : Fin 8 × Fin 2) (i : Fin 8) (b : Fin 2) :
    (meanTangentRaw j) (i, b) = if b = j.2 then meanScalarRaw j.1 i else 0 := rfl

theorem κ_qZ (j : Fin 8 × Fin 2) (i : Fin 8) (b : Fin 2) : κ (qZ j i b) = 2 * (meanTangentRaw j) (i, b) := by
  rw [mtr_apply, qZ]; split_ifs <;> simp [κ_msrZ]

theorem ι_qA (j : Fin 8 × Fin 2) (i : Fin 8) (b : Fin 2) : ι (qA j i b) = 2 * (meanTangentRaw j) (i, b) := by
  rw [qA, ι_em, κ_qZ]

theorem κ_ccZ (b : Fin 2) : κ (ccZ b) = 2 * contactCosine b := by
  fin_cases b <;> simp [ccZ, contactCosine, κ_mk, hinv] <;> ring
theorem κ_csZ (b : Fin 2) : κ (csZ b) = 2 * contactSine b := by
  fin_cases b <;> simp [csZ, contactSine, κ_mk, hinv] <;> ring
theorem κ_cpZ (b : Fin 2) : κ (cpZ b) = contactParity b := by
  fin_cases b <;> simp [cpZ, contactParity]
theorem κ_dZ (b : Fin 2) :
    κ (dZ b) = 14 * (packingHeight * contactCosine b + (1 - packingHeight) * contactParity b) := by
  simp only [dZ, map_add, map_mul, map_sub, κ_aZ, κ_ccZ, κ_cpZ]
  have h14 : κ 14 = 14 := by simpa using (map_ofNat κ 14)
  have h2 : κ 2 = 2 := by simpa using (map_ofNat κ 2)
  rw [h14, h2]; ring

theorem cnext_eq (e : ContactIndex) : cnext e = contactNext e := rfl

/-! ## Contact components -/

theorem ι_fZ (e : ContactIndex) (j : Fin 8 × Fin 2) (c : Fin 4) :
    ι (fZ e j c) = 28 * contactMComponents e (meanTangentRaw j) c := by
  have h2 : κ 2 = 2 := by simpa using (map_ofNat κ 2)
  have h7 : κ 7 = 7 := by simpa using (map_ofNat κ 7)
  fin_cases c <;>
    simp only [fZ, contactMComponents, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, κ2, κ7,
      ι_add, ι_sub, ι_em, ι_zs, ι_hZ1, map_add, map_sub, map_mul, h2, h7, κ_aZ, κ_ccZ, κ_csZ, κ_dZ, κ_qZ, cnext_eq] <;>
    ring

/-! ## Rotations and the bilinear form -/

theorem rot_apply (r : Fin 3) (i : Fin 8) (b : Fin 2) :
    (boundaryRotation r) (i, b) = boundaryRawPair (boundaryRotationIndex r) i b := rfl

theorem ι_rotZ (r : Fin 2) (i : Fin 8) (b : Fin 2) :
    ι (rotZ r i b) = 2 * (boundaryRotation (Fin.castSucc r)) (i, b) := by
  rw [rot_apply]
  fin_cases r <;> fin_cases b <;>
    simp [rotZ, boundaryRawPair, boundaryRotationIndex, boundaryCos3, boundarySin3, ι_zs, ι_em, ι_hZ1,
      map_mul, map_neg, κ_lsZ, κ_acZ, κ_asZ] <;> ring

theorem ι_fdZ (X V : Fin 8 → Fin 2 → AZ) (x v : TangentCoordinates)
    (hX : ∀ i b, ι (X i b) = 2 * x (i, b)) (hV : ∀ i b, ι (V i b) = 2 * v (i, b)) (e : ContactIndex) :
    ι (fdZ X V e) = 392 * contactFrameDot x v e := by
  have h7 : κ 7 = 7 := by simpa using (map_ofNat κ 7)
  simp only [fdZ, contactFrameDot, ι_add, ι_sub, ι_zs, ι_mul7, ι_hZ1, map_mul, h7, κ_ccZ, κ_csZ, κ_dZ, hX, hV,
    cnext_eq]
  ring

theorem ι_gZ7 (X V : Fin 8 → Fin 2 → AZ) (x v : TangentCoordinates)
    (hX : ∀ i b, ι (X i b) = 2 * x (i, b)) (hV : ∀ i b, ι (V i b) = 2 * v (i, b)) (e : ContactIndex) :
    ι (gZ7 X V e) = 392 * contactMBilinear e x v := by
  have h2 : κ 2 = 2 := by simpa using (map_ofNat κ 2)
  simp only [gZ7, contactMBilinear, ι_add, ι_sub, ι_zs, ι_mul7, map_mul, h2, κ_aZ, hX, hV, cnext_eq,
    ι_fdZ X V x v hX hV e, ι_fdZ V X v x hV hX e]
  ring

/-- The third rotation `(R, 0)`: `contactMBilinear e rot₂ q = R β`. -/
noncomputable def beta (e : ContactIndex) (q : TangentCoordinates) : ℝ :=
  packingHeight * (q (e.1, 0) + q (contactNext e, 0)) - contactCosine e.2 * q (contactNext e, 0) +
    packingZHeight * contactSine e.2 * q (contactNext e, 1) - contactCosine e.2 * q (e.1, 0) -
    packingZHeight * contactSine e.2 * q (e.1, 1)

theorem bil_rot2 (e : ContactIndex) (q : TangentCoordinates) :
    contactMBilinear e (boundaryRotation 2) q = packingRadius * beta e q := by
  simp [contactMBilinear, contactFrameDot, rot_apply, boundaryRotationIndex, boundaryRawPair, beta] <;> ring

theorem ι_bZ (e : ContactIndex) (j : Fin 8 × Fin 2) : ι (bZ e j) = 56 * beta e (meanTangentRaw j) := by
  have h4 : κ 4 = 4 := by simpa using (map_ofNat κ 4)
  have h14 : κ 14 = 14 := by simpa using (map_ofNat κ 14)
  simp only [bZ, beta, ι_add, ι_sub, ι_em, ι_zs, ι_hZ1, map_add, map_sub, map_mul, h4, h14, κ_aZ, κ_ccZ, κ_csZ,
    κ_qZ, cnext_eq]
  ring

/-! ## Spectral data -/

theorem mPartner_eq : mPartner = meanPartner := rfl

theorem κ_mswZ (j : Fin 8) : κ (mswZ j) = meanScalarWeight j := by
  unfold mswZ meanScalarWeight; split_ifs
  · exact κ8
  · exact κ4
theorem κ_mSinZ (j : Fin 8) : κ (mSinZ j) = meanSinSign j := by
  fin_cases j <;> simp [mSinZ, meanSinSign]
theorem κ_mPhiZ (j : Fin 8) : κ (mPhiZ j) = 7 * meanPhiEigen j := by
  fin_cases j <;> simp [mPhiZ, meanPhiEigen, κ_mk] <;> ring
theorem κ_mMerZ (j : Fin 8) : κ (mMerZ j) = 7 * meanMeridianEigen j := by
  fin_cases j <;> simp [mMerZ, meanMeridianEigen, κ_mk] <;> ring
theorem κ_mBetaZ (j : Fin 8) : κ (mBetaZ j) = 7 * meanBetaFactor j := by
  fin_cases j <;> simp [mBetaZ, meanBetaFactor, κ_mk] <;> ring
theorem κ_cPhiZ (j : Fin 8) : κ (cPhiZ j) = 5488 * centeredPhiEigen j := by
  fin_cases j <;> simp [cPhiZ, centeredPhiEigen, κ_mk] <;> ring
theorem κ_cMerZ (j : Fin 8) : κ (cMerZ j) = 5488 * centeredMeridianEigen j := by
  fin_cases j <;> simp [cMerZ, centeredMeridianEigen, κ_mk] <;> ring
theorem κ_cBetaZ (j : Fin 8) : κ (cBetaZ j) = 5488 * centeredBetaFactor j := by
  fin_cases j <;> simp [cBetaZ, centeredBetaFactor, κ_mk] <;> ring

theorem ι_hZ (j k : Fin 8 × Fin 2) : ι (hZ j k) = 7 * meanHEntry j k := by
  rw [hZ, meanHEntry, mPartner_eq]
  split_ifs with h1 h2 h3
  · rw [ι_em, map_mul, κ_mswZ, κ_mPhiZ]; ring
  · rw [ι_em, map_mul, κ_mswZ, κ_mMerZ]; ring
  · rw [ι_zs, ι_hZ1]; simp [map_mul, κ_mswZ, κ_mBetaZ, κ_mSinZ, h3]; ring
  · rw [ι_zs, ι_hZ1]; simp [map_mul, κ_mswZ, κ_mBetaZ, κ_mSinZ, h3]; ring
  · rw [ι_zero]; ring

theorem ι_qEZ (j k : Fin 8 × Fin 2) : ι (qEZ j k) = 5488 * centeredQEntry j k := by
  rw [qEZ, centeredQEntry, mPartner_eq]
  split_ifs with h1 h2 h3
  · rw [ι_em, map_mul, κ_mswZ, κ_cPhiZ]; ring
  · rw [ι_em, map_mul, κ_mswZ, κ_cMerZ]; ring
  · rw [ι_zs, ι_hZ1]; simp [map_mul, κ_mswZ, κ_cBetaZ, κ_mSinZ, h3]; ring
  · rw [ι_zs, ι_hZ1]; simp [map_mul, κ_mswZ, κ_cBetaZ, κ_mSinZ, h3]; ring
  · rw [ι_zero]; ring

/-! ## Weights -/

theorem κ_kwZ (e : ContactIndex) : κ (kwZ e) = 2 * contactWeight e := by
  unfold kwZ contactWeight
  split_ifs
  · rw [κ2]; ring
  · rw [κ_mk, contactKappa, one_div, hinv]; push_cast; ring

theorem bw_rot01 (r : Fin 2) : boundaryWeight (boundaryRotationIndex (Fin.castSucc r)) = 4 * (1 + packingHeight) := by
  fin_cases r <;> simp [boundaryWeight, boundaryRotationIndex, hH2]

theorem bw_rot2 : boundaryWeight (boundaryRotationIndex 2) = 8 * packingRadius ^ 2 := by
  simp [boundaryWeight, boundaryRotationIndex]

theorem κ_wZ : κ wZ * (4 * (1 + packingHeight)) = 8 := by
  rw [show wZ = ⟨3, -1⟩ from rfl, κ_mk, packingHeight]; push_cast
  linear_combination (-8 / 7 : ℝ) * hs2'

theorem κ_tZ : κ tZ * contactTotalWeight = 56 := by
  rw [show tZ = ⟨4, -1⟩ from rfl, κ_mk, contactTotalWeight]; push_cast
  linear_combination (-4 : ℝ) * hs2'

theorem κ_mswN (j : Fin 8) : κ (mswN j) * meanScalarWeight j = 8 := by
  unfold mswN meanScalarWeight; split_ifs
  · simp
  · rw [κ2]; norm_num

end ThomsonCompact.TailC.Centered
