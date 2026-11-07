import AllS.Units.N_FI.N_energy_lower.N_energy_bound

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def hermiteGap (s a : ℝ) (m : Fin 5 → ℕ) (Y : Configuration) (i j : Fin 8) : ℝ :=
  phi s (inner ℝ (Y i) (Y j))-(hermitePolynomial s a m).eval (inner ℝ (Y i) (Y j))

theorem hermiteGap_nonneg {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (i j : Fin 8) (hij : i≠j) : 0 ≤ hermiteGap s a m Y i j := by
  have hne : Y i≠Y j := fun he => hij (hY.2 he)
  have hd := (geometry_distance_domain (Y i) (Y j) (hY.1 i) (hY.1 j) hne).1
  exact sub_nonneg.mpr ((hermite_minorant s a D m h.s_nonneg h.physical_a h.profile_valid).1 _ hd.1 hd.2).1

theorem hermiteGap_sum (s a : ℝ) (m : Fin 5 → ℕ) (Y : Configuration) :
    PairSum (hermiteGap s a m Y)=Ehat s Y-polyPairEnergy (hermitePolynomial s a m) Y := by
  simp [PairSum,hermiteGap,Ehat,polyPairEnergy,Finset.sum_sub_distrib]

theorem equality_hermite_energy {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (he : E s Y=E s (X a)) :
    Ehat s Y=Ehat s (X a) ∧ polyPairEnergy (hermitePolynomial s a m) Y=Ehat s (X a) := by
  have hX := candidate_is_configuration a (physical_mem_Ioo a h.physical_a)
  have hn := (energy_eq_iff_normalized s h.s_nonneg Y (X a) hY hX).mp he
  exact ⟨hn,le_antisymm ((hermite_pair_energy_le h Y hY).trans hn.le)
    (certificate_hermite_energy_lower h Y hY)⟩

theorem equality_pair_gaps_zero {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (he : E s Y=E s (X a)) : ∀ i j,i≠j → hermiteGap s a m Y i j=0 := by
  obtain ⟨hn,hH⟩ := equality_hermite_energy h Y hY he
  have hsum : PairSum (hermiteGap s a m Y)=0 := by rw [hermiteGap_sum,hn,hH,sub_self]
  have hinner (i : Fin 8) : 0 ≤ ∑ j : Fin 8 with i<j,hermiteGap s a m Y i j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hermiteGap_nonneg h Y hY i j (ne_of_lt (Finset.mem_filter.mp hj).2)
  have hpos (i j : Fin 8) (hij : i<j) : hermiteGap s a m Y i j=0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hinner i)).mp hsum i (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj =>
      hermiteGap_nonneg h Y hY i j (ne_of_lt (Finset.mem_filter.mp hj).2))).mp hi j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩)
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hpos i j hlt
  · simpa only [hermiteGap,real_inner_comm (Y j) (Y i)] using hpos j i hgt

theorem equality_block_pairing_zero {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y)
    (he : E s Y=E s (X a)) (p : MomentPivots (D/2)) (β : ℝ) (W : GramFamily (D/2))
    (hW : ∀ b,(W.val b).PosDef) (hpoly : gramPoly a (D/2) p W=normalizedTarget s a β m)
    (b : GramBlock (D/2)) : gramMatrixPairing (W.val b) (gramBlockMoment Y a (D/2) p b)=0 := by
  have hH := (equality_hermite_energy h Y hY he).2
  have hz : distinctPolySum Y (gramPoly a (D/2) p W)=0 := by
    rw [hpoly,normalizedTarget_distinctSum,hH,sub_self,mul_zero]
  rw [distinct_gramPoly_pairing] at hz
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun b hb =>
    gramMatrixPairing_nonneg _ _ (hW b).posSemidef
      (moment_pos_weighted_outer_products Y hY.1 a (D/2) p b))).mp hz b (Finset.mem_univ _)

theorem equality_outer_summand_zero {n : ℕ} (W M : Matrix (Fin n) (Fin n) ℝ)
    (hW : W.PosSemidef) (hpair : gramMatrixPairing W M=0)
    (N : ℕ) (w : Fin N → ℝ) (v : Fin N → Fin n → ℝ) (hw : ∀ t,0 ≤ w t)
    (hrep : M=∑ t,w t • Matrix.vecMulVec (v t) (v t)) :
    ∀ t,w t*dotProduct (v t) (W.mulVec (v t))=0 := by
  rw [hrep,gramMatrixPairing_sum] at hpair
  simp only [gramMatrixPairing_smul,gramMatrixPairing_outer] at hpair
  intro t
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun r hr => mul_nonneg (hw r)
    (by simpa only [star_trivial] using hW.dotProduct_mulVec_nonneg (v r)))).mp hpair t (Finset.mem_univ _)

def EqualityZerosContract : Prop := ∀ s a D m,∀ h : Certificate s a D m,
  ∀ Y : Configuration,IsConfiguration Y → E s Y=E s (X a) →
  (∀ i j,i≠j → hermiteGap s a m Y i j=0) ∧
  (∀ p : MomentPivots (D/2),∀ β : ℝ,∀ W : GramFamily (D/2),
    (∀ b,(W.val b).PosDef) → gramPoly a (D/2) p W=normalizedTarget s a β m →
    ∀ b,gramMatrixPairing (W.val b) (gramBlockMoment Y a (D/2) p b)=0 ∧
      ∀ N (w : Fin N → ℝ) (v : Fin N → Fin (gramBlockDimension (D/2) b) → ℝ),
        (∀ t,0 ≤ w t) → gramBlockMoment Y a (D/2) p b=∑ t,w t • Matrix.vecMulVec (v t) (v t) →
        ∀ t,w t*dotProduct (v t) ((W.val b).mulVec (v t))=0)

theorem energy_lower_equality_zeros : EqualityZerosContract := by
  intro s a D m h Y hY he
  refine ⟨equality_pair_gaps_zero h Y hY he,?_⟩
  intro p β W hW hpoly b
  have hz := equality_block_pairing_zero h Y hY he p β W hW hpoly b
  exact ⟨hz,equality_outer_summand_zero _ _ (hW b).posSemidef hz⟩

#check energy_lower_equality_zeros
#print axioms energy_lower_equality_zeros
end Blueprint.Thomson.Finite
