import AllS.Units.N_FI.N_raw_projection.PowerSumCatalogue
import AllS.Units.N_AI.N_residual_replay.RawSparseLookupSupport
import AllS.Units.N_FI.N_certificate.N_corrected_gram
import AllS.Units.N_FI.N_compatibility.N_normalized_target
import AllS.Units.N_F.N_height_upper
import AllS.Units.N_AI.N_fixed_tables.D12.Layout
import Blueprint.CAPContracts

/-!
# Exact target coordinates (F2a, no Taylor models)

The retained coordinate `t` of the normalized target `β · (avg H - E/28)` is
`β · H.coeff (w t) / 3 · [σ,b,c-coefficient of the power sum p_{w t} at t]`, `w = tagWeight`
(`raw_projection_target_coordinate`). The power-sum coefficients are read from the proven sparse catalogue
`PowerSumCatalogue.p00 … p18` (weights ≤ 18, i.e. all four active degrees), so the coordinate is the rational
`targetQ t j` (nonzero only for `j + 1 = w t`) times the Hermite coefficient `j + 1`.

* `retained_target_sum`: one theorem for every degree `D ≤ 18`, every profile `m` with `Profile.Valid D m`
  (in particular D12 'original' and 'far4') and every balance `β`.
* `D12.target_link`: exactly the `Residual12.target_link` field (β = 1, `t = 12` Hermite coefficients),
  with the computable table `D12.q` and `D12.hfun j x = (hermitePolynomial (s x) (aS (s x)) m).coeff (j+1)`.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- The proven sparse power-sum catalogue as one function of the weight. -/
def powerSparse : ℕ → RawCatalogue.SparsePoly
  | 0 => PowerSumCatalogue.p00
  | 1 => PowerSumCatalogue.p01
  | 2 => PowerSumCatalogue.p02
  | 3 => PowerSumCatalogue.p03
  | 4 => PowerSumCatalogue.p04
  | 5 => PowerSumCatalogue.p05
  | 6 => PowerSumCatalogue.p06
  | 7 => PowerSumCatalogue.p07
  | 8 => PowerSumCatalogue.p08
  | 9 => PowerSumCatalogue.p09
  | 10 => PowerSumCatalogue.p10
  | 11 => PowerSumCatalogue.p11
  | 12 => PowerSumCatalogue.p12
  | 13 => PowerSumCatalogue.p13
  | 14 => PowerSumCatalogue.p14
  | 15 => PowerSumCatalogue.p15
  | 16 => PowerSumCatalogue.p16
  | 17 => PowerSumCatalogue.p17
  | 18 => PowerSumCatalogue.p18
  | _ => []

theorem powerSparse_identity : ∀ w, w ≤ 18 →
    RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (powerSparse w)) = rawInvariantPowerSum w
  | 0, _ => PowerSumCatalogue.identity_00
  | 1, _ => PowerSumCatalogue.identity_01
  | 2, _ => PowerSumCatalogue.identity_02
  | 3, _ => PowerSumCatalogue.identity_03
  | 4, _ => PowerSumCatalogue.identity_04
  | 5, _ => PowerSumCatalogue.identity_05
  | 6, _ => PowerSumCatalogue.identity_06
  | 7, _ => PowerSumCatalogue.identity_07
  | 8, _ => PowerSumCatalogue.identity_08
  | 9, _ => PowerSumCatalogue.identity_09
  | 10, _ => PowerSumCatalogue.identity_10
  | 11, _ => PowerSumCatalogue.identity_11
  | 12, _ => PowerSumCatalogue.identity_12
  | 13, _ => PowerSumCatalogue.identity_13
  | 14, _ => PowerSumCatalogue.identity_14
  | 15, _ => PowerSumCatalogue.identity_15
  | 16, _ => PowerSumCatalogue.identity_16
  | 17, _ => PowerSumCatalogue.identity_17
  | 18, _ => PowerSumCatalogue.identity_18
  | _ + 19, h => absurd h (by omega)

/-- Power-sum coefficients are the computable sparse lookups. -/
theorem powerSum_coeff (w : ℕ) (hw : w ≤ 18) (t : Tag) :
    MvPolynomial.coeff (tagExponent t) (rawInvariantPowerSum w) =
      ((rawRationalLookup (powerSparse w) t : ℚ) : ℝ) := by
  rw [← powerSparse_identity w hw]
  change MvPolynomial.coeff _ (MvPolynomial.map (Rat.castHom ℝ) _) = _
  rw [MvPolynomial.coeff_map, sparsePolynomial_coeff_lookup]
  rfl

/-- The rational target table: coordinate `tg` reads Hermite coefficient `j + 1` iff `j + 1 = tagWeight tg`. -/
def targetQ {D : ℕ} (tg : Tag) (j : Fin D) : ℚ :=
  if j.val + 1 = tagWeight tg then rawRationalLookup (powerSparse (tagWeight tg)) tg / 3 else 0

/-- Retained target coordinate in closed form (any degree, profile and balance). -/
theorem retained_target (s a β : ℝ) (D : ℕ) (m : Fin 5 → ℕ) (hs : 0 ≤ s) (ha : physical a)
    (hroot : F s a = 0) (hm : Profile.Valid D m) (t : RetainedIndex D) :
    retainCompatible a D (normalizedTargetCompatible s a β D m hs ha hroot hm) t =
      β * (hermitePolynomial s a m).coeff (tagWeight t.val) / 3 *
        MvPolynomial.coeff (tagExponent t.val) (rawInvariantPowerSum (tagWeight t.val)) := by
  have hb : compatibleToBounded a D (normalizedTargetCompatible s a β D m hs ha hroot hm) =
      boundedNormalizedPolynomial D (hermitePolynomial s a m)
        (hermitePolynomial_natDegree_le s a D m hm) β (Ehat s (X a)) := Subtype.ext rfl
  show retainedCoordinates D (compatibleToBounded a D _) t = _
  rw [hb, raw_projection_target_coordinate]

theorem one_le_tagWeight {D : ℕ} (t : RetainedIndex D) : 1 ≤ tagWeight t.val := by
  have h0 := (mem_RetainedTags.mp t.property).2.1
  rcases hv : t.val with ⟨p, q, r⟩
  rw [hv] at h0
  simp only [tagWeight]
  by_contra hc
  exact h0 (by
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    have hr : r = 0 := by omega
    rw [hp, hq, hr])

/-- **Target link, generic.** For `D ≤ 18`, every profile and balance: the retained target coordinates are
`∑ j, targetQ t j · (β · H.coeff (j+1))` with the computable rational table `targetQ`. -/
theorem retained_target_sum (s a β : ℝ) (D : ℕ) (hD : D ≤ 18) (m : Fin 5 → ℕ) (hs : 0 ≤ s)
    (ha : physical a) (hroot : F s a = 0) (hm : Profile.Valid D m) (t : RetainedIndex D) :
    retainCompatible a D (normalizedTargetCompatible s a β D m hs ha hroot hm) t =
      ∑ j : Fin D, (targetQ t.val j : ℝ) * (β * (hermitePolynomial s a m).coeff (j.val + 1)) := by
  have hwD := (mem_RetainedTags.mp t.property).1
  have hw1 := one_le_tagWeight t
  rw [retained_target, powerSum_coeff _ (hwD.trans hD)]
  rw [Finset.sum_eq_single (⟨tagWeight t.val - 1, by omega⟩ : Fin D)]
  · have he : tagWeight t.val - 1 + 1 = tagWeight t.val := by omega
    simp only [targetQ, he, if_true]
    push_cast
    ring
  · intro j _ hj
    have hne : j.val + 1 ≠ tagWeight t.val := by
      intro h
      apply hj
      ext
      simp only
      omega
    simp only [targetQ, hne, if_false, Rat.cast_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

namespace D12

/-- D12 target table (`t = 12` Hermite coefficients `1 … 12`); computable. -/
def q (r : Fin 100) (j : Fin 12) : ℚ := targetQ (FixedTables.D12.coordinateTags r) j

/-- Hermite coefficient `j + 1` of the exact target at exponent `s x` (β = 1 for all D12 cells). -/
noncomputable def hfun (s : ℝ → ℝ) (m : Fin 5 → ℕ) (j : Fin 12) (x : ℝ) : ℝ :=
  (hermitePolynomial (s x) (aS (s x)) m).coeff (j.val + 1)

/-- Exactly the `Residual12.target_link` field (the target there unfolds to this
`normalizedTargetCompatible`), for every D12 profile. -/
theorem target_link (s : ℝ → ℝ) (m : Fin 5 → ℕ) :
    ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 12 m) (r : Fin 100),
      retainCompatible (aS (s x)) 12
        (normalizedTargetCompatible (s x) (aS (s x)) 1 12 m hs (aS_physical _ hs)
          (aS_mem_and_root _ hs).2 hm) (FixedTables.D12.retainedIndex r) =
        ∑ j, (q r j : ℝ) * hfun s m j x := by
  intro x _ hs hm r
  rw [retained_target_sum _ _ _ 12 (by norm_num), FixedTables.D12.retainedIndex_tag]
  simp only [one_mul, q, hfun]

end D12

#print axioms powerSum_coeff
#print axioms retained_target_sum
#print axioms D12.target_link

end ThomsonCompact.CoeffMap
