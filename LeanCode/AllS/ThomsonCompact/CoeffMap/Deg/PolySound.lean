import ThomsonCompact.CoeffMap.Deg.Poly
import ThomsonCompact.CoeffMap.MomentSound
import ThomsonCompact.CoeffMap.PackLemmas
import ThomsonCompact.CoeffMap.Rep
import AllS.Units.N_AI.N_residual_replay.RawSparseLookupSupport

/-!
# Soundness of the raw scalar coordinate mirror (F2e)

`spEval L` is the old sparse-catalogue polynomial of the integer term list `L` (denominator 1), so
`MvPolynomial.coeff (tagExponent t) (spEval L) = rawIntegerLookup L t` (`spEval_coeff`, from the old
`integerSparsePolynomial_coeff`). The kernel operations are sound for `spEval` (`spEval_shift`, `spEval_scale`,
`spEval_mul`, `spEval_merge`), the power-sum tables are the old `rawInvariantPowerSum` / `rawInvariantPairPowerSum`
(`psTab_at`, `ppsTab_at`), and

* `par3_eval`: `spEval (par3 P PP i j k) = 3 · rawParityCoordinates i j k`,
* `rscZ_eval`: `spEval (rscZ P PP f det lq rq t) = famDen f · rawScalarCoordinates ⟨f, det, lq, rq, t⟩` (`f ≤ 4`),

whenever the power-sum indices are inside the tables.
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap

/-- Semantics of a sparse integer polynomial: the old sparse-catalogue polynomial with denominator `1`. -/
def spEval (L : SP) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry 1 L))

theorem spEval_nil : spEval [] = 0 := by
  simp [spEval, normalizeIntegerRawEntry, RawCatalogue.sparsePolynomial]

theorem spEval_cons (e : T3 × ℤ) (L : SP) :
    spEval (e :: L) = MvPolynomial.C (e.2 : ℝ) * coordinateMonomial e.1 + spEval L := by
  simp [spEval, normalizeIntegerRawEntry, RawCatalogue.sparsePolynomial, RawCatalogue.ratToReal,
    coordinateMonomial, mul_assoc]

theorem spEval_coeff (L : SP) (t : T3) :
    MvPolynomial.coeff (tagExponent t) (spEval L) = (rawIntegerLookup L t : ℝ) := by
  have h := integerSparsePolynomial_coeff L 1 t
  simpa [spEval] using h

theorem spEval_append : ∀ L M : SP, spEval (L ++ M) = spEval L + spEval M
  | [], M => by simp [spEval_nil]
  | e :: L, M => by rw [List.cons_append, spEval_cons, spEval_cons, spEval_append L M]; ring

theorem cm_tadd (t u : T3) : coordinateMonomial (tadd t u) = coordinateMonomial t * coordinateMonomial u := by
  simp only [coordinateMonomial, tadd, Nat.add_eq, pow_add]; ring

theorem spEval_shift (t : T3) : ∀ L : SP, spEval (spShift t L) = coordinateMonomial t * spEval L
  | [] => by simp [spShift, spEval_nil]
  | e :: L => by
    show spEval ((tadd e.1 t, e.2) :: spShift t L) = _
    rw [spEval_cons, spEval_cons, spEval_shift t L, cm_tadd]; ring

theorem spEval_scale (c : ℤ) : ∀ L : SP, spEval (spScale c L) = MvPolynomial.C (c : ℝ) * spEval L
  | [] => by simp [spScale, spEval_nil]
  | e :: L => by
    show spEval ((e.1, c * e.2) :: spScale c L) = _
    rw [spEval_cons, spEval_cons, spEval_scale c L]; push_cast; rw [map_mul]; ring

theorem spEval_map_mul (e : T3 × ℤ) : ∀ M : SP,
    spEval (M.map fun f => (tadd e.1 f.1, e.2 * f.2)) =
      MvPolynomial.C (e.2 : ℝ) * coordinateMonomial e.1 * spEval M
  | [] => by simp [spEval_nil]
  | f :: M => by
    rw [List.map_cons, spEval_cons, spEval_cons, spEval_map_mul e M, cm_tadd]; push_cast; rw [map_mul]; ring

theorem spEval_mul : ∀ L M : SP, spEval (spMul L M) = spEval L * spEval M
  | [], M => by simp [spMul, spEval_nil]
  | e :: L, M => by
    show spEval ((M.map fun f => (tadd e.1 f.1, e.2 * f.2)) ++ spMul L M) = _
    rw [spEval_append, spEval_map_mul, spEval_mul L M, spEval_cons]; ring

theorem teq_eq {t u : T3} (h : teq t u = true) : t = u := by
  unfold teq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := u
  simp only at e1 e2 e3
  rw [e1, e2, e3]

theorem spMergeF_zero (L M : SP) : spMergeF 0 L M = L ++ M := rfl
theorem spMergeF_nil (f : ℕ) (M : SP) : spMergeF (f + 1) [] M = M := rfl
theorem spMergeF_cons_nil (f : ℕ) (a : T3 × ℤ) (L : SP) : spMergeF (f + 1) (a :: L) [] = a :: L := rfl
theorem spMergeF_cons_cons (f : ℕ) (a b : T3 × ℤ) (L M : SP) : spMergeF (f + 1) (a :: L) (b :: M) =
    cond (Nat.blt (tkey a.1) (tkey b.1)) (a :: spMergeF f L (b :: M))
      (cond (Nat.blt (tkey b.1) (tkey a.1)) (b :: spMergeF f (a :: L) M)
        (cond (teq a.1 b.1)
          (cond (decide (a.2 + b.2 = 0)) (spMergeF f L M) ((a.1, a.2 + b.2) :: spMergeF f L M))
          (a :: b :: spMergeF f L M))) := rfl

theorem spEval_mergeF : ∀ (f : ℕ) (L M : SP), spEval (spMergeF f L M) = spEval L + spEval M
  | 0, L, M => by rw [spMergeF_zero, spEval_append]
  | f + 1, [], M => by rw [spMergeF_nil, spEval_nil, zero_add]
  | f + 1, a :: L, [] => by rw [spMergeF_cons_nil, spEval_nil, add_zero]
  | f + 1, a :: L, b :: M => by
    have ih := spEval_mergeF f
    rw [spMergeF_cons_cons]
    cases h1 : Nat.blt (tkey a.1) (tkey b.1)
    · cases h2 : Nat.blt (tkey b.1) (tkey a.1)
      · cases h3 : teq a.1 b.1
        · simp only [cond_false, spEval_cons, ih]; ring
        · have hab := teq_eq h3
          cases h4 : decide (a.2 + b.2 = 0)
          · simp only [cond_false, cond_true, spEval_cons, ih, hab]; push_cast; rw [map_add]; ring
          · have h5 : (a.2 : ℝ) + b.2 = 0 := by exact_mod_cast of_decide_eq_true h4
            simp only [cond_true, cond_false, spEval_cons, ih, hab]
            have : MvPolynomial.C (a.2 : ℝ) * coordinateMonomial b.1 +
                MvPolynomial.C (b.2 : ℝ) * coordinateMonomial b.1 = 0 := by
              rw [← add_mul, ← map_add, h5, map_zero, zero_mul]
            linear_combination (-1 : Poly3) * this
      · simp only [cond_false, cond_true, spEval_cons, ih]; ring
    · simp only [cond_true, spEval_cons, ih]; ring

theorem spEval_merge (L M : SP) : spEval (spMerge L M) = spEval L + spEval M := spEval_mergeF _ L M

/-! ## Power sums -/

theorem seqOf_succ (step : SP × SP × SP → SP × SP × SP) (n : ℕ) (x : SP × SP × SP) :
    seqOf step (n + 1) x = x.1 :: seqOf step n (step x) := rfl

theorem listAt_seqOf (step : SP × SP × SP → SP × SP × SP) : ∀ (n i : ℕ) (x : SP × SP × SP), i < n →
    listAt [] (seqOf step n x) i = (step^[i] x).1
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, x, _ => by rw [seqOf_succ, listAt_eq]; rfl
  | n + 1, i + 1, x, h => by
    rw [seqOf_succ, listAt_eq, List.getD_cons_succ, ← listAt_eq, listAt_seqOf step n i (step x) (by omega),
      Function.iterate_succ_apply]

theorem cm_e0 : coordinateMonomial (1, 0, 0) = MvPolynomial.X 0 := by simp [coordinateMonomial]
theorem cm_e1 : coordinateMonomial (0, 1, 0) = MvPolynomial.X 1 := by simp [coordinateMonomial]
theorem cm_e2 : coordinateMonomial (0, 0, 1) = MvPolynomial.X 2 := by simp [coordinateMonomial]
theorem cm_zero : coordinateMonomial (0, 0, 0) = 1 := by simp [coordinateMonomial]

theorem ps_triple : ∀ i : ℕ, spEval (psStep^[i] ps0).1 = rawInvariantPowerSum i ∧
    spEval (psStep^[i] ps0).2.1 = rawInvariantPowerSum (i + 1) ∧
    spEval (psStep^[i] ps0).2.2 = rawInvariantPowerSum (i + 2)
  | 0 => by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [ps0, spEval_cons, spEval_nil, rawInvariantPowerSum, coordinateMonomial, map_ofNat] <;> ring
  | i + 1 => by
    obtain ⟨h0, h1, h2⟩ := ps_triple i
    rw [Function.iterate_succ_apply']
    refine ⟨h1, h2, ?_⟩
    show spEval (spMerge (spMerge (spShift (1, 0, 0) (psStep^[i] ps0).2.2)
      (spScale (-1) (spShift (0, 1, 0) (psStep^[i] ps0).2.1))) (spShift (0, 0, 1) (psStep^[i] ps0).1)) = _
    rw [spEval_merge, spEval_merge, spEval_shift, spEval_scale, spEval_shift, spEval_shift, h0, h1, h2,
      cm_e0, cm_e1, cm_e2, show i + 1 + 2 = i + 3 by ring, rawInvariantPowerSum]
    push_cast
    rw [map_neg, map_one]; ring

theorem pps_triple : ∀ i : ℕ, spEval (ppsStep^[i] pps0).1 = rawInvariantPairPowerSum i ∧
    spEval (ppsStep^[i] pps0).2.1 = rawInvariantPairPowerSum (i + 1) ∧
    spEval (ppsStep^[i] pps0).2.2 = rawInvariantPairPowerSum (i + 2)
  | 0 => by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [pps0, spEval_cons, spEval_nil, rawInvariantPairPowerSum, coordinateMonomial, map_ofNat] <;> ring
  | i + 1 => by
    obtain ⟨h0, h1, h2⟩ := pps_triple i
    rw [Function.iterate_succ_apply']
    refine ⟨h1, h2, ?_⟩
    show spEval (spMerge (spMerge (spShift (0, 1, 0) (ppsStep^[i] pps0).2.2)
      (spScale (-1) (spShift (1, 0, 1) (ppsStep^[i] pps0).2.1))) (spShift (0, 0, 2) (ppsStep^[i] pps0).1)) = _
    rw [spEval_merge, spEval_merge, spEval_shift, spEval_scale, spEval_shift, spEval_shift, h0, h1, h2,
      cm_e1, show i + 1 + 2 = i + 3 by ring, rawInvariantPairPowerSum]
    push_cast
    rw [map_neg, map_one]
    simp only [coordinateMonomial, pow_zero, pow_one, one_mul, mul_one]
    ring

theorem psTab_at (n i : ℕ) (hi : i < n) : spEval (listAt [] (psTab n) i) = rawInvariantPowerSum i := by
  rw [psTab, listAt_seqOf psStep n i ps0 hi]; exact (ps_triple i).1

theorem ppsTab_at (n i : ℕ) (hi : i < n) : spEval (listAt [] (ppsTab n) i) = rawInvariantPairPowerSum i := by
  rw [ppsTab, listAt_seqOf ppsStep n i pps0 hi]; exact (pps_triple i).1

/-! ## Parity coordinates -/

theorem spEval_flatMap {α : Type*} (g : α → SP) : ∀ L : List α, spEval (L.flatMap g) = (L.map (spEval ∘ g)).sum
  | [] => by simp [spEval_nil]
  | a :: L => by rw [List.flatMap_cons, spEval_append, spEval_flatMap g L, List.map_cons, List.sum_cons]; rfl

theorem sign_int (l : ℕ) : ((cond (Nat.beq (Nat.land l 1) 0) (1 : ℤ) (-1) : ℤ) : ℝ) = (-1 : ℝ) ^ l := by
  have hl : Nat.land l 1 = l % 2 := Nat.and_one_is_mod l
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · have hb : Nat.beq (Nat.land l 1) 0 = true := by rw [hl, h]; rfl
    rw [hb, cond_true, Int.cast_one, Even.neg_one_pow (Nat.even_iff.mpr h)]
  · have hb : Nat.beq (Nat.land l 1) 0 = false := by rw [hl, h]; rfl
    rw [hb, cond_false, Int.cast_neg, Int.cast_one, Odd.neg_one_pow (Nat.odd_iff.mpr h)]

theorem cm_shift_parity (a b : ℕ) : coordinateMonomial (a, 0, b) = MvPolynomial.X 0 ^ a * MvPolynomial.X 2 ^ b := by
  simp [coordinateMonomial]

/-- `par3` is three times the old parity coordinate (power-sum indices inside the tables). -/
theorem par3_eval (n : ℕ) (i j k : ℕ) (hij : i + j < n) (hk : k < n) :
    spEval (par3 (psTab n) (ppsTab n) i j k) = MvPolynomial.C (3 : ℝ) * rawParityCoordinates i j k := by
  unfold par3 rawParityCoordinates
  rw [spEval_flatMap, list_sum_range, ← mul_assoc, ← map_mul, show (3 : ℝ) * (1 / 3) = 1 by norm_num, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  simp only [Function.comp]
  rw [spEval_scale]
  push_cast
  rw [sign_int, chooseI_eq]
  by_cases hkl : k ≤ i + l
  · rw [show Nat.ble k (Nat.add i l) = true from Nat.ble_eq.mpr hkl, cond_true, if_pos hkl, spEval_shift,
      cm_shift_parity, psTab_at n _ (show Nat.sub (Nat.add i l) k < n by simp only [Nat.sub_eq, Nat.add_eq]; omega)]
    simp only [map_mul, map_pow, map_neg, map_one, Int.ofNat_eq_natCast, Int.cast_natCast, map_natCast, Nat.sub_eq,
      Nat.add_eq]
    ring
  · rw [show Nat.ble k (Nat.add i l) = false from Bool.eq_false_iff.mpr (fun h => hkl (Nat.ble_eq.mp h)), cond_false, if_neg hkl, spEval_shift,
      cm_shift_parity, ppsTab_at n _ (show Nat.sub k (Nat.add i l) < n by simp only [Nat.sub_eq, Nat.add_eq]; omega)]
    simp only [map_mul, map_pow, map_neg, map_one, Int.ofNat_eq_natCast, Int.cast_natCast, map_natCast, Nat.sub_eq,
      Nat.add_eq]
    ring

theorem even3_eval (n : ℕ) (t : T3) (h1 : t.1 + 2 + t.2.1 < n) (h2 : t.2.2 < n) :
    spEval (even3 (psTab n) (ppsTab n) t) = MvPolynomial.C (3 : ℝ) * rawEvenCoordinates t := by
  unfold even3 rawEvenCoordinates
  rw [spEval_append, spEval_scale, par3_eval n _ _ _ (by omega) h2, par3_eval n _ _ _ h1 h2]
  push_cast
  rw [map_neg, map_one]
  ring

theorem odd3_eval (n : ℕ) (t : T3) (h1 : t.1 + t.2.1 + 4 < n) (h2 : t.2.2 + 1 < n) :
    spEval (odd3 (psTab n) (ppsTab n) t) = MvPolynomial.C (3 : ℝ) * rawOddCoordinates t := by
  unfold odd3 rawOddCoordinates
  rw [spEval_append, spEval_scale, even3_eval n _ (by simp only [Nat.add_eq]; omega) (by simp only; omega),
    even3_eval n _ (by simp only [Nat.add_eq]; omega) (by simp only [Nat.add_eq]; omega)]
  simp only [Nat.add_eq]
  push_cast
  rw [show ((-4 : ℝ)) = -(4 : ℝ) from rfl, map_neg, show (MvPolynomial.C (4 : ℝ) : Poly3) = 4 from map_ofNat _ 4]
  ring

/-! ## Fixed weights -/

theorem spEval_wSP (det : Bool) : spEval (wSP det) = rawSymmetricWeight det := by
  apply MvPolynomial.funext
  intro x
  cases det <;>
    simp [wSP, detSP, spEval_cons, spEval_nil, rawSymmetricWeight, rawDeterminantCoordinates, coordinateMonomial] <;>
    ring

theorem spEval_disc : spEval discSP = rawDiscriminantCoordinates := by
  apply MvPolynomial.funext
  intro x
  simp [discSP, spEval_cons, spEval_nil, rawDiscriminantCoordinates, coordinateMonomial]
  ring

theorem spEval_std81 (p q : Bool) : spEval (std81 p q) = MvPolynomial.C (81 : ℝ) * rawStandardCoordinates p q := by
  apply MvPolynomial.funext
  intro x
  cases p <;> cases q <;>
    simp [std81, spEval_cons, spEval_nil, rawStandardCoordinates, coordinateMonomial] <;> ring

theorem famDen_0 : famDen 0 = 1 := rfl
theorem famDen_1 : famDen 1 = 1 := rfl
theorem famDen_3 : famDen 3 = 3 := rfl
theorem famDen_4 : famDen 4 = 3 := rfl

/-- **The mirror of the raw scalar coordinates** (families `0 … 4`; power-sum indices inside the tables). -/
theorem rscZ_eval (n : ℕ) (f : ℕ) (hf : f ≤ 4) (det lq rq : Bool) (t : T3)
    (hb : 3 ≤ f → t.1 + t.2.1 + 4 < n ∧ t.2.2 + 2 < n) :
    spEval (rscZ (psTab n) (ppsTab n) f det lq rq t) =
      MvPolynomial.C ((famDen f : ℕ) : ℝ) * rawScalarCoordinates ⟨f, det, lq, rq, t⟩ := by
  interval_cases f
  · simp only [rscZ, show Nat.beq 0 0 = true from rfl, cond_true]
    rw [spEval_shift, spEval_wSP, famDen_0]
    simp only [rawScalarCoordinates, Nat.cast_one, map_one, one_mul]
    ring
  · simp only [rscZ, show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl, cond_true, cond_false]
    rw [spEval_shift, spEval_mul, spEval_wSP, spEval_disc, famDen_1]
    simp only [rawScalarCoordinates, Nat.cast_one, map_one, one_mul]
    ring
  · simp only [rscZ, show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
      show Nat.beq 2 2 = true from rfl, cond_true, cond_false]
    rw [spEval_shift, spEval_mul, spEval_wSP, spEval_std81]
    simp only [rawScalarCoordinates, famDen, show Nat.beq 2 2 = true from rfl, cond_true]
    ring
  · obtain ⟨h1, h2⟩ := hb (le_refl 3)
    simp only [rscZ, show Nat.beq 3 0 = false from rfl, show Nat.beq 3 1 = false from rfl,
      show Nat.beq 3 2 = false from rfl, show Nat.beq 3 3 = true from rfl, cond_true, cond_false]
    rw [even3_eval n t (by omega) (by omega), famDen_3]
    simp only [rawScalarCoordinates]
    norm_num
  · obtain ⟨h1, h2⟩ := hb (by norm_num)
    simp only [rscZ, show Nat.beq 4 0 = false from rfl, show Nat.beq 4 1 = false from rfl,
      show Nat.beq 4 2 = false from rfl, show Nat.beq 4 3 = false from rfl, show Nat.beq 4 4 = true from rfl,
      cond_true, cond_false]
    rw [odd3_eval n t (by omega) (by omega), famDen_4]
    simp only [rawScalarCoordinates]
    norm_num

#print axioms rscZ_eval
#print axioms spEval_coeff

end ThomsonCompact.CoeffMap.Deg
