import ThomsonCompact.CoeffMap.W0Part
import ThomsonCompact.CoeffMap.KRowsRSound
import ThomsonCompact.CoeffMap.BSum

/-!
# Soundness of the checkpointed W0 sums (F2d)

* `walkP_spec`, `blockOkS_spec`: a leaf `blockOkS … = true` gives `ok` and `ckOk` of each of its pieces.
* `ck_valid`: `Encl c T f` and `ckOk c F T rec = true` give `(ckQ N S F rec).asTM.Valid f` (the checkpoint QModel,
  point coefficients `sdec dₖ · 2^F / 2^S`, error `e' 2^F / 2^S`).
* `valid_sum`: point QModels add (coefficients and errors).
* `sumOkR_spec`: the final record holds the coefficient sums and at least the error sum of the 112 checkpoints.
* `bsum_valid_of`: **per retained coordinate `r`, `(BsumQ N S sd r).asTM.Valid (fun x => ∑ ι, gpk s d hord ι r x)`**,
  i.e. the final record encloses the sum of the 112 W0 contribution pieces of `w0Part_of` (`Residual12.g`).
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.D12
open scoped BigOperators

/-! ## Leaves -/

theorem walkP_spec {α : Type} (p : ℕ → α → Bool) (r0 r1 : ℕ) (d : α) : ∀ (L : List α) (s : ℕ),
    walkP p r0 r1 L s = true → ∀ i, i < L.length → r0 ≤ s + i → s + i < r1 → p (s + i) (L.getD i d) = true
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: L, s, h, i, hi, h0, h1 => by
    have h' : cond (Nat.blt s r1) (cond (Nat.ble r0 s) (p s x && walkP p r0 r1 L (s + 1))
        (walkP p r0 r1 L (s + 1))) true = true := h
    rw [show Nat.blt s r1 = true from Nat.blt_eq.mpr (by omega), cond_true] at h'
    cases i with
    | zero =>
      rw [show Nat.ble r0 s = true from Nat.ble_eq.mpr (by omega), cond_true, Bool.and_eq_true] at h'
      simpa using h'.1
    | succ j =>
      have hrest : walkP p r0 r1 L (s + 1) = true := by
        cases hb : Nat.ble r0 s
        · rw [hb, cond_false] at h'; exact h'
        · rw [hb, cond_true, Bool.and_eq_true] at h'; exact h'.2
      have := walkP_spec p r0 r1 d L (s + 1) hrest j (by simp at hi; omega) (by omega) (by omega)
      rw [show s + (j + 1) = s + 1 + j by omega]
      simpa using this

theorem splitC_length {α : Type} : ∀ (lens : List ℕ) (L : List α), (splitC lens L).length = lens.length
  | [], _ => rfl
  | _ :: lens, L => by
    show (splitC lens _).length + 1 = lens.length + 1
    rw [splitC_length lens]

theorem eTabG_length (pb : ℕ) : (eTabG pb).length = 100 := by
  unfold eTabG
  rw [splitC_length, mkList_eq, List.length_map, List.length_range]

theorem blockOkS_spec {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {sd : SumData} {n bi g0 g1 r0 r1 : ℕ}
    (h : blockOkS c A WT sd n bi g0 g1 r0 r1 = true) :
    ∀ g, g0 ≤ g → g < g1 → ∀ r, r0 ≤ r → r < r1 → r < 100 →
      (blockTMgr c A WT bi g r).ok = true ∧ ckOk c sd.F n (blockTMgr c A WT bi g r) (ckRec sd n bi g r) = true := by
  induction g1 with
  | zero => intro g _ h1; exact absurd h1 (Nat.not_lt_zero _)
  | succ k ih =>
    intro g h0 h1 r hr0 hr1 hr
    have h' : cond (Nat.ble g0 k) (walkP (pieceOkS c A WT bi (ckRec sd n bi k) sd.F n) r0 r1
        (eTabG (Nat.add (Nat.mul 8 bi) k)) 0 && blockOkS c A WT sd n bi g0 k r0 r1)
        (blockOkS c A WT sd n bi g0 k r0 r1) = true := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h2 | h2
    · apply ih _ g h0 h2 r hr0 hr1 hr
      cases hb : Nat.ble g0 k
      · rw [hb] at h'; exact h'
      · rw [hb, cond_true, Bool.and_eq_true] at h'; exact h'.2
    · subst h2
      rw [show Nat.ble g0 g = true from Nat.ble_eq.mpr h0, cond_true, Bool.and_eq_true] at h'
      have hw := walkP_spec _ r0 r1 [] _ 0 h'.1 r (by rw [eTabG_length]; exact hr) (by omega) (by omega)
      rw [Nat.zero_add] at hw
      have hb : blockTMgr c A WT bi g r = gTMz c WT (blockRowr c A bi) (gDimN bi) (D12E.eSize bi)
          ((eTabG (Nat.add (Nat.mul 8 bi) g)).getD r []) (D12E.eDen bi) := by
        unfold blockTMgr
        rw [listAt_eq]
      unfold pieceOkS at hw
      rw [hb]
      simpa only [Bool.and_eq_true] using hw

/-! ## A checkpoint encloses what its piece encloses -/

/-- The QModel of a checkpoint record: point coefficients `sdec dₖ 2^F / 2^S`, error `e' 2^F / 2^S`. -/
noncomputable def ckQ (N S F : ℕ) (rec : List ℕ) : QModel N :=
  ⟨fun k => ⟨(sdec (rec.getD k.val 0) : ℚ) * 2 ^ F / 2 ^ S, (sdec (rec.getD k.val 0) : ℚ) * 2 ^ F / 2 ^ S⟩,
    ((rec.getD (N + 1) 0 : ℕ) : ℚ) * 2 ^ F / 2 ^ S⟩

theorem slotAt_eq (w x i : ℕ) : slotAt w x i = x / 2 ^ (w * i) % 2 ^ w := by
  unfold slotAt
  rw [show Nat.sub (Nat.shiftLeft 1 w) 1 = 2 ^ w - 1 from by
    rw [show Nat.shiftLeft 1 w = 1 <<< w from rfl, Nat.shiftLeft_eq, one_mul]; rfl]
  rw [show Nat.shiftRight x (Nat.mul w i) = x >>> (w * i) from rfl, Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem land_one (z : ℕ) : Nat.land z 1 = z % 2 := Nat.and_one_is_mod z

theorem shr_one (z : ℕ) : Nat.shiftRight z 1 = z / 2 := by
  show z >>> 1 = z / 2
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem sdec_eq (z : ℕ) : sdec z = if z % 2 = 1 then -((z / 2 : ℕ) : ℤ) else ((z / 2 : ℕ) : ℤ) := by
  unfold sdec
  rw [land_one, shr_one]
  split_ifs <;> simp

theorem absDiff_cast (x y : ℕ) : ((absDiff x y : ℕ) : ℤ) = |(x : ℤ) - y| := by
  unfold absDiff
  rcases le_total x y with h | h
  · rw [show Nat.add (Nat.sub x y) (Nat.sub y x) = y - x from by
      show x - y + (y - x) = y - x
      rw [Nat.sub_eq_zero_of_le h, zero_add]]
    have h' : (x : ℤ) ≤ y := by exact_mod_cast h
    rw [Nat.cast_sub h, abs_of_nonpos (by linarith)]
    ring
  · rw [show Nat.add (Nat.sub x y) (Nat.sub y x) = x - y from by
      show x - y + (y - x) = x - y
      rw [Nat.sub_eq_zero_of_le h, add_zero]]
    have h' : (y : ℤ) ≤ x := by exact_mod_cast h
    rw [Nat.cast_sub h, abs_of_nonneg (by linarith)]

/-- `devK` is the distance `|c - d 2^F|` for the biased slot `b = c + H`. -/
theorem devK_eq (H F b z : ℕ) (cf : ℤ) (hb : (b : ℤ) = cf + H) :
    (devK H F b z : ℤ) = |cf - sdec z * 2 ^ F| := by
  have hsh : Nat.shiftLeft (Nat.shiftRight z 1) F = z / 2 * 2 ^ F := by
    show (z >>> 1) <<< F = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, pow_one]
  unfold devK
  rw [land_one, hsh, sdec_eq]
  by_cases h : z % 2 = 1
  · rw [h, if_pos rfl]
    show ((absDiff (b + z / 2 * 2 ^ F) H : ℕ) : ℤ) = _
    rw [absDiff_cast]
    push_cast
    rw [hb]
    congr 1
    ring
  · have h0 : z % 2 = 0 := by omega
    rw [h0, if_neg (by decide)]
    show ((absDiff b (H + z / 2 * 2 ^ F)) : ℤ) = _
    rw [absDiff_cast]
    push_cast
    rw [hb]
    congr 1
    ring

theorem devSum_eq (W H F X : ℕ) (cs : ℕ → ℤ) (hcs : ∀ k, (slotAt W X k : ℤ) = cs k + H) :
    ∀ (zs : List ℕ) (k : ℕ), (devSum W H F X k zs : ℤ) =
      ∑ j ∈ Finset.range zs.length, |cs (k + j) - sdec (zs.getD j 0) * 2 ^ F|
  | [], _ => by simp [devSum]
  | z :: zs, k => by
    show ((devK H F (slotAt W X k) z + devSum W H F X (k + 1) zs : ℕ) : ℤ) = _
    rw [Nat.cast_add, devK_eq H F _ z (cs k) (hcs k), devSum_eq W H F X cs hcs zs (k + 1),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [show k + (j + 1) = k + 1 + j by omega])

theorem getD_take_of_lt (L : List ℕ) {m k : ℕ} (h : k < m) : (L.take m).getD k 0 = L.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

/-- Closeness of point coefficients gives validity of a point QModel (the polynomial may have a higher degree
`M - 1 ≥ N`; the QModel coefficients beyond `N` are zero). -/
theorem valid_of_close {N M : ℕ} (hNM : N + 1 ≤ M) (f : ℝ → ℝ) (p : ℕ → ℝ) (q : ℕ → ℚ)
    (hq : ∀ k, N < k → q k = 0) (e₀ dev : ℝ) (E : ℚ)
    (hf : ∀ x ∈ cellDomain, |f x - ∑ k ∈ Finset.range M, p k * x ^ k| ≤ e₀)
    (hdev : ∑ k ∈ Finset.range M, |p k - (q k : ℝ)| ≤ dev) (hE : e₀ + dev ≤ (E : ℝ)) (hE0 : 0 ≤ E) :
    (⟨fun k => ⟨q k.val, q k.val⟩, E⟩ : QModel N).asTM.Valid f := by
  refine ⟨hE0, fun k => (q k.val : ℝ), fun k => ⟨le_refl _, le_refl _⟩, fun x hx => ?_⟩
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
  have hse : scalarEval (fun k : Fin (N + 1) => (q k.val : ℝ)) x =
      ∑ k ∈ Finset.range M, (q k : ℝ) * x ^ k := by
    unfold scalarEval
    rw [Fin.sum_univ_eq_sum_range (fun k => (q k : ℝ) * x ^ k) (N + 1), ← Finset.sum_range_add_sum_Ico _ hNM]
    rw [Finset.sum_eq_zero (s := Finset.Ico (N + 1) M) (fun k hk => by
      rw [hq k (by have := (Finset.mem_Ico.mp hk).1; omega)]; simp), add_zero]
  rw [hse]
  have hsplit : f x - ∑ k ∈ Finset.range M, (q k : ℝ) * x ^ k =
      (f x - ∑ k ∈ Finset.range M, p k * x ^ k) + ∑ k ∈ Finset.range M, (p k - q k) * x ^ k := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc |(f x - ∑ k ∈ Finset.range M, p k * x ^ k) + ∑ k ∈ Finset.range M, (p k - q k) * x ^ k|
      ≤ |f x - ∑ k ∈ Finset.range M, p k * x ^ k| + |∑ k ∈ Finset.range M, (p k - q k) * x ^ k| :=
        abs_add_le _ _
    _ ≤ e₀ + ∑ k ∈ Finset.range M, |p k - (q k : ℝ)| := by
        refine add_le_add (hf x hx) ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_)))
        rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hx1)
    _ ≤ e₀ + dev := by linarith
    _ ≤ E := hE

theorem padRec_length (n m : ℕ) (rec : List ℕ) (hl : n + 1 ≤ rec.length) (hm : n + 1 ≤ m) :
    (padRec n m rec).length = m := by
  unfold padRec
  rw [List.length_append, List.length_take, List.length_replicate]
  show min (n + 1) rec.length + (m - (n + 1)) = m
  omega

theorem padRec_getD (n m : ℕ) (rec : List ℕ) (hl : n + 1 ≤ rec.length) (k : ℕ) :
    (padRec n m rec).getD k 0 = if k ≤ n then rec.getD k 0 else 0 := by
  unfold padRec
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  have htl : (rec.take (Nat.add n 1)).length = n + 1 := by
    rw [List.length_take]; show min (n + 1) rec.length = n + 1; omega
  split_ifs with h1 h2 h2
  · rw [List.getElem?_take, if_pos (by show k < n + 1; omega), ← List.getD_eq_getElem?_getD]
  · rw [htl] at h1; omega
  · rw [htl] at h1; omega
  · rw [htl, List.getElem?_replicate]
    split_ifs <;> rfl

/-- **A checkpoint of target order `n ≤ N` encloses what its piece (order `N`) encloses.** -/
theorem ck_valid {N S B W : ℕ} (hg : Good N S B W) {T : TM} {f : ℝ → ℝ} (hE : Encl (mkCtx N S B W) T f)
    (F n : ℕ) (hn : n ≤ N) (rec : List ℕ) (hl : n + 1 ≤ rec.length) (h : ckOk (mkCtx N S B W) F n T rec = true) :
    (ckQ n S F rec).asTM.Valid f := by
  set c := mkCtx N S B W with hc
  set cs := decode c T.v with hcs
  have hX : Nat.land (Nat.add T.v c.hb) c.maskK = (T.v + c.hb) % 2 ^ c.K := by
    rw [show c.maskK = Nat.sub (2 ^ c.K) 1 from rfl]
    exact land_mask_eq _ _
  have hm : c.m = N + 1 := rfl
  set csf : ℕ → ℤ := fun k =>
    (slotAt c.W (Nat.land (Nat.add T.v c.hb) c.maskK) k : ℤ) - (c.hW : ℕ) with hcsf
  have hslot' : ∀ k, (slotAt c.W (Nat.land (Nat.add T.v c.hb) c.maskK) k : ℤ) = csf k + (c.hW : ℕ) := by
    intro k; rw [hcsf]; ring
  have hcs_eq : ∀ k, k < N + 1 → csf k = cs.getD k 0 := by
    intro k hk
    rw [hcsf]
    dsimp only
    rw [hX, slotAt_eq, hcs]
    unfold decode
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, digitsN, List.getElem?_map,
      List.getElem?_range (by rw [hm]; exact hk)]
    simp only [Option.map_some, Option.getD_some]
    rw [show c.hW = 2 ^ (c.W - 1) from rfl]
    push_cast
    ring
  have hpl : (padRec n c.m rec).length = N + 1 := by rw [padRec_length n c.m rec hl (by rw [hm]; omega), hm]
  have hdev := devSum_eq c.W c.hW F _ csf hslot' (padRec n c.m rec) 0
  rw [hpl] at hdev
  unfold ckOk at h
  rw [Nat.ble_eq] at h
  set D := devSum c.W c.hW F (Nat.land (Nat.add T.v c.hb) c.maskK) 0 (padRec n c.m rec) with hD
  set q : ℕ → ℚ := fun k => if k ≤ n then (sdec (rec.getD k 0) : ℚ) * 2 ^ F / 2 ^ S else 0 with hq
  have hdevR : (D : ℝ) = ∑ k ∈ Finset.range (N + 1),
      |((cs.getD k 0 : ℤ) : ℝ) - (if k ≤ n then (sdec (rec.getD k 0) : ℝ) else 0) * 2 ^ F| := by
    have h1 : (D : ℝ) = ((D : ℤ) : ℝ) := rfl
    rw [h1, hdev]
    push_cast
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    rw [Nat.zero_add, hcs_eq k hk', padRec_getD n c.m rec hl k]
    split_ifs <;> simp [sdec_zero]
  have hQ : ckQ n S F rec = (⟨fun k => ⟨q k.val, q k.val⟩, ((rec.getD (n + 1) 0 : ℕ) : ℚ) * 2 ^ F / 2 ^ S⟩ : QModel n) := by
    unfold ckQ
    congr 1
    funext k
    rw [hq]
    dsimp only
    rw [if_pos (Nat.lt_succ_iff.mp k.isLt)]
  rw [hQ]
  refine valid_of_close (M := N + 1) (by omega) f (fun k => ((cs.getD k 0 : ℤ) : ℝ) / 2 ^ S) q
    (fun k hk => by rw [hq]; dsimp only; rw [if_neg (by omega)])
    ((T.e : ℝ) / 2 ^ S) ((D : ℝ) / 2 ^ S) _ ?_ ?_ ?_ ?_
  · intro x hx
    have h1 := (Encl.export hg hE) x hx
    rw [poly_eq_sum] at h1
    simp only [show (mkCtx N S B W).m = N + 1 from rfl, show (mkCtx N S B W).S = S from rfl] at h1
    simpa only [err, show (mkCtx N S B W).S = S from rfl, div_mul_eq_mul_div] using h1
  · rw [hdevR, Finset.sum_div]
    refine le_of_eq (Finset.sum_congr rfl (fun k _ => ?_))
    rw [hq]
    dsimp only
    split_ifs
    · push_cast
      rw [show ((cs.getD k 0 : ℤ) : ℝ) / 2 ^ S - (sdec (rec.getD k 0) : ℝ) * 2 ^ F / 2 ^ S =
        (((cs.getD k 0 : ℤ) : ℝ) - (sdec (rec.getD k 0) : ℝ) * 2 ^ F) / 2 ^ S by ring, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ S)]
    · push_cast
      rw [zero_mul, sub_zero, sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ S)]
  · have h2 : ((T.e + D : ℕ) : ℝ) ≤ ((rec.getD (n + 1) 0 * 2 ^ F : ℕ) : ℝ) := by
      have : D + T.e ≤ rec.getD (n + 1) 0 * 2 ^ F := by
        have h' : Nat.add D T.e ≤ Nat.shiftLeft (rec.getD (Nat.add n 1) 0) F := h
        rwa [show Nat.shiftLeft (rec.getD (Nat.add n 1) 0) F = rec.getD (n + 1) 0 * 2 ^ F from
          Nat.shiftLeft_eq _ _] at h'
      exact_mod_cast (by omega : T.e + D ≤ rec.getD (n + 1) 0 * 2 ^ F)
    push_cast at h2 ⊢
    rw [← add_div]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  · positivity

/-! ## Sums of point QModels -/

theorem point_coeff_eq {N : ℕ} {M : QModel N} {p : Fin (N + 1) → ℚ}
    (hp : ∀ k, M.coeff k = ⟨p k, p k⟩) (a : Fin (N + 1) → ℝ) (ha : M.asTM.CoeffContains a) :
    ∀ k, a k = (p k : ℝ) := by
  intro k
  have h := ha k
  simp only [QModel.asTM, QInterval.asBox, hp k, Box.Contains] at h
  exact le_antisymm h.2 h.1

/-- **Point QModels add.** -/
theorem valid_sum {N : ℕ} {ι : Type*} (s : Finset ι) (M : ι → QModel N) (f : ι → ℝ → ℝ)
    (p : ι → Fin (N + 1) → ℚ) (hp : ∀ i k, (M i).coeff k = ⟨p i k, p i k⟩)
    (hv : ∀ i ∈ s, (M i).asTM.Valid (f i)) (D : QModel N)
    (hD : ∀ k, D.coeff k = ⟨∑ i ∈ s, p i k, ∑ i ∈ s, p i k⟩) (hE : ∑ i ∈ s, (M i).error ≤ D.error) :
    D.asTM.Valid (fun x => ∑ i ∈ s, f i x) := by
  have hE0 : 0 ≤ ∑ i ∈ s, (M i).error := Finset.sum_nonneg (fun i hi => (hv i hi).1)
  refine ⟨hE0.trans hE, fun k => ((∑ i ∈ s, p i k : ℚ) : ℝ), fun k => ?_, fun x hx => ?_⟩
  · simp only [QModel.asTM, QInterval.asBox, hD k, Box.Contains]
    exact ⟨le_refl _, le_refl _⟩
  · have hbound : ∀ i ∈ s, |f i x - scalarEval (fun k => (p i k : ℝ)) x| ≤ ((M i).error : ℝ) := by
      intro i hi
      obtain ⟨_, a, ha, hf⟩ := hv i hi
      have := hf x hx
      rwa [show a = fun k => (p i k : ℝ) from funext (point_coeff_eq (hp i) a ha)] at this
    have hsum : scalarEval (fun k => ((∑ i ∈ s, p i k : ℚ) : ℝ)) x =
        ∑ i ∈ s, scalarEval (fun k => (p i k : ℝ)) x := by
      unfold scalarEval
      push_cast
      simp only [Finset.sum_mul]
      exact Finset.sum_comm
    rw [hsum, ← Finset.sum_sub_distrib]
    calc |∑ i ∈ s, (f i x - scalarEval (fun k => (p i k : ℝ)) x)|
        ≤ ∑ i ∈ s, |f i x - scalarEval (fun k => (p i k : ℝ)) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, ((M i).error : ℝ) := Finset.sum_le_sum hbound
      _ ≤ (D.error : ℝ) := by exact_mod_cast hE

/-! ## The sum leaf -/

/-- Value of a `(positive, negative)` accumulator. -/
def pval (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2

theorem decRec_length (ws : ℕ) : ∀ n i x, (decRec ws n i x).length = n
  | 0, _, _ => rfl
  | n + 1, i, x => by
    show (decRec ws n _ _).length + 1 = n + 1
    rw [decRec_length ws n]

theorem accSM_length : ∀ (zs : List ℕ) (acc : List (ℕ × ℕ)), (accSM zs acc).length = acc.length
  | z :: zs, p :: acc => by
    show (accSM zs acc).length + 1 = acc.length + 1
    rw [accSM_length zs acc]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem accSM_val : ∀ (zs : List ℕ) (acc : List (ℕ × ℕ)) (k : ℕ), k < acc.length →
    pval ((accSM zs acc).getD k (0, 0)) = pval (acc.getD k (0, 0)) + sdec (zs.getD k 0)
  | z :: zs, p :: acc, k, hk => by
    cases k with
    | zero =>
      show pval (cond (Nat.beq (Nat.land z 1) 1) (p.1, Nat.add p.2 (Nat.shiftRight z 1))
        (Nat.add p.1 (Nat.shiftRight z 1), p.2)) = pval p + sdec z
      rw [sdec_eq, land_one, shr_one]
      by_cases h : z % 2 = 1
      · rw [h, if_pos rfl]
        show pval (p.1, p.2 + z / 2) = pval p + -((z / 2 : ℕ) : ℤ)
        unfold pval; push_cast; ring
      · have h0 : z % 2 = 0 := by omega
        rw [h0, if_neg (by decide)]
        show pval (p.1 + z / 2, p.2) = pval p + ((z / 2 : ℕ) : ℤ)
        unfold pval; push_cast; ring
    | succ j =>
      show pval ((accSM zs acc).getD j (0, 0)) = pval (acc.getD j (0, 0)) + sdec (zs.getD j 0)
      exact accSM_val zs acc j (by simp at hk; omega)
  | [], acc, k, _ => by
    show pval (acc.getD k (0, 0)) = pval (acc.getD k (0, 0)) + sdec (([] : List ℕ).getD k 0)
    simp [sdec_zero]
  | _ :: _, [], k, hk => absurd hk (Nat.not_lt_zero _)

theorem accRecs_spec (m : ℕ) : ∀ (L : List (List ℕ)) (acc : List (ℕ × ℕ)) (e : ℕ),
    (accRecs m L (acc, e)).1.length = acc.length ∧
    (∀ k, k < acc.length → pval ((accRecs m L (acc, e)).1.getD k (0, 0)) =
      pval (acc.getD k (0, 0)) + (L.map fun rec => sdec ((rec.take m).getD k 0)).sum) ∧
    (accRecs m L (acc, e)).2 = e + (L.map fun rec => rec.getD m 0).sum
  | [], acc, e => ⟨rfl, fun k _ => by
      show pval (acc.getD k (0, 0)) = pval (acc.getD k (0, 0)) + (([] : List (List ℕ)).map _).sum
      simp, by simp [accRecs]⟩
  | rec :: L, acc, e => by
    obtain ⟨h1, h2, h3⟩ := accRecs_spec m L (accSM (rec.take m) acc) (Nat.add e (rec.getD m 0))
    refine ⟨?_, fun k hk => ?_, ?_⟩
    · show (accRecs m L (accSM (rec.take m) acc, Nat.add e (rec.getD m 0))).1.length = _
      rw [h1, accSM_length]
    · show pval ((accRecs m L (accSM (rec.take m) acc, Nat.add e (rec.getD m 0))).1.getD k (0, 0)) = _
      rw [h2 k (by rw [accSM_length]; exact hk), accSM_val _ _ k hk, List.map_cons, List.sum_cons]
      ring
    · show (accRecs m L (accSM (rec.take m) acc, Nat.add e (rec.getD m 0))).2 = _
      rw [h3, List.map_cons, List.sum_cons]
      show e + rec.getD m 0 + _ = _
      ring

theorem smEq_spec {z : ℕ} {p : ℕ × ℕ} (h : smEq z p = true) : sdec z = pval p := by
  unfold smEq at h
  rw [sdec_eq]
  unfold pval
  rw [land_one, shr_one] at h
  by_cases hz : z % 2 = 1
  · rw [hz, show Nat.beq 1 1 = true from rfl, cond_true, Nat.beq_eq] at h
    rw [if_pos hz, h]
    show -(((z / 2 : ℕ) : ℤ)) = (p.1 : ℤ) - ((z / 2 + p.1 : ℕ) : ℤ)
    rw [Nat.cast_add]
    ring
  · have h0 : z % 2 = 0 := by omega
    rw [h0, show Nat.beq 0 1 = false from rfl, cond_false, Nat.beq_eq] at h
    rw [if_neg hz, h]
    show (((z / 2 : ℕ) : ℤ)) = ((z / 2 + p.2 : ℕ) : ℤ) - (p.2 : ℤ)
    rw [Nat.cast_add]
    ring

theorem smAll_spec : ∀ (zs : List ℕ) (ps : List (ℕ × ℕ)), smAll zs ps = true →
    zs.length = ps.length ∧ ∀ k, k < zs.length → sdec (zs.getD k 0) = pval (ps.getD k (0, 0))
  | [], [], _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | z :: zs, p :: ps, h => by
    have h' : (smEq z p && smAll zs ps) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hl, hk⟩ := smAll_spec zs ps h'.2
    refine ⟨by simp [hl], fun k hk' => ?_⟩
    cases k with
    | zero => exact smEq_spec h'.1
    | succ j => exact hk j (by simp at hk'; omega)
  | [], _ :: _, h => absurd h (by simp [smAll])
  | _ :: _, [], h => absurd h (by simp [smAll])

theorem lsum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, lsum_range f n, Finset.sum_range_succ]
    simp

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (f : α → List β) (φ : β → M) :
    ∀ L : List α, ((L.flatMap f).map φ).sum = (L.map fun x => ((f x).map φ).sum).sum
  | [] => by simp
  | x :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap f φ L, List.map_cons, List.sum_cons]

theorem recsAt_sum {M : Type*} [AddCommMonoid M] (sd : SumData) (n r : ℕ) (φ : List ℕ → M) :
    ((recsAt sd n r).map φ).sum = ∑ bi ∈ Finset.range 14, ∑ g ∈ Finset.range (ngD12 bi), φ (ckRec sd n bi g r) := by
  unfold recsAt
  rw [sum_map_flatMap, lsum_range]
  refine Finset.sum_congr rfl (fun bi _ => ?_)
  rw [List.map_map]
  exact lsum_range (φ ∘ fun g => ckRec sd n bi g r) (ngD12 bi)

/-- **The sum leaf**: the final record has the exact coefficient sums and at least the error sum of the 112
checkpoints at `r`. -/
theorem sumOkR_spec (sd : SumData) (n r : ℕ) (h : sumOkR sd n r = true) :
    (∀ k, k < n + 1 → sdec ((dRec sd n r).getD k 0) =
      ∑ bi ∈ Finset.range 14, ∑ g ∈ Finset.range (ngD12 bi), sdec ((ckRec sd n bi g r).getD k 0)) ∧
    ∑ bi ∈ Finset.range 14, ∑ g ∈ Finset.range (ngD12 bi), (ckRec sd n bi g r).getD (n + 1) 0 ≤
      (dRec sd n r).getD (n + 1) 0 := by
  unfold sumOkR at h
  obtain ⟨hl, hv, he⟩ := accRecs_spec (Nat.add n 1) (recsAt sd n r) (List.replicate (Nat.add n 1) (0, 0)) 0
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hs, hle⟩ := h
  obtain ⟨hlen, hk⟩ := smAll_spec _ _ hs
  have hdl : (dRec sd n r).length = n + 2 := decRec_length _ _ _ _
  refine ⟨fun k hk' => ?_, ?_⟩
  · have h1 := hk k (by rw [List.length_take, hdl]; show k < min (n + 1) (n + 2); omega)
    rw [getD_take_of_lt _ (show k < Nat.add n 1 from hk')] at h1
    rw [h1, hv k (by rw [List.length_replicate]; exact hk')]
    have h0 : pval ((List.replicate (Nat.add n 1) ((0 : ℕ), (0 : ℕ))).getD k (0, 0)) = 0 := by
      have : (List.replicate (Nat.add n 1) ((0 : ℕ), (0 : ℕ))).getD k (0, 0) = (0, 0) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split_ifs <;> rfl
      rw [this]
      simp [pval]
    rw [h0, zero_add, recsAt_sum sd n r (fun rec => sdec ((rec.take (Nat.add n 1)).getD k 0))]
    refine Finset.sum_congr rfl (fun bi _ => Finset.sum_congr rfl (fun g _ => ?_))
    rw [getD_take_of_lt _ (show k < Nat.add n 1 from hk')]
  · rw [he, zero_add, recsAt_sum sd n r (fun rec => rec.getD (Nat.add n 1) 0)] at hle
    exact hle

theorem sumOk_spec {sd : SumData} {n r0 r1 : ℕ} (h : sumOk sd n r0 r1 = true) :
    ∀ r, r0 ≤ r → r < r1 → sumOkR sd n r = true := by
  intro r h0 h1
  unfold sumOk at h
  rw [List.all_eq_true] at h
  have := h r (List.mem_range.mpr h1)
  rw [show Nat.ble r0 r = true from Nat.ble_eq.mpr h0] at this
  simpa using this

/-! ## Per retained coordinate: the checkpointed sum of the 112 pieces -/

/-- The final sum QModel at coordinate `r` (point coefficients `sdec Dₖ 2^F / 2^S`, error `D_e 2^F / 2^S`). -/
noncomputable def BsumQ (n S : ℕ) (sd : SumData) (r : ℕ) : QModel n := ckQ n S sd.F (dRec sd n r)

theorem emptyGroupsOk_spec (h : emptyGroupsOk = true) (bi g r : ℕ) (hb : bi < 14) (hg : g < 8)
    (hng : ngD12 bi ≤ g) (hr : r < 100) : listAt [] (eTabG (Nat.add (Nat.mul 8 bi) g)) r = [] := by
  unfold emptyGroupsOk at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Nat.blt_eq] at h
  rcases h bi hb g hg with h1 | h1
  · omega
  · rw [listAt_eq]
    have hl : r < (eTabG (Nat.add (Nat.mul 8 bi) g)).length := by rw [eTabG_length]; exact hr
    have := h1 _ (List.getElem_mem hl)
    rw [List.getD_eq_getElem _ _ hl]
    simpa using this

/-- Pieces of the empty groups are `zeroTM` (hence `ok`). -/
theorem empty_piece (hE : emptyGroupsOk = true) (c : Ctx) (A : TM) (WT : ℕ → ℕ → TM) (bi g r : ℕ) (hb : bi < 14)
    (hg : g < 8) (hng : ngD12 bi ≤ g) (hr : r < 100) : blockTMgr c A WT bi g r = zeroTM := by
  unfold blockTMgr
  rw [emptyGroupsOk_spec hE bi g r hb hg hng hr]
  rfl

/-- The real functions of the empty pieces vanish. -/
theorem empty_gpk (hE : emptyGroupsOk = true) (s : ℝ → ℝ) (d : CellData)
    (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b) (bi : Fin 14) (g : Fin 8) (r : Fin 100)
    (hng : ngD12 bi ≤ g) (x : ℝ) : gpk s d hord (pieceEquiv (bi, g)) r x = 0 := by
  rw [gpk_piece]
  unfold gPiece
  have h1 := eTabG_eq bi bi.isLt g g.isLt r r.isLt
  rw [eTab_eq bi bi.isLt r r.isLt, emptyGroupsOk_spec hE bi g r bi.isLt g.isLt hng r.isLt] at h1
  rw [← h1]
  simp [gF]

/-- Per-block sum of the checkpoint QModels of the nonempty pieces. -/
noncomputable def blkQ (n S : ℕ) (sd : SumData) (bi r : ℕ) : QModel n :=
  ⟨fun k => ⟨∑ g ∈ Finset.range (ngD12 bi), (sdec ((ckRec sd n bi g r).getD k.val 0) : ℚ) * 2 ^ sd.F / 2 ^ S,
    ∑ g ∈ Finset.range (ngD12 bi), (sdec ((ckRec sd n bi g r).getD k.val 0) : ℚ) * 2 ^ sd.F / 2 ^ S⟩,
    ∑ g ∈ Finset.range (ngD12 bi), ((ckRec sd n bi g r).getD (n + 1) 0 : ℚ) * 2 ^ sd.F / 2 ^ S⟩

/-- **`Bsum_valid`: the final records enclose the sum of the 112 W0 contribution pieces**, for every retained
coordinate (`gpk` = `(w0Part_of …).g`). -/
theorem bsum_valid_of {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (s : ℝ → ℝ) {A : TM}
    (hA : Encl (mkCtx N S B W) A (fun x => aS (s x)))
    (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b) (sd : SumData) (hE : emptyGroupsOk = true)
    (n : ℕ) (hn : n ≤ N)
    (hok : ∀ (bi : Fin 14) (g : Fin 8) (r : Fin 100), g.val < ngD12 bi →
      (blockTMgr (mkCtx N S B W) A (WTp d (mkCtx N S B W) bi) bi g r).ok = true ∧
      ckOk (mkCtx N S B W) sd.F n (blockTMgr (mkCtx N S B W) A (WTp d (mkCtx N S B W) bi) bi g r)
        (ckRec sd n bi g r) = true)
    (hsum : ∀ r : Fin 100, sumOkR sd n r = true) (r : Fin 100) :
    (BsumQ n S sd r).asTM.Valid (fun x => ∑ ι, gpk s d hord ι r x) := by
  obtain ⟨hD, hEr⟩ := sumOkR_spec sd n r (hsum r)
  -- the piece functions as a double sum over the nonempty groups
  have hfun : (fun x => ∑ ι, gpk s d hord ι r x) = fun x => ∑ bi ∈ Finset.range 14, ∑ g ∈ Finset.range (ngD12 bi),
      (if h : bi < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0) := by
    funext x
    rw [← Fintype.sum_equiv pieceEquiv (fun p : Fin 14 × Fin 8 => gpk s d hord (pieceEquiv p) r x)
      (fun ι => gpk s d hord ι r x) (fun _ => rfl), Fintype.sum_prod_type,
      ← Fin.sum_univ_eq_sum_range (fun bi => ∑ g ∈ Finset.range (ngD12 bi),
        (if h : bi < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0))]
    refine Finset.sum_congr rfl (fun bi _ => ?_)
    have hng : ngD12 bi ≤ 8 := by fin_cases bi <;> decide
    have h1 : ∑ y : Fin 8, gpk s d hord (pieceEquiv (bi, y)) r x = ∑ g ∈ Finset.range 8,
        (if h : (bi : ℕ) < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0) := by
      rw [← Fin.sum_univ_eq_sum_range (fun g => (if h : (bi : ℕ) < 14 ∧ g < 8 then
        gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0)) 8]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [dif_pos ⟨bi.isLt, g.isLt⟩]
    rw [h1, ← Finset.sum_range_add_sum_Ico _ hng]
    have hz : ∑ g ∈ Finset.Ico (ngD12 bi) 8,
        (if h : (bi : ℕ) < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0) = 0 := by
      refine Finset.sum_eq_zero (fun g hg' => ?_)
      have hg2 := Finset.mem_Ico.mp hg'
      rw [dif_pos ⟨bi.isLt, hg2.2⟩]
      exact empty_gpk hE s d hord bi ⟨g, hg2.2⟩ r hg2.1 x
    rw [hz, add_zero]
  rw [hfun]
  -- inner sums (per block), then the outer sum
  have hinner : ∀ bi ∈ Finset.range 14, (blkQ n S sd bi r).asTM.Valid
      (fun x => ∑ g ∈ Finset.range (ngD12 bi),
        (if h : bi < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0)) := by
    intro bi hbi
    have hbi' := Finset.mem_range.mp hbi
    refine valid_sum (Finset.range (ngD12 bi)) (fun g => ckQ n S sd.F (ckRec sd n bi g r))
      (fun g x => if h : bi < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0)
      (fun g k => (sdec ((ckRec sd n bi g r).getD k.val 0) : ℚ) * 2 ^ sd.F / 2 ^ S) (fun _ _ => rfl)
      (fun g hg' => ?_) _ (fun k => rfl) (le_refl _)
    have hng : g < ngD12 bi := Finset.mem_range.mp hg'
    have hg8 : g < 8 := lt_of_lt_of_le hng (by interval_cases bi <;> decide)
    have hfg : (fun x => if h : bi < 14 ∧ g < 8 then gpk s d hord (pieceEquiv (⟨bi, h.1⟩, ⟨g, h.2⟩)) r x else 0) =
        gpk s d hord (pieceEquiv (⟨bi, hbi'⟩, ⟨g, hg8⟩)) r := by
      funext x; rw [dif_pos ⟨hbi', hg8⟩]
    rw [hfg, show gpk s d hord (pieceEquiv (⟨bi, hbi'⟩, ⟨g, hg8⟩)) r =
      gPiece s d.cell (blkOf d) hord ⟨bi, hbi'⟩ (D12G.gmap bi) 8 g r from funext (gpk_piece s d hord _ _ r)]
    have hok' := hok ⟨bi, hbi'⟩ ⟨g, hg8⟩ r hng
    have hE' := blockTMgr_sound hg s hA d.cell (blkOf d) hord _ ⟨bi, hbi'⟩ (hW_of hg d hord _) g hg8 r hok'.1
    exact ck_valid hg hE' sd.F n hn _ (by unfold ckRec; rw [decRec_length]; show n + 1 ≤ n + 2; omega) hok'.2
  refine valid_sum (Finset.range 14) (fun bi => blkQ n S sd bi r) _
    (fun bi k => ∑ g ∈ Finset.range (ngD12 bi), (sdec ((ckRec sd n bi g r).getD k.val 0) : ℚ) * 2 ^ sd.F / 2 ^ S)
    (fun _ _ => rfl) hinner (BsumQ n S sd r) (fun k => ?_) ?_
  · show (⟨_, _⟩ : QInterval) = _
    rw [hD k.val k.isLt]
    push_cast
    simp only [Finset.sum_mul, Finset.sum_div]
  · show ∑ bi ∈ Finset.range 14, ∑ g ∈ Finset.range (ngD12 bi),
        ((ckRec sd n bi g r).getD (n + 1) 0 : ℚ) * 2 ^ sd.F / 2 ^ S ≤ ((dRec sd n r).getD (n + 1) 0 : ℚ) * 2 ^ sd.F / 2 ^ S
    simp only [← Finset.sum_div, ← Finset.sum_mul]
    have : (∑ bi ∈ Finset.range 14, ∑ g ∈ Finset.range (ngD12 bi), ((ckRec sd n bi g r).getD (n + 1) 0 : ℚ)) ≤
        ((dRec sd n r).getD (n + 1) 0 : ℚ) := by exact_mod_cast hEr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)) (by positivity)

#print axioms ck_valid
#print axioms sumOkR_spec
#print axioms bsum_valid_of
#print axioms empty_piece
#print axioms sumOk_spec

end ThomsonCompact.CoeffMap
