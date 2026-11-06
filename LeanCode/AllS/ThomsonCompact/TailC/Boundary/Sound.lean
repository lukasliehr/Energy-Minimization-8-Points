import ThomsonCompact.TailC.StageReal
import ThomsonCompact.TailC.Boundary.Leaf
import ThomsonCompact.TailC.Boundary.LeafTabs
import ThomsonCompact.TailC.Boundary.ContactData
import AllS.Units.N_GI.N_boundary_infeasible.N_direct_certificate

/-!
# TailC.Boundary: the compact boundary SOS certificate (workstream TC1)

`boundary_sos_infeasible_compact : BoundarySOSInfeasible` — the same statement as the old
`Blueprint.Thomson.Tail.Implementation.boundary_sos_infeasible`, through the same interface lemma
`boundary_infeasible_of_bounded_residual`, with the multipliers given explicitly as sums of squares of the forms
stored in `DataF`/`DataE` (generated from the paper's 539 factor entries by `tools/tailc_boundary_export.py`):

* `freeM  = Σ_k (H_k(y)/Dh)²`, `upperM = Σ_m (λᵘ_m(y)/Du)²`, `lowerM = Σ_m (λˡ_m(y)/Du)²`,
  `edgeM e = Σ_m (λᵉ_m(y)/De)²` (`σ_d ∘ S^{-i}`), all nonnegative by construction;
* `residualM := -1 - (freeM + upperM (1 - N) + lowerM (N - ℓ) + Σ_e edgeM e · g_e)`, so the identity is `ring`;
* `|residualM y| < 1` on the cube: `bD · residualM = -Σ_γ κ(C_γ) M4_γ` with the 2380 coefficients `C_γ` computed by
  the kernel leaf `checkAll_true` (Level 1: 18 Gram stages, Level 2: 124 products), the index tables
  (`LeafTabs`), the exact contact data (`ContactData`, against the old exact geometry), and the `√2` bracket.
-/

namespace ThomsonCompact.TailC.Boundary
open ThomsonCompact.TailC Finset
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

/-! ## Generic facts -/

theorem allLt_spec (f : ℕ → Bool) : ∀ n, allLt n f = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : (allLt n f && f n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allLt_spec f n h'.1 k hk
    · exact h'.2

theorem mkL_go {α : Type} (f : ℕ → α) : ∀ (n k : ℕ),
    (Nat.rec (motive := fun _ => Nat → List α) (fun _ => []) (fun _ ih k => f k :: ih (Nat.add k 1)) n k) =
      (List.range n).map (fun j => f (k + j))
  | 0, k => rfl
  | n + 1, k => by
    show f k :: (Nat.rec (motive := fun _ => Nat → List α) (fun _ => []) (fun _ ih k => f k :: ih (Nat.add k 1))
      n (Nat.add k 1)) = _
    rw [mkL_go f n, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left (fun j _ => ?_)
    simp only [Function.comp, nadd]; congr 1; omega

theorem mkL_eq {α : Type} (f : ℕ → α) (n : ℕ) : mkL f n = (List.range n).map f := by
  rw [mkL, mkL_go]; simp

theorem minN_eq (a b : ℕ) : minN a b = min a b := by
  simp only [minN, brec, nble, decide_eq_true_iff]; split_ifs with h <;> omega
theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  simp only [maxN, brec, nble, decide_eq_true_iff]; split_ifs with h <;> omega

theorem fld_lt (x off w : ℕ) : fld x off w < 2 ^ w := by
  rw [fld_eq]; exact Nat.mod_lt _ (by positivity)

theorem gamF_eq (P : SP) (s t : ℕ) : gamF P s t = gamD P s t := by
  simp only [gamF, gamD, dig, fld_eq, nmul]

/-! ## Monomials -/

/-- Homogeneous coordinates: `x_0 = 1`, `x_(j+1) = y_j`. -/
noncomputable def xa (y : Fin 13 → ℝ) (a : ℕ) : ℝ :=
  if a = 0 then 1 else if h : a - 1 < 13 then y ⟨a - 1, h⟩ else 0

/-- Quadratic monomial `s`. -/
noncomputable def mq (y : Fin 13 → ℝ) (s : ℕ) : ℝ := xa y (qa s) * xa y (qb s)

/-- Quartic monomial `γ`. -/
noncomputable def M4 (y : Fin 13 → ℝ) (γ : ℕ) : ℝ :=
  xa y (fld (r4 γ) 0 4) * xa y (fld (r4 γ) 4 4) * xa y (fld (r4 γ) 8 4) * xa y (fld (r4 γ) 12 4)

theorem xa_minmax (y : Fin 13 → ℝ) (a b : ℕ) : xa y (min a b) * xa y (max a b) = xa y a * xa y b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

theorem abs_xa_le (y : Fin 13 → ℝ) (hy : ∀ j, |y j| ≤ 1) (a : ℕ) : |xa y a| ≤ 1 := by
  unfold xa; split_ifs
  · simp
  · exact hy _
  · simp

theorem abs_M4_le (y : Fin 13 → ℝ) (hy : ∀ j, |y j| ≤ 1) (γ : ℕ) : |M4 y γ| ≤ 1 := by
  unfold M4
  rw [abs_mul, abs_mul, abs_mul]
  have h := abs_xa_le y hy
  exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (h _) (abs_nonneg _) (h _)) (abs_nonneg _) (h _)) (abs_nonneg _) (h _)

theorem q2_facts : qa 0 = 0 ∧ qb 0 = 0 ∧ ∀ s < 105, qa s ≤ qb s ∧ qb s ≤ 13 := by
  have h := q2Ok_true
  simp only [q2Ok, Bool.and_eq_true, nbeq, decide_eq_true_iff] at h
  refine ⟨h.1.1, h.1.2, fun s hs => ?_⟩
  have := allLt_spec _ 105 h.2 s hs
  simpa only [Bool.and_eq_true, nble, decide_eq_true_iff] using this

theorem g1_facts (a b : ℕ) (ha : a < 14) (hb : b < 14) :
    gamD sp1 a b < 105 ∧ qa (gamD sp1 a b) = min a b ∧ qb (gamD sp1 a b) = max a b := by
  have h := allLt_spec _ 14 (allLt_spec _ 14 g1Ok_true a ha) b hb
  simp only [Bool.and_eq_true, nbeq, nblt, decide_eq_true_iff, gamF_eq, minN_eq, maxN_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem xa_mul_g1 (y : Fin 13 → ℝ) (a b : ℕ) (ha : a < 14) (hb : b < 14) :
    xa y a * xa y b = mq y (gamD sp1 a b) := by
  obtain ⟨_, h1, h2⟩ := g1_facts a b ha hb
  rw [mq, h1, h2, xa_minmax]

theorem merge4_fields (a b c d : ℕ) (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    fld (merge4 a b c d) 0 4 = min a c ∧ fld (merge4 a b c d) 4 4 = min (min b d) (max a c) ∧
    fld (merge4 a b c d) 8 4 = max (min b d) (max a c) ∧ fld (merge4 a b c d) 12 4 = max b d := by
  simp only [merge4, minN_eq, maxN_eq, nadd, nmul, fld_eq]
  norm_num
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem g2_facts (s t : ℕ) (hs : s < 105) (ht : t < 105) :
    gamD sp2 s t < 2380 ∧ merge4 (qa s) (qb s) (qa t) (qb t) = r4 (gamD sp2 s t) := by
  have h := allLt_spec _ 105 (allLt_spec _ 105 g2Ok_true s hs) t ht
  simp only [Bool.and_eq_true, nbeq, nblt, decide_eq_true_iff, gamF_eq, nadd, zero_add] at h
  exact h

theorem mq_mul_g2 (y : Fin 13 → ℝ) (s t : ℕ) (hs : s < 105) (ht : t < 105) :
    mq y s * mq y t = M4 y (gamD sp2 s t) := by
  obtain ⟨_, h⟩ := g2_facts s t hs ht
  have l16 : ∀ x, qa x < 16 ∧ qb x < 16 := fun x =>
    ⟨by have := fld_lt q2tab (Nat.mul 8 x) 4; norm_num at this; exact this,
     by have := fld_lt q2tab (Nat.add (Nat.mul 8 x) 4) 4; norm_num at this; exact this⟩
  obtain ⟨f0, f1, f2, f3⟩ := merge4_fields _ _ _ _ (l16 s).1 (l16 s).2 (l16 t).1 (l16 t).2
  rw [M4, ← h, f0, f1, f2, f3, mq, mq]
  have e1 := xa_minmax y (min (qb s) (qb t)) (max (qa s) (qa t))
  have e2 := xa_minmax y (qa s) (qa t)
  have e3 := xa_minmax y (qb s) (qb t)
  calc xa y (qa s) * xa y (qb s) * (xa y (qa t) * xa y (qb t))
      = (xa y (qa s) * xa y (qa t)) * (xa y (qb s) * xa y (qb t)) := by ring
    _ = (xa y (min (qa s) (qa t)) * xa y (max (qa s) (qa t))) *
          (xa y (min (qb s) (qb t)) * xa y (max (qb s) (qb t))) := by rw [e2, e3]
    _ = xa y (min (qa s) (qa t)) * (xa y (min (qb s) (qb t)) * xa y (max (qa s) (qa t))) *
          xa y (max (qb s) (qb t)) := by ring
    _ = _ := by rw [← e1]; ring

/-! ## Stage facts from the leaf -/

theorem checks : l1U.1 = true ∧ l1L.1 = true ∧ (∀ e < 16, (l1E e).1 = true) ∧ l2.1 = true ∧
    bndSum l2.2 < sqQ * bD := by
  have h := checkAll_true
  simp only [checkAll, Bool.and_eq_true, nblt, decide_eq_true_iff, nmul] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, allLt_spec _ 16 h3, h4, h5⟩

theorem sp1_W : 1 ≤ sp1.W := by decide
theorem sp1_W2 : 1 ≤ sp1.W2 := by decide
theorem sp2_W : 1 ≤ sp2.W := by decide
theorem sp2_W2 : 1 ≤ sp2.W2 := by decide

theorem gram_sv (src : ℕ → ℕ) (y : Fin 13 → ℝ) (hok : (stage sp1 (gramTerms src)).1 = true) :
    sv (stage sp1 (gramTerms src)).2 (mq y) = ∑ m ∈ range 14, (sv (decSV (src m)) (xa y)) ^ 2 := by
  rw [stage_real sp1 (gramTerms src) sp1_W sp1_W2 (fun i hi j hj => (g1_facts i j hi hj).1) hok (xa y) (mq y)
    (fun i hi j hj => xa_mul_g1 y i j hi hj), gramTerms, mkL_eq, List.map_map, lsum_range]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp [Function.comp, pow_two]

/-! ## The constraint lists -/

/-- `qWeight` scaled by 4 (as in `NormKernels.qWeight`). -/
def qWn : Fin 13 → ℕ × ℕ := ![(8, 9), (4, 1), (4, 1), (8, 9), (8, 9), (4, 1), (4, 1), (8, 9), (8, 9), (4, 2), (4, 2),
  (4, 1), (8, 9)]

theorem qw4_eq : ∀ j : Fin 13, qw4 j.val = qWn j := by decide +kernel

theorem diag_eq (j : Fin 13) : ((qWn j).1 : ℝ) + ((qWn j).2 : ℝ) * Real.sqrt 2 = 4 * boundaryDiagonal j := by
  fin_cases j <;> simp [qWn, boundaryDiagonal, boundaryM, boundaryZ, boundaryT] <;> ring

theorem d_facts (j : ℕ) (hj : j < 13) : qa (dIdx j) = j + 1 ∧ qb (dIdx j) = j + 1 := by
  have h := allLt_spec _ 13 dOk_true j hj
  simpa only [Bool.and_eq_true, nbeq, nadd, decide_eq_true_iff] using h

theorem mq_dIdx (y : Fin 13 → ℝ) (j : Fin 13) : mq y (dIdx j.val) = y j ^ 2 := by
  obtain ⟨h1, h2⟩ := d_facts j.val j.isLt
  rw [mq, h1, h2]
  simp [xa, pow_two]

theorem mq_zero (y : Fin 13 → ℝ) : mq y 0 = 1 := by
  rw [mq, q2_facts.1, q2_facts.2.1]; simp [xa]

theorem sv_cons (e : Ent) (l : List Ent) (m : ℕ → ℝ) : sv (e :: l) m = κ (ev e) * m e.1 + sv l m := by
  simp [sv]

theorem κ_ev (e : Ent) : κ (ev e) = smv e.2.1 + smv e.2.2 * Real.sqrt 2 := by
  rw [κ_apply]; rfl

theorem sv_diag (y : Fin 13 → ℝ) (f : ℕ → Ent) (hf : ∀ j, (f j).1 = dIdx j) :
    sv (mkL f 13) (mq y) = ∑ j : Fin 13, κ (ev (f j.val)) * y j ^ 2 := by
  rw [sv, mkL_eq, List.map_map, lsum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Function.comp, hf, mq_dIdx]

theorem sv_nuL (y : Fin 13 → ℝ) : sv nuL (mq y) = 4 * (1 - boundaryNormPolynomial y) := by
  rw [nuL, sv_cons, sv_diag y _ (fun j => rfl), mq_zero, boundaryNormPolynomial, mul_sub, mul_one, Finset.mul_sum]
  have h0 : κ (ev (0, (false, 4), (false, 0))) = 4 := by rw [κ_ev]; simp [smv]
  rw [h0, mul_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [κ_ev]
  simp only [smv, if_true]
  rw [qw4_eq j]
  have := diag_eq j
  push_cast
  linear_combination (-(y j ^ 2)) * this

theorem sv_nlL (y : Fin 13 → ℝ) : sv nlL (mq y) = 14884 * (boundaryNormPolynomial y - 3620 / 3721) := by
  rw [nlL, sv_cons, sv_diag y _ (fun j => rfl), mq_zero, boundaryNormPolynomial, mul_sub, Finset.mul_sum]
  have h0 : κ (ev (0, (true, 14480), (false, 0))) = -14480 := by rw [κ_ev]; simp [smv]
  rw [h0, mul_one, add_comm, sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [κ_ev]
    simp only [smv, Bool.false_eq_true, if_false, nmul]
    rw [qw4_eq j]
    have := diag_eq j
    push_cast
    linear_combination (3721 * y j ^ 2) * this
  · norm_num

theorem sv_oneL (y : Fin 13 → ℝ) : sv oneL (mq y) = 1 := by
  simp [oneL, sv, κ_ev, smv, mq_zero]

/-! ## The contact bridge -/

theorem lsum_div {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map f).sum / c = (l.map fun a => f a / c).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, add_div, ih]

theorem abs_lsum_le_r {α : Type*} (l : List α) (f : α → ℝ) : |(l.map f).sum| ≤ (l.map fun a => |f a|).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem wordEval_word (y : Fin 13 → ℝ) (s : ℕ) (hs : s < 105) :
    Blueprint.CAP.BoundaryDirect.wordEval (word s) y = mq y s := by
  obtain ⟨_, _, h⟩ := q2_facts
  obtain ⟨hab, hb⟩ := h s hs
  simp only [word, mq, nbeq, nsub, Bool.cond_decide]
  by_cases h0 : qb s = 0
  · have ha : qa s = 0 := by omega
    simp [h0, ha, xa, Blueprint.CAP.BoundaryDirect.wordEval]
  · by_cases ha : qa s = 0
    · simp only [h0, ha, if_false, if_true]
      simp [Blueprint.CAP.BoundaryDirect.wordEval, xa, h0, fin13, Nat.mod_eq_of_lt (show qb s - 1 < 13 by omega),
        show qb s - 1 < 13 by omega]
    · simp only [h0, ha, if_false]
      simp [Blueprint.CAP.BoundaryDirect.wordEval, xa, h0, ha, fin13, Nat.mod_eq_of_lt (show qb s - 1 < 13 by omega),
        Nat.mod_eq_of_lt (show qa s - 1 < 13 by omega), show qb s - 1 < 13 by omega, show qa s - 1 < 13 by omega]

theorem eval_toPoly (y : Fin 13 → ℝ) (l : List Ent) (hl : ∀ e ∈ l, e.1 < 105) :
    Blueprint.CAP.BoundaryDirect.eval (toPoly l) y = sv l (mq y) / dG := by
  rw [Blueprint.CAP.BoundaryDirect.eval, toPoly, List.map_map, sv, lsum_div]
  refine lsum_congr _ _ _ (fun e he => ?_)
  simp only [Function.comp, Blueprint.CAP.BoundaryDirect.qeval, wordEval_word y e.1 (hl e he), κ_ev]
  simp only [smvQ, smv, Bool.cond_eq_ite]
  split_ifs <;> push_cast <;> ring

theorem gC_idx (k : ℕ) (hk : k < 16) : ∀ e ∈ decSV (gC k), e.1 < 105 := by
  have hidx := (stage_sound sp2 l2Terms sp2_W sp2_W2 (fun i hi j hj => (g2_facts i j hi hj).1) checks.2.2.2.1).2
  refine (hidx (decSV (gC k), (l1E k).2, cE) ?_).1
  simp only [l2Terms, List.mem_cons, List.mem_append, mkL_eq, List.mem_map, List.mem_range]
  right; right; right; right
  exact ⟨k, hk, rfl⟩

theorem contact_sv (e : ContactIndex) (y : Fin 13 → ℝ) :
    boundaryContactPolynomial e y = sv (decSV (gC (2 * e.1.val + e.2.val))) (mq y) / dG := by
  rw [← Blueprint.CAP.BoundaryDirect.contactValue_eval, contact_data e]
  exact eval_toPoly y _ (gC_idx _ (by have h1 := e.1.isLt; have h2 := e.2.isLt; simp only [nadd, nmul]; omega))

/-! ## The multipliers -/

def bDh : ℝ := 2000000000000000
def bDu : ℝ := 1000000000000000

/-- The free multiplier `Σ_k (H_k / Dh)²`. -/
noncomputable def freeM (y : Fin 13 → ℝ) : ℝ := ∑ k ∈ range 105, (sv (decSV (hF k)) (mq y) / bDh) ^ 2

/-- The upper annulus multiplier. -/
noncomputable def upperM (y : Fin 13 → ℝ) : ℝ := ∑ m ∈ range 14, (sv (decSV (lamU m)) (xa y) / bDu) ^ 2

/-- The lower annulus multiplier. -/
noncomputable def lowerM (y : Fin 13 → ℝ) : ℝ := ∑ m ∈ range 14, (sv (decSV (lamL m)) (xa y) / bDu) ^ 2

/-- The edge multipliers (index `k = 2 i + d'`). -/
noncomputable def edgeK (k : ℕ) (y : Fin 13 → ℝ) : ℝ :=
  ∑ m ∈ range 14, (sv (decSV (lamE (Nat.add (Nat.mul 14 k) m))) (xa y) / bDh) ^ 2

noncomputable def edgeM (e : ContactIndex) (y : Fin 13 → ℝ) : ℝ := edgeK (2 * e.1.val + e.2.val) y

/-- The residual (by definition, so that the identity holds). -/
noncomputable def residualM (y : Fin 13 → ℝ) : ℝ :=
  -1 - (freeM y + upperM y * (1 - boundaryNormPolynomial y) + lowerM y * (boundaryNormPolynomial y - 3620 / 3721) +
    ∑ e, edgeM e y * boundaryContactPolynomial e y)

theorem sum_range_pairs (F : ℕ → ℝ) : ∀ n, ∑ k ∈ range (2 * n), F k = ∑ i ∈ range n, (F (2 * i) + F (2 * i + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, sum_range_pairs F n,
      Finset.sum_range_succ]
    ring

theorem sum_contact (F : ℕ → ℝ) : ∑ e : ContactIndex, F (2 * e.1.val + e.2.val) = ∑ k ∈ range 16, F k := by
  rw [Fintype.sum_prod_type, show (16 : ℕ) = 2 * 8 from rfl, sum_range_pairs,
    ← Fin.sum_univ_eq_sum_range (fun i => F (2 * i) + F (2 * i + 1))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_two]; simp

theorem free_part (y : Fin 13 → ℝ) : (bD : ℝ) * freeM y =
    ∑ k ∈ range 105, (cF : ℝ) * (sv (decSV (hF k)) (mq y) * sv (decSV (hF k)) (mq y)) := by
  rw [freeM, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [bD, cF, bDh, div_pow]
  push_cast
  field_simp
  ring

theorem gram_part (D c d : ℝ) (hD : D ≠ 0) (hc : c * d * D ^ 2 = 1) (S : ℕ → ℝ) (n : ℕ) (X : ℝ) :
    (∑ m ∈ range n, (S m / D) ^ 2) * X = c * (d * X * ∑ m ∈ range n, S m ^ 2) := by
  have : ∑ m ∈ range n, (S m / D) ^ 2 = (∑ m ∈ range n, S m ^ 2) / D ^ 2 := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun m _ => by rw [div_pow])
  rw [this]
  field_simp
  linear_combination (-(X * ∑ m ∈ range n, S m ^ 2)) * hc

theorem edge_part (y : Fin 13 → ℝ) : (bD : ℝ) * ∑ e : ContactIndex, edgeM e y * boundaryContactPolynomial e y =
    ∑ k ∈ range 16, (cE : ℝ) * (sv (decSV (gC k)) (mq y) *
      ∑ m ∈ range 14, (sv (decSV (lamE (Nat.add (Nat.mul 14 k) m))) (xa y)) ^ 2) := by
  have h : ∀ e : ContactIndex, edgeM e y * boundaryContactPolynomial e y =
      edgeK (2 * e.1.val + e.2.val) y * (sv (decSV (gC (2 * e.1.val + e.2.val))) (mq y) / dG) := by
    intro e; rw [contact_sv]; rfl
  have hs := sum_contact (fun k => edgeK k y * (sv (decSV (gC k)) (mq y) / dG))
  rw [Finset.sum_congr rfl (fun e _ => h e), hs, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [edgeK]
  rw [← mul_assoc, mul_comm (bD : ℝ), mul_assoc, ← mul_div_assoc,
    gram_part bDh ((cE : ℝ) * dG / bD) 1 (by norm_num [bDh]) (by norm_num [bD, cE, dG, bDh])]
  have hdG : (dG : ℝ) ≠ 0 := by norm_num [dG]
  have hbD : (bD : ℝ) ≠ 0 := by norm_num [bD]
  field_simp

/-- `bD · residual = -Σ_γ κ(C_γ) M4_γ`. -/
theorem residual_identity (y : Fin 13 → ℝ) : (bD : ℝ) * residualM y = -sv l2.2 (M4 y) := by
  obtain ⟨hU, hL, hE, h2, _⟩ := checks
  have hsv : sv l2.2 (M4 y) = _ := stage_real sp2 l2Terms sp2_W sp2_W2 (fun i hi j hj => (g2_facts i j hi hj).1) h2
    (mq y) (M4 y) (fun i hi j hj => mq_mul_g2 y i j hi hj)
  have hgU := gram_sv lamU y hU
  have hgL := gram_sv lamL y hL
  have hgE : ∀ k ∈ range 16, (cE : ℝ) * (sv (decSV (gC k)) (mq y) * sv (l1E k).2 (mq y)) =
      (cE : ℝ) * (sv (decSV (gC k)) (mq y) *
        ∑ m ∈ range 14, (sv (decSV (lamE (Nat.add (Nat.mul 14 k) m))) (xa y)) ^ 2) :=
    fun k hk => by rw [show (l1E k).2 = (stage sp1 (gramTerms fun m => lamE (Nat.add (Nat.mul 14 k) m))).2 from rfl,
      gram_sv _ y (hE k (Finset.mem_range.1 hk))]
  have hup : (bD : ℝ) * (upperM y * (1 - boundaryNormPolynomial y)) =
      (cU : ℝ) * (sv nuL (mq y) * sv l1U.2 (mq y)) := by
    rw [sv_nuL, show (l1U.2 : List Ent) = (stage sp1 (gramTerms lamU)).2 from rfl, hgU, upperM,
      gram_part bDu ((cU : ℝ) / bD) 4 (by norm_num [bDu]) (by norm_num [bD, cU, bDu])]
    field_simp; norm_num [bD]; ring
  have hlo : (bD : ℝ) * (lowerM y * (boundaryNormPolynomial y - 3620 / 3721)) =
      (cL : ℝ) * (sv nlL (mq y) * sv l1L.2 (mq y)) := by
    rw [sv_nlL, show (l1L.2 : List Ent) = (stage sp1 (gramTerms lamL)).2 from rfl, hgL, lowerM,
      gram_part bDu ((cL : ℝ) / bD) 14884 (by norm_num [bDu]) (by norm_num [bD, cL, bDu])]
    field_simp; norm_num [bD]; ring
  rw [hsv, l2Terms]
  simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append, mkL_eq, List.map_map, lsum_range,
    Function.comp]
  rw [Finset.sum_congr rfl hgE, ← edge_part, ← hup, ← hlo, ← free_part, sv_oneL, residualM]
  ring

/-! ## The residual bound -/

theorem abs_le_max_of {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : |b| ≤ max |a| |c| := by
  rcases le_total 0 b with h | h
  · exact le_max_of_le_right (by rw [abs_of_nonneg h]; exact h2.trans (le_abs_self c))
  · exact le_max_of_le_left (by rw [abs_of_nonpos h]; exact (neg_le_neg h1).trans (neg_le_abs a))

theorem linB_eq (q p : ℕ) (e : Ent) : (linB q p e : ℝ) = |(q : ℝ) * smv e.2.1 + p * smv e.2.2| := by
  obtain ⟨i, ⟨su, mu⟩, ⟨sv, mv⟩⟩ := e
  have hd : ∀ a b : ℕ, (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - b| := by
    intro a b
    rcases le_total a b with h | h
    · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.2 (Nat.cast_le.2 h))]; ring
    · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.2 (Nat.cast_le.2 h))]
  have hnn : (0 : ℝ) ≤ q * mu + p * mv := by positivity
  cases su <;> cases sv
  · show ((Nat.add (Nat.mul q mu) (Nat.mul p mv) : ℕ) : ℝ) = _
    simp only [smv, nadd, nmul, Bool.false_eq_true, if_false]; push_cast; rw [abs_of_nonneg hnn]
  · show ((Nat.add (Nat.sub (Nat.mul q mu) (Nat.mul p mv)) (Nat.sub (Nat.mul p mv) (Nat.mul q mu)) : ℕ) : ℝ) = _
    simp only [smv, nadd, nsub, nmul, Bool.false_eq_true, if_false, if_true]
    rw [hd]; push_cast; congr 1; ring
  · show ((Nat.add (Nat.sub (Nat.mul q mu) (Nat.mul p mv)) (Nat.sub (Nat.mul p mv) (Nat.mul q mu)) : ℕ) : ℝ) = _
    simp only [smv, nadd, nsub, nmul, Bool.false_eq_true, if_false, if_true]
    rw [hd, ← abs_neg]; push_cast; congr 1; ring
  · show ((Nat.add (Nat.mul q mu) (Nat.mul p mv) : ℕ) : ℝ) = _
    simp only [smv, nadd, nmul, if_true]; push_cast
    rw [show (q : ℝ) * -(mu : ℝ) + p * -(mv : ℝ) = -((q : ℝ) * mu + p * mv) by ring, abs_neg, abs_of_nonneg hnn]

theorem sqrt2_bracket : (sqL : ℝ) / sqQ ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (sqU : ℝ) / sqQ := by
  have hq : (0 : ℝ) < sqQ := by norm_num [sqQ]
  constructor
  · rw [Real.le_sqrt (by positivity) (by norm_num), div_pow, div_le_iff₀ (by positivity)]
    norm_num [sqL, sqQ]
  · rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
    norm_num [sqU, sqQ]

theorem abs_κ_le (e : Ent) : |κ (ev e)| ≤ (maxN (linB sqQ sqL e) (linB sqQ sqU e) : ℝ) / sqQ := by
  have hq : (0 : ℝ) < sqQ := by norm_num [sqQ]
  obtain ⟨hL, hU⟩ := sqrt2_bracket
  rw [maxN_eq, Nat.cast_max, linB_eq, linB_eq, κ_ev, le_div_iff₀ hq]
  set u : ℝ := ((smv e.2.1 : ℤ) : ℝ)
  set v : ℝ := ((smv e.2.2 : ℤ) : ℝ)
  have hL' : (sqL : ℝ) ≤ sqQ * Real.sqrt 2 := by rw [div_le_iff₀ hq] at hL; linarith
  have hU' : sqQ * Real.sqrt 2 ≤ (sqU : ℝ) := by rw [le_div_iff₀ hq] at hU; linarith
  have key : |sqQ * u + sqQ * Real.sqrt 2 * v| ≤ max |sqQ * u + sqL * v| |sqQ * u + sqU * v| := by
    rcases le_total 0 v with hv | hv
    · exact abs_le_max_of (by nlinarith) (by nlinarith)
    · rw [max_comm]; exact abs_le_max_of (by nlinarith) (by nlinarith)
  calc |u + v * Real.sqrt 2| * sqQ = |sqQ * u + sqQ * Real.sqrt 2 * v| := by
        rw [← abs_of_pos hq, ← abs_mul, abs_of_pos hq]; congr 1; ring
    _ ≤ _ := key

theorem bndSum_eq : ∀ l : List Ent, bndSum l = (l.map fun e => maxN (linB sqQ sqL e) (linB sqQ sqU e)).sum
  | [] => rfl
  | e :: l => by
    show Nat.add (maxN (linB sqQ sqL e) (linB sqQ sqU e)) (bndSum l) = _
    rw [bndSum_eq l]; simp [nadd]

theorem abs_sv_le (y : Fin 13 → ℝ) (hy : ∀ j, |y j| ≤ 1) (l : List Ent) :
    |sv l (M4 y)| ≤ (bndSum l : ℝ) / sqQ := by
  rw [sv, bndSum_eq, Nat.cast_list_sum, List.map_map, lsum_div]
  refine (abs_lsum_le_r _ _).trans (List.sum_le_sum (fun e _ => ?_))
  rw [abs_mul]
  calc |κ (ev e)| * |M4 y e.1| ≤ |κ (ev e)| * 1 := by gcongr; exact abs_M4_le y hy _
    _ ≤ _ := by rw [mul_one]; exact abs_κ_le e

theorem residual_small (y : Fin 13 → ℝ) (hy : ∀ j, |y j| ≤ 1) : |residualM y| < 1 := by
  have hid := residual_identity y
  have hbD : (0 : ℝ) < bD := by norm_num [bD]
  have hq : (0 : ℝ) < sqQ := by norm_num [sqQ]
  have hb : (bndSum l2.2 : ℝ) < sqQ * bD := by exact_mod_cast checks.2.2.2.2
  have h2 : |sv l2.2 (M4 y)| < bD := by
    calc _ ≤ (bndSum l2.2 : ℝ) / sqQ := abs_sv_le y hy l2.2
      _ < bD := by rw [div_lt_iff₀ hq]; linarith
  have h3 : residualM y = -sv l2.2 (M4 y) / bD := by
    field_simp; linarith
  rw [h3, abs_div, abs_neg, abs_of_pos hbD, div_lt_one hbD]
  exact h2

/-- **The boundary SOS exclusion**, compact proof: the same statement as
`Blueprint.Thomson.Tail.Implementation.boundary_sos_infeasible`. -/
theorem boundary_sos_infeasible_compact : BoundarySOSInfeasible := by
  apply boundary_infeasible_of_bounded_residual freeM upperM lowerM edgeM residualM
  · intro y; unfold freeM; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  · intro y; unfold upperM; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  · intro y; unfold lowerM; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  · intro e y; unfold edgeM edgeK; exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  · intro y; unfold residualM; ring
  · exact residual_small

#print axioms boundary_sos_infeasible_compact

end ThomsonCompact.TailC.Boundary
