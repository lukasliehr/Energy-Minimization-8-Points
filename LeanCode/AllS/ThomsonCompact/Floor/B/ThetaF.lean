import ThomsonCompact.Floor.Check

/-!
# Fast short-metric check (F3g; Init only)

`checkTheta` (F3a) evaluates `θ = max_i Σ_j |F_ij + F_ji|`, `F = Zi Kz - 2^sc 1`, entry by entry: every `F_ij` sums
`n` products whose `Kz` entries are read with `kl.getD (l(l-1)/2 + j)` (a walk of length `O(n²)`), so the leaf costs
`O(n⁵)` kernel steps — 21 s / 2.2 GB for the D14 block `M0_standard` (`n = 32`), minutes for D16/D18 (`n = 47`, `65`).
`checkThetaF` computes the same number in `O(n³)` products: the columns of `Kz` once in `O(n²)` (`kzCols`: the dense rows
by one sequential walk of `kl`, `kzRowsAux`, then one transpose), then `F_ij` as one dot product (`dotZ`); `checkThetaR`
does it for a range of rows (leaves of `O(k n²)`). `checkThetaF_imp`: a passing `checkThetaF` is
a passing `checkTheta` (`thetaNumF_eq`: the two numbers are equal for the decoded short metric `zMatrix`).
-/

namespace ThomsonCompact.Floor

/-- `Σ_k x_k y_k` over the common prefix -/
def dotZ : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dotZ xs ys
  | _, _ => 0

/-- the first `l` entries of `r` times `s` (zeros past its end) -/
def lowerRow (s : Int) : Nat → List Int → List Int
  | 0, _ => []
  | l + 1, x :: xs => x * s :: lowerRow s l xs
  | l + 1, [] => 0 :: lowerRow s l []

/-- dense row `l < n` of `Kz` (scale `2^-mb`): the strict lower entries `kl` (row major) times `2^(mb - bits)`, the
diagonal `2^(mb + ex_l)`, zeros above the diagonal -/
def kzRow (n bits mb : Nat) (ex kl : List Int) (l : Nat) : List Int :=
  lowerRow ((2 : Int) ^ (mb - bits)) l (kl.drop (l * (l - 1) / 2)) ++
    ((2 : Int) ^ (Int.toNat ((mb : Int) + ex.getD l 0)) :: List.replicate (n - l - 1) 0)

/-- the columns `j < n` of a list of rows -/
def kCols (n : Nat) (KR : List (List Int)) : List (List Int) :=
  (List.range n).map fun j => KR.map fun row => row.getD j 0

/-- the dense rows `l, l+1, …` (`m` of them) of `Kz` from the remaining strict lower entries `r` (row `l` takes `l`) -/
def kzRowsAux (n bits mb : Nat) (ex : List Int) : Nat → Nat → List Int → List (List Int)
  | 0, _, _ => []
  | m + 1, l, r =>
    (lowerRow ((2 : Int) ^ (mb - bits)) l r ++
      ((2 : Int) ^ (Int.toNat ((mb : Int) + ex.getD l 0)) :: List.replicate (n - l - 1) 0)) ::
      kzRowsAux n bits mb ex m (l + 1) (r.drop l)

/-- transpose of a list of rows of length `n` -/
def transposeN (n : Nat) (rows : List (List Int)) : List (List Int) :=
  rows.foldr (fun row cols => List.zipWith (fun x c => x :: c) row cols) (List.replicate n [])

/-- the columns of `Kz` in `O(n²)`: one sequential walk of `kl`, then one transpose -/
def kzCols (n bits mb : Nat) (ex kl : List Int) : List (List Int) :=
  transposeN n (kzRowsAux n bits mb ex n 0 kl)

/-- `F_ij` from the rows of `Zi` and the columns of `Kz` -/
def fentF (Z KC : List (List Int)) (sc i j : Nat) : Int :=
  dotZ (Z.getD i []) (KC.getD j []) - (if i = j then (2 : Int) ^ sc else 0)

/-- `max_i Σ_j |F_ij + F_ji|` in `O(n³)` -/
def thetaNumF (Z : List (List Int)) (n bits mb : Nat) (ex kl : List Int) (sc : Nat) : Nat :=
  let KC := kzCols n bits mb ex kl
  maxN n fun i => sumN n fun j => (fentF Z KC sc i j + fentF Z KC sc j i).natAbs

/-- **Fast short-metric leaf**: `checkTheta` with `thetaNumF` -/
def checkThetaF (nb wz bits mb : Nat) (zrows : List Nat) (ex kl : List Int) (claim : Nat) : Bool :=
  Nat.ble (thetaNumF (zMatrix nb wz zrows) nb bits mb ex kl (Nat.add 32 mb)) claim &&
    Nat.ble bits mb && ex.all (fun e => decide (0 ≤ (mb : Int) + e)) &&
    Nat.beq ex.length nb && Nat.beq zrows.length nb

/-- rows `i0 ≤ i < i0 + k` of `θ ≤ claim` (the `O(n³)` kernel split by rows: `O(k n²)` per leaf) -/
def thetaRowsF (Z : List (List Int)) (n bits mb : Nat) (ex kl : List Int) (sc claim i0 : Nat) : Nat → Bool :=
  let KC := kzCols n bits mb ex kl
  fun k => (List.range k).all fun i =>
    Nat.ble (sumN n fun j => (fentF Z KC sc (i0 + i) j + fentF Z KC sc j (i0 + i)).natAbs) claim

/-- **Fast short-metric leaf on the rows `i0 ≤ i < i0 + k`** (with the side conditions of `checkTheta`) -/
def checkThetaR (nb wz bits mb : Nat) (zrows : List Nat) (ex kl : List Int) (claim i0 k : Nat) : Bool :=
  thetaRowsF (zMatrix nb wz zrows) nb bits mb ex kl (Nat.add 32 mb) claim i0 k &&
    Nat.ble bits mb && ex.all (fun e => decide (0 ≤ (mb : Int) + e)) &&
    Nat.beq ex.length nb && Nat.beq zrows.length nb

/-! ## `thetaNumF = thetaNum` -/

theorem dotZ_nil_left (ys : List Int) : dotZ [] ys = 0 := by cases ys <;> rfl

theorem dotZ_nil_right (xs : List Int) : dotZ xs [] = 0 := by cases xs <;> rfl

theorem sumZ_zero : ∀ (n : Nat) (f : Nat → Int), (∀ l < n, f l = 0) → sumZ n f = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
    show sumZ n f + f n = 0
    rw [sumZ_zero n f (fun l hl => h l (by omega)), h n (by omega)]
    rfl

theorem sumZ_shift : ∀ (m : Nat) (g : Nat → Int), sumZ (m + 1) g = g 0 + sumZ m (fun l => g (l + 1))
  | 0, g => by show sumZ 0 g + g 0 = g 0 + 0; show (0 : Int) + g 0 = g 0 + 0; omega
  | m + 1, g => by
    show sumZ (m + 1) g + g (m + 1) = g 0 + (sumZ m (fun l => g (l + 1)) + g (m + 1))
    rw [sumZ_shift m g]
    omega

theorem dotZ_eq : ∀ (xs ys : List Int) (n : Nat), xs.length ≤ n →
    dotZ xs ys = sumZ n (fun l => xs.getD l 0 * ys.getD l 0)
  | [], ys, n, _ => by
    rw [dotZ_nil_left, sumZ_zero n _ (fun l _ => by simp)]
  | x :: xs, [], n, _ => by
    rw [dotZ_nil_right, sumZ_zero n _ (fun l _ => by simp)]
  | x :: xs, y :: ys, n, h => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
    have h' : xs.length ≤ m := by simp at h; omega
    show x * y + dotZ xs ys = _
    rw [dotZ_eq xs ys m h', sumZ_shift m]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

theorem sumZ_congr {f g : Nat → Int} : ∀ n, (∀ l < n, f l = g l) → sumZ n f = sumZ n g
  | 0, _ => rfl
  | n + 1, h => by
    show sumZ n f + f n = sumZ n g + g n
    rw [sumZ_congr n (fun l hl => h l (by omega)), h n (by omega)]

theorem sumN_congr {f g : Nat → Nat} : ∀ n, (∀ l < n, f l = g l) → sumN n f = sumN n g
  | 0, _ => rfl
  | n + 1, h => by
    show Nat.add (sumN n f) (f n) = Nat.add (sumN n g) (g n)
    rw [sumN_congr n (fun l hl => h l (by omega)), h n (by omega)]

theorem maxN_congr {f g : Nat → Nat} : ∀ n, (∀ l < n, f l = g l) → maxN n f = maxN n g
  | 0, _ => rfl
  | n + 1, h => by
    show Nat.max (maxN n f) (f n) = Nat.max (maxN n g) (g n)
    rw [maxN_congr n (fun l hl => h l (by omega)), h n (by omega)]

theorem lowerRow_length (s : Int) : ∀ (l : Nat) (r : List Int), (lowerRow s l r).length = l
  | 0, _ => rfl
  | l + 1, _ :: xs => by simp [lowerRow, lowerRow_length s l xs]
  | l + 1, [] => by simp [lowerRow, lowerRow_length s l []]

theorem lowerRow_getD (s : Int) : ∀ (l : Nat) (r : List Int) (j : Nat), j < l →
    (lowerRow s l r).getD j 0 = r.getD j 0 * s
  | 0, _, j, h => absurd h (by omega)
  | l + 1, x :: xs, 0, _ => by simp [lowerRow]
  | l + 1, x :: xs, j + 1, h => by
    simp only [lowerRow, List.getD_cons_succ]
    exact lowerRow_getD s l xs j (by omega)
  | l + 1, [], 0, _ => by simp [lowerRow]
  | l + 1, [], j + 1, h => by
    simp only [lowerRow, List.getD_cons_succ]
    rw [lowerRow_getD s l [] j (by omega)]
    simp

theorem getD_append_left' (a b : List Int) (j : Nat) (h : j < a.length) : (a ++ b).getD j 0 = a.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (a b : List Int) (j : Nat) (h : a.length ≤ j) :
    (a ++ b).getD j 0 = b.getD (j - a.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_replicate_zero (m j : Nat) : (List.replicate m (0 : Int)).getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_drop' (r : List Int) (k j : Nat) : (r.drop k).getD j 0 = r.getD (k + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem kzRow_getD (n bits mb : Nat) (ex kl : List Int) (l j : Nat) :
    (kzRow n bits mb ex kl l).getD j 0 = kzent bits mb ex kl l j := by
  unfold kzRow kzent
  have hlen := lowerRow_length ((2 : Int) ^ (mb - bits)) l (kl.drop (l * (l - 1) / 2))
  by_cases hj : j < l
  · rw [getD_append_left' _ _ _ (by omega), lowerRow_getD _ _ _ _ hj, getD_drop', if_pos hj]
  · rw [getD_append_right' _ _ _ (by omega), if_neg hj, hlen]
    by_cases hl : l = j
    · subst hl; rw [if_pos rfl, Nat.sub_self]; rfl
    · rw [if_neg hl]
      obtain ⟨d, hd⟩ : ∃ d, j - l = d + 1 := ⟨j - l - 1, by omega⟩
      rw [hd, List.getD_cons_succ, getD_replicate_zero]

theorem kCols_getD (n : Nat) (KR : List (List Int)) (j l : Nat) (hj : j < n) (hl : l < KR.length) :
    ((kCols n KR).getD j []).getD l 0 = (KR.getD l []).getD j 0 := by
  unfold kCols
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, hl]

theorem getD_map_range (f : Nat → List Int) (l n : Nat) (h : l < n) : ((List.range n).map f).getD l [] = f l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

theorem tri_succ (l : Nat) : (l + 1) * (l + 1 - 1) / 2 = l * (l - 1) / 2 + l := by
  have h : (l + 1) * l = l * (l - 1) + 2 * l := by
    cases l with
    | zero => rfl
    | succ k => simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_succ, Nat.add_mul, Nat.mul_add]; omega
  rw [Nat.add_sub_cancel, h]
  omega

theorem kzRowsAux_getD (n bits mb : Nat) (ex kl : List Int) : ∀ (i m l : Nat), i < m →
    (kzRowsAux n bits mb ex m l (kl.drop (l * (l - 1) / 2))).getD i [] = kzRow n bits mb ex kl (l + i)
  | _, 0, _, h => absurd h (by omega)
  | 0, m + 1, l, _ => by simp [kzRowsAux, kzRow]
  | i + 1, m + 1, l, h => by
    simp only [kzRowsAux, List.getD_cons_succ]
    rw [List.drop_drop, show l * (l - 1) / 2 + l = (l + 1) * (l + 1 - 1) / 2 from (tri_succ l).symm,
      kzRowsAux_getD n bits mb ex kl i m (l + 1) (by omega), show l + 1 + i = l + (i + 1) by omega]

theorem kzRowsAux_length (n bits mb : Nat) (ex : List Int) : ∀ (m l : Nat) (r : List Int),
    (kzRowsAux n bits mb ex m l r).length = m
  | 0, _, _ => rfl
  | m + 1, l, r => by simp [kzRowsAux, kzRowsAux_length n bits mb ex m]

theorem kzRow_length (n bits mb : Nat) (ex kl : List Int) (l : Nat) (hl : l < n) :
    (kzRow n bits mb ex kl l).length = n := by
  simp [kzRow, lowerRow_length]; omega

theorem transposeN_length (n : Nat) : ∀ (rows : List (List Int)), (∀ r ∈ rows, r.length = n) →
    (transposeN n rows).length = n
  | [], _ => by simp [transposeN]
  | row :: rows, h => by
    show (List.zipWith _ row (transposeN n rows)).length = n
    rw [List.length_zipWith, h row (by simp), transposeN_length n rows (fun r hr => h r (by simp [hr]))]
    simp

theorem transposeN_getD (n : Nat) : ∀ (rows : List (List Int)), (∀ r ∈ rows, r.length = n) →
    ∀ j l, j < n → l < rows.length → ((transposeN n rows).getD j []).getD l 0 = (rows.getD l []).getD j 0
  | [], _, j, l, _, hl => absurd hl (by simp)
  | row :: rows, h, j, l, hj, hl => by
    have hrow : row.length = n := h row (by simp)
    have hT := transposeN_length n rows (fun r hr => h r (by simp [hr]))
    show ((List.zipWith (fun x c => x :: c) row (transposeN n rows)).getD j []).getD l 0 = _
    have e : (List.zipWith (fun x c => x :: c) row (transposeN n rows)).getD j [] =
        row.getD j 0 :: (transposeN n rows).getD j [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < row.length by omega),
        List.getElem?_eq_getElem (show j < (transposeN n rows).length by omega)]
    rw [e]
    cases l with
    | zero => simp
    | succ l =>
      simp only [List.getD_cons_succ]
      exact transposeN_getD n rows (fun r hr => h r (by simp [hr])) j l hj (by simp at hl; omega)

theorem kzCols_getD (n bits mb : Nat) (ex kl : List Int) (j l : Nat) (hj : j < n) (hl : l < n) :
    ((kzCols n bits mb ex kl).getD j []).getD l 0 = kzent bits mb ex kl l j := by
  unfold kzCols
  have hlen : ∀ r ∈ kzRowsAux n bits mb ex n 0 kl, r.length = n := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hi' : i < n := by rw [kzRowsAux_length] at hi; exact hi
    have := kzRowsAux_getD n bits mb ex kl i n 0 hi'
    simp only [Nat.zero_mul, Nat.zero_div, List.drop_zero, Nat.zero_add] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    rw [this]
    exact kzRow_length n bits mb ex kl i hi'
  rw [transposeN_getD n _ hlen j l hj (by rw [kzRowsAux_length]; exact hl)]
  have := kzRowsAux_getD n bits mb ex kl l n 0 hl
  simp only [Nat.zero_mul, Nat.zero_div, List.drop_zero, Nat.zero_add] at this
  rw [this]
  exact kzRow_getD n bits mb ex kl l j

theorem decodeSM_length (w : Nat) : ∀ (n x : Nat), (decodeSM w n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [decodeSM, decodeSM_length w n]

theorem zMatrix_row_length (nb wz : Nat) (zrows : List Nat) (i : Nat) :
    ((zMatrix nb wz zrows).getD i []).length ≤ nb := by
  unfold zMatrix
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases zrows[i]? with
  | none => simp
  | some x => simp [decodeSM_length]

theorem fentF_eq (nb wz bits mb : Nat) (zrows : List Nat) (ex kl : List Int) (sc i j : Nat) (hj : j < nb) :
    fentF (zMatrix nb wz zrows) (kzCols nb bits mb ex kl) sc i j =
      fent (zMatrix nb wz zrows) nb bits mb ex kl sc i j := by
  unfold fentF fent
  rw [dotZ_eq _ _ nb (zMatrix_row_length nb wz zrows i)]
  congr 1
  apply sumZ_congr
  intro l hl
  rw [kzCols_getD nb bits mb ex kl j l hj hl]
  rfl

theorem thetaNumF_eq (nb wz bits mb : Nat) (zrows : List Nat) (ex kl : List Int) (sc : Nat) :
    thetaNumF (zMatrix nb wz zrows) nb bits mb ex kl sc = thetaNum (zMatrix nb wz zrows) nb bits mb ex kl sc := by
  unfold thetaNumF thetaNum
  apply maxN_congr
  intro i hi
  apply sumN_congr
  intro j hj
  rw [fentF_eq nb wz bits mb zrows ex kl sc i j hj, fentF_eq nb wz bits mb zrows ex kl sc j i hi]

/-- **A passing fast short-metric leaf is a passing `checkTheta` leaf.** -/
theorem checkThetaF_imp {nb wz bits mb : Nat} {zrows : List Nat} {ex kl : List Int} {claim : Nat}
    (h : checkThetaF nb wz bits mb zrows ex kl claim = true) : checkTheta nb wz bits mb zrows ex kl claim = true := by
  unfold checkThetaF at h
  unfold checkTheta
  rw [← thetaNumF_eq]
  exact h

theorem maxN_le {f : Nat → Nat} {c : Nat} : ∀ n, (∀ i < n, f i ≤ c) → maxN n f ≤ c
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    show Nat.max (maxN n f) (f n) ≤ c
    exact Nat.max_le.mpr ⟨maxN_le n (fun i hi => h i (by omega)), h n (by omega)⟩

/-- **Row-split fast short-metric leaves covering the rows give a passing `checkTheta` leaf.** -/
theorem checkTheta_of_rows {nb wz bits mb : Nat} {zrows : List Nat} {ex kl : List Int} {claim : Nat}
    (ranges : List (Nat × Nat)) (hn : 0 < nb) (hcov : ∀ i < nb, ∃ p ∈ ranges, p.1 ≤ i ∧ i < p.1 + p.2)
    (h : ∀ p ∈ ranges, checkThetaR nb wz bits mb zrows ex kl claim p.1 p.2 = true) :
    checkTheta nb wz bits mb zrows ex kl claim = true := by
  have hrow : ∀ i < nb, (sumN nb fun j => (fentF (zMatrix nb wz zrows) (kzCols nb bits mb ex kl) (32 + mb) i j +
      fentF (zMatrix nb wz zrows) (kzCols nb bits mb ex kl) (32 + mb) j i).natAbs) ≤ claim := by
    intro i hi
    obtain ⟨p, hp, h1, h2⟩ := hcov i hi
    have hl := h p hp
    unfold checkThetaR at hl
    simp only [Bool.and_eq_true] at hl
    have hr := hl.1.1.1.1
    unfold thetaRowsF at hr
    rw [List.all_eq_true] at hr
    have := hr (i - p.1) (List.mem_range.mpr (by omega))
    rw [show p.1 + (i - p.1) = i by omega] at this
    exact Nat.le_of_ble_eq_true this
  obtain ⟨p, hp, -, -⟩ := hcov 0 hn
  have hl := h p hp
  unfold checkThetaR at hl
  simp only [Bool.and_eq_true] at hl
  unfold checkTheta
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, hl.1.1.1.2⟩, hl.1.1.2⟩, hl.1.2⟩, hl.2⟩
  rw [← thetaNumF_eq]
  unfold thetaNumF
  exact Nat.ble_eq.mpr (maxN_le nb hrow)

end ThomsonCompact.Floor
