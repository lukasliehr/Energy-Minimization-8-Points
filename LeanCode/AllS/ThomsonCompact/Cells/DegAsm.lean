import ThomsonCompact.Cells.D12Asm
import ThomsonCompact.Cells.DegGateK
import ThomsonCompact.Floor.B.SoundBlockS

/-!
# Degree-generic pieces of the D14/D16/D18 cell assemblies (F3g)

Generic in the number of retained coordinates `nI` (145/202/272) and of target models `t` (14/16/18); used by every
`Cells/<cell>/Cell.lean` of the cells 19–29 (per-degree parts: `Cells/DegAsm14.lean`, `DegAsm16.lean`, `DegAsm18.lean`).

* `centreGateT_spec` (soundness of the leaf kernel `DegGateK.centreGateT`, with `D12Asm.cgateF_spec`);
* `centre_gate_of_hintS`, **`centre_gate_degS`**: the centre gate of `gateR H B q` for the target TMs `H` (T3) and
  one combined W0 point model per coordinate `B _ r = ckQ N S F (D r)` (F2's `BsumD N S sumData r` is this with
  `D r = dRecD sumData N r`, `F = sumData.F`; coefficients `sdec dₖ · 2^F / 2^S = sdec dₖ · 2^(128+Fp)` at `2^-256`)
  from the fast centre-gate leaves `centreGateT … 128 Fp … nT i0 n = true` covering the coordinates;
  `centre_gate_degF`: the announced format `S = 160`, `F = 80` (`Fp = 48`). Any record scale works: the W0
  accuracy the floors need goes down to `2^-88` (cell 28), below the `2^-80` resolution of `F = 80`;
* **`dir_of_tags`**: the target directions `targetQ (tags r) j` are the channel directions `dirT`/`dirQ` of the cell
  data, from one check per coordinate (instead of one per coordinate and target index);
* `blockOkS_of`: a sequential column leaf (`KernelQ2.blockOkS` on the packed block coordinates `uvs` and the
  checkpoint slice `cks`) is a `blockOkQ` leaf (`SoundBlockS.blockOkS_imp` + the one-time `uvs = uvsOf row j0 nr`).
-/

namespace ThomsonCompact.Cells.DegAsm

open ThomsonCompact.Packed ThomsonCompact.Floor.B ThomsonCompact.CoeffMap ThomsonCompact.Cells.D12Asm
open ThomsonCompact.Floor (slot)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- **Soundness of a centre-gate leaf** (any degree): every coordinate of its range passes `cgateF`. -/
theorem centreGateT_spec {c : Ctx} {Ht : ℕ → TM} {dirT : ℕ → ℕ} {dirQ : ℕ → Bool × ℕ} {D : ℕ → List ℕ}
    {G F' wc : ℕ} {cm Er : ℕ → ℕ} {nT i0 : ℕ} : ∀ {n : ℕ},
    centreGateT c Ht dirT dirQ D G F' wc cm Er nT i0 n = true → ∀ i, i0 ≤ i → i < i0 + n →
      dirT i < nT ∧ cgateF c (Ht (dirT i)) (dirQ i) (D i) G F' wc (cm i) (Er i) = true
  | 0, _, i, h1, h2 => absurd h2 (by omega)
  | n + 1, h, i, h1, h2 => by
    have h' : ((Nat.blt (dirT (Nat.add i0 n)) nT && cgateF c (Ht (dirT (Nat.add i0 n))) (dirQ (Nat.add i0 n))
        (D (Nat.add i0 n)) G F' wc (cm (Nat.add i0 n)) (Er (Nat.add i0 n))) &&
        centreGateT c Ht dirT dirQ D G F' wc cm Er nT i0 n) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge i (i0 + n) with h3 | h3
    · exact centreGateT_spec h'.2 i h1 h3
    · have e : i = i0 + n := by omega
      subst e
      exact ⟨Nat.le_of_ble_eq_true h'.1.1, h'.1.2⟩

/-- **Centre gate of one combined W0 point model per coordinate** (any degree, any record scale) from the
per-coordinate integer inequality `hint`. Target models `H j = toQModel c (L_{j+1})` (`L` = T3's coefficient list), W0
point models `Bs r = ckQ N S F (D r)` (coefficients `sdec dₖ · 2^F / 2^S = sdec dₖ · 2^(128+Fp) / 2^256`), directions
`q` of the channel data `cb`, centres `C 2^-Sc`, radii `Er 2^-256`. -/
theorem centre_gate_of_hintS {N Bw Ww Sc nI t : ℕ} (S F Fp : ℕ) (hSF : 256 + F = S + (128 + Fp)) (hSc : Sc ≤ 256)
    (H : Fin t → QModel N) (L : List TM)
    (hH : ∀ j : Fin t, H j = toQModel (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM))
    (Bs : Fin nI → QModel N) (D : ℕ → List ℕ) (hB : ∀ r : Fin nI, Bs r = ckQ N S F (D r.val))
    (cb : CellB) (q : Fin nI → Fin t → ℚ)
    (hq : ∀ (r : Fin nI) (j : Fin t), q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hint : ∀ i : Fin nI, cb.dirT i < t ∧
      ∑ k : Fin (N + 1), |sv (cb.dirQ i) * (decode (mkCtx N 256 Bw Ww) (L.getD (cb.dirT i + 1) zeroTM).v).getD k 0 -
        3 * (sdec ((D i).getD k 0) * 2 ^ (128 + Fp)) - 3 * sv (smDec (slot cb.wc (cb.cm i) k)) * 2 ^ (256 - Sc)| +
        3 * (((D i).getD (N + 1) 0 * 2 ^ (128 + Fp) : ℕ) : ℤ) ≤ 3 * (cb.Er i : ℤ)) :
    StructuredCenterGate (gateR H (fun (_ : Fin 1) (r : Fin nI) => Bs r) q)
      (fun r k => (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ Sc) (fun r => (cb.Er r : ℚ) / 2 ^ 256) := by
  have hpow : ∀ z : ℚ, z * 2 ^ F / 2 ^ S = z * 2 ^ (128 + Fp) / 2 ^ 256 := by
    intro z
    have e : (2 : ℚ) ^ F * 2 ^ 256 = 2 ^ (128 + Fp) * 2 ^ S := by
      rw [← pow_add, ← pow_add, Nat.add_comm F 256, hSF, Nat.add_comm S]
    rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, e, ← mul_assoc]
  refine centre_gate_of_int H (fun _ r => Bs r) q _ _
    (fun j k => (decode (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM).v).getD k.val 0)
    (fun i k => sdec ((D i).getD k.val 0) * 2 ^ (128 + Fp))
    (fun i => (D i).getD (N + 1) 0 * 2 ^ (128 + Fp))
    (fun i => ⟨cb.dirT i, (hint i).1⟩) (fun i => sv (cb.dirQ i))
    (fun i k => sv (smDec (slot cb.wc (cb.cm i) k))) (fun i => cb.Er i) Sc hSc
    ?hH ?hpt ?hbs ?hbe ?hq ?hcen ?herr ?hint
  case hH =>
    intro j k
    rw [hH j]
    rfl
  case hpt =>
    intro j i k
    show ((Bs i).coeff k).hi = ((Bs i).coeff k).lo
    rw [hB i]
    rfl
  case hbs =>
    intro i k
    rw [Fin.sum_univ_one]
    show ((Bs i).coeff k).lo = _
    rw [hB i]
    show (sdec ((D i).getD k.val 0) : ℚ) * 2 ^ F / 2 ^ S = _
    rw [hpow]
    push_cast
    ring
  case hbe =>
    intro i
    rw [Fin.sum_univ_one]
    show (Bs i).error = _
    rw [hB i]
    show (((D i).getD (N + 1) 0 : ℕ) : ℚ) * 2 ^ F / 2 ^ S = _
    rw [hpow]
    push_cast
    ring
  case hq =>
    intro i j
    rw [hq i j]
    by_cases h : cb.dirT i = j.val
    · have e : (⟨cb.dirT i, (hint i).1⟩ : Fin t) = j := Fin.ext h
      rw [if_pos h, if_pos e]
    · have e : (⟨cb.dirT i, (hint i).1⟩ : Fin t) ≠ j := fun e => h (congrArg Fin.val e)
      rw [if_neg h, if_neg e]
      simp
  case hcen =>
    intro i k
    rfl
  case herr =>
    intro i
    rfl
  case hint =>
    intro i
    exact (hint i).2

/-- **Centre gate of the combined W0 sums** (any degree, record scale `2^-(S-F)`) from fast centre-gate leaves
covering the `nI` coordinates (`DegGateK.centreGateT`, centres at `2^-128`, records shifted by `2^(128+Fp)` to the
gate scale `2^-256`; F2's announced format `S = 160`, `F = 80` is `Fp = 48`). -/
theorem centre_gate_degS {N Bw Ww nI t : ℕ} (S F Fp : ℕ) (hSF : 256 + F = S + (128 + Fp)) (H : Fin t → QModel N)
    (L : List TM) (hH : ∀ j : Fin t, H j = toQModel (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM))
    (Bs : Fin nI → QModel N) (D : ℕ → List ℕ) (hB : ∀ r : Fin nI, Bs r = ckQ N S F (D r.val))
    (cb : CellB) (q : Fin nI → Fin t → ℚ)
    (hq : ∀ (r : Fin nI) (j : Fin t), q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (leaves : List (ℕ × ℕ)) (hcov : ∀ i < nI, ∃ p ∈ leaves, p.1 ≤ i ∧ i < p.1 + p.2)
    (hleaf : ∀ p ∈ leaves, centreGateT (mkCtx N 256 Bw Ww) (fun t => (L.drop 1).getD t zeroTM) cb.dirT cb.dirQ
      D 128 Fp cb.wc cb.cm cb.Er t p.1 p.2 = true) :
    StructuredCenterGate (gateR H (fun (_ : Fin 1) (r : Fin nI) => Bs r) q)
      (fun r k => (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ 128) (fun r => (cb.Er r : ℚ) / 2 ^ 256) := by
  refine centre_gate_of_hintS S F Fp hSF (by norm_num) H L hH Bs D hB cb q hq fun i => ?_
  obtain ⟨p, hp, h1, h2⟩ := hcov i.val i.isLt
  have h := centreGateT_spec (hleaf p hp) i.val h1 h2
  refine ⟨h.1, ?_⟩
  have h3 := cgateF_spec 128 Fp _ _ _ _ _ _ h.2
  simp only [svK_eq, getD_drop_one] at h3
  have e : ∀ k : Fin (N + 1), sv (pvGet Ww (N + 1) ((L.getD (cb.dirT ↑i + 1) zeroTM).v) k) =
      (decode (mkCtx N 256 Bw Ww) (L.getD (cb.dirT ↑i + 1) zeroTM).v).getD k 0 :=
    fun k => pvGet_decode _ _ k.isLt
  simp only [e] at h3
  exact h3

/-- the announced format of F2's final sums (`S = 160`, `F = 80`: records at `2^-80`, shift `2^176`) -/
theorem centre_gate_degF {N Bw Ww nI t : ℕ} (H : Fin t → QModel N) (L : List TM)
    (hH : ∀ j : Fin t, H j = toQModel (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM))
    (Bs : Fin nI → QModel N) (D : ℕ → List ℕ) (hB : ∀ r : Fin nI, Bs r = ckQ N 160 80 (D r.val))
    (cb : CellB) (q : Fin nI → Fin t → ℚ)
    (hq : ∀ (r : Fin nI) (j : Fin t), q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (leaves : List (ℕ × ℕ)) (hcov : ∀ i < nI, ∃ p ∈ leaves, p.1 ≤ i ∧ i < p.1 + p.2)
    (hleaf : ∀ p ∈ leaves, centreGateT (mkCtx N 256 Bw Ww) (fun t => (L.drop 1).getD t zeroTM) cb.dirT cb.dirQ
      D 128 48 cb.wc cb.cm cb.Er t p.1 p.2 = true) :
    StructuredCenterGate (gateR H (fun (_ : Fin 1) (r : Fin nI) => Bs r) q)
      (fun r k => (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ 128) (fun r => (cb.Er r : ℚ) / 2 ^ 256) :=
  centre_gate_degS 160 80 48 rfl H L hH Bs D hB cb q hq leaves hcov hleaf

/-- **Target directions from one check per coordinate**: if `dirT r + 1` is the weight of the tag of `r` and
`dirQ r` its power-sum coefficient, then `targetQ (tags r) j = [dirT r = j] · dirQ r / 3`. -/
theorem dir_of_tags {nI t : ℕ} (tags : Fin nI → Tag) (cb : CellB)
    (h : ∀ r : Fin nI, cb.dirT r + 1 = tagWeight (tags r) ∧
      (sv (cb.dirQ r) : ℚ) = rawRationalLookup (powerSparse (tagWeight (tags r))) (tags r)) :
    ∀ (r : Fin nI) (j : Fin t),
      targetQ (tags r) j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3 := by
  intro r j
  obtain ⟨h1, h2⟩ := h r
  unfold targetQ
  by_cases hj : cb.dirT r = j.val
  · rw [if_pos (by omega), if_pos hj, ← h2]
  · rw [if_neg (by omega), if_neg hj]
    simp

/-- **A sequential column leaf is a `blockOkQ` leaf** (packed block coordinates `uvs = uvsOf row j0 nr`, checkpoint
slice `cks = cksOf ckd j0 nr`). -/
theorem blockOkS_of (cb : CellB) (row : ℕ → RowT) (Kc wv we : ℕ) (ckd : ℕ → CkRow) (j0 nr n wz : ℕ)
    (zrows : List ℕ) (FG LB LE LS ch0 nch ww : ℕ) (wsN : ℕ → ℕ) (wEN : ℕ) (q0 nq : ℕ) (Rp : ℕ → ℕ) (RpE : ℕ)
    (uvs : List (ℕ × ℕ)) (cks : List CkRow) (huv : uvs = uvsOf row j0 nr) (hck : cksOf ckd j0 nr = cks)
    (h : blockOkS cb uvs cks Kc wv we n wz zrows FG LB LE LS ch0 nch ww wsN wEN q0 nq Rp RpE = true) :
    blockOkQ cb row Kc wv we ckd j0 nr n wz zrows FG LB LE LS ch0 nch (wsL n ww wsN) (wEL n ww wEN) q0 nq Rp RpE
      = true := by
  subst huv
  rw [← hck] at h
  exact blockOkS_imp cb row Kc wv we ckd j0 nr n wz zrows FG LB LE LS ch0 nch ww wsN wEN q0 nq Rp RpE h

end ThomsonCompact.Cells.DegAsm
