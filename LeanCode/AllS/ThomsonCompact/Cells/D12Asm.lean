import ThomsonCompact.Floor.B.CellAsm
import ThomsonCompact.Floor.B.CellGate
import ThomsonCompact.CoeffMap.BSumSound
import ThomsonCompact.CoeffMap.W0Part
import ThomsonCompact.CoeffMap.Target
import ThomsonCompact.Cells.D12GateK

/-!
# Generic pieces of the D12 cell assemblies (F3e; used by every `Cells/<cell>/Cell.lean`)

* `combine`: one combined W0 model per retained coordinate (`nb = 1`) from F2's 112 pieces (`w0Part`) and their
  final sums (`Bsum_valid`); `g _ r = Σ_ι w0Part.g ι r`, so `W0_link` is F2's (`Fin.sum_univ_one`).
* `centre_gate_bsum`: the centre gate of `gateR H B q` for the target TMs `H` (T3) and the combined sums
  `B _ r = BsumQ N 160 sd r` (coefficients `sdec dₖ · 2^80 / 2^160`, i.e. `sdec dₖ · 2^176` at `2^-256`) from the leaf
  `centreGateOk … (dRec sd N) 176 Sc wc cm Er 100 = true` (`CellGate.centreGate_hint`, `CellAsm.centre_gate_of_int`).
* `centre_gate_bsumF`: the same from the fast leaves `centreGateF … 128 48 … i0 n = true` (`D12GateK`: no products
  with powers of two, coordinate ranges); `cgateF_spec`, `centreGateF_spec` (exact soundness).
* `box_of_height12`: `box_of_heightG` at the D12 anchor `19/2^6`, `σ = 2^-4` (either sign of the box centre).
-/

namespace ThomsonCompact.Cells.D12Asm

open ThomsonCompact.Packed ThomsonCompact.Floor.B ThomsonCompact.CoeffMap
open ThomsonCompact.Floor (slot)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- **One combined W0 model per coordinate** (`nb = 1`) from the 112 pieces and the per-coordinate sums. -/
noncomputable def combine {s : ℝ → ℝ} {cell : Literals.Cell} {blk : GramBlock 6 → Literals.Block}
    {hord : ∀ b, (blk b).order = gramBlockDimension 6 b} {NI N : ℕ} (P : W0Part s cell blk hord NI 112)
    (Bs : ℕ → QModel N) (hB : ∀ r : Fin 100, (Bs r).asTM.Valid (fun x => ∑ ι, P.g ι r x)) :
    W0Part s cell blk hord N 1 where
  B _ r := Bs r
  g _ r x := ∑ ι, P.g ι r x
  B_valid _ r := hB r
  W0_link x hx hs r := by
    rw [Fin.sum_univ_one]
    exact P.W0_link x hx hs r

/-- **Centre gate of the combined W0 sums** from the per-coordinate integer inequality (`hint`). Target models
`H j = toQModel c (L_{j+1})` (`L` = T3's coefficient list), sums `BsumQ N 160 sd` (`sd.F = 80`), directions `q` of the
channel data `cb`, centres `C 2^-Sc`, radii `Er 2^-256`. -/
theorem centre_gate_of_hint {N Bw Ww Sc : ℕ} (hSc : Sc ≤ 256) (H : Fin 12 → QModel N) (L : List TM)
    (hH : ∀ j : Fin 12, H j = toQModel (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM))
    (sd : SumData) (hF : sd.F = 80) (cb : CellB) (q : Fin 100 → Fin 12 → ℚ)
    (hq : ∀ (r : Fin 100) (j : Fin 12), q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hint : ∀ i : Fin 100, cb.dirT i < 12 ∧
      ∑ k : Fin (N + 1), |sv (cb.dirQ i) * (decode (mkCtx N 256 Bw Ww) (L.getD (cb.dirT i + 1) zeroTM).v).getD k 0 -
        3 * (sdec ((dRec sd N i).getD k 0) * 2 ^ 176) - 3 * sv (smDec (slot cb.wc (cb.cm i) k)) * 2 ^ (256 - Sc)| +
        3 * (((dRec sd N i).getD (N + 1) 0 * 2 ^ 176 : ℕ) : ℤ) ≤ 3 * (cb.Er i : ℤ)) :
    StructuredCenterGate (gateR H (fun (_ : Fin 1) (r : Fin 100) => BsumQ N 160 sd r) q)
      (fun r k => (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ Sc) (fun r => (cb.Er r : ℚ) / 2 ^ 256) := by
  refine centre_gate_of_int H (fun _ r => BsumQ N 160 sd r) q _ _
    (fun j k => (decode (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM).v).getD k.val 0)
    (fun i k => sdec ((dRec sd N i).getD k.val 0) * 2 ^ 176)
    (fun i => (dRec sd N i).getD (N + 1) 0 * 2 ^ 176)
    (fun i => ⟨cb.dirT i, (hint i).1⟩) (fun i => sv (cb.dirQ i))
    (fun i k => sv (smDec (slot cb.wc (cb.cm i) k))) (fun i => cb.Er i) Sc hSc
    ?hH ?hpt ?hbs ?hbe ?hq ?hcen ?herr ?hint
  case hH =>
    intro j k
    rw [hH j]
    rfl
  case hpt =>
    intro j i k
    rfl
  case hbs =>
    intro i k
    rw [Fin.sum_univ_one]
    show (sdec ((dRec sd N i).getD k.val 0) : ℚ) * 2 ^ sd.F / 2 ^ 160 = _
    rw [hF]
    push_cast
    ring
  case hbe =>
    intro i
    rw [Fin.sum_univ_one]
    show (((dRec sd N i).getD (N + 1) 0 : ℕ) : ℚ) * 2 ^ sd.F / 2 ^ 160 = _
    rw [hF]
    push_cast
    ring
  case hq =>
    intro i j
    rw [hq i j]
    by_cases h : cb.dirT i = j.val
    · have e : (⟨cb.dirT i, (hint i).1⟩ : Fin 12) = j := Fin.ext h
      rw [if_pos h, if_pos e]
    · have e : (⟨cb.dirT i, (hint i).1⟩ : Fin 12) ≠ j := fun e => h (congrArg Fin.val e)
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

/-- **Centre gate of the combined W0 sums** from the centre-gate leaf `centreGateOk` (`Floor.B.KernelC`). -/
theorem centre_gate_bsum {N Bw Ww Sc : ℕ} (hSc : Sc ≤ 256) (H : Fin 12 → QModel N) (L : List TM)
    (hH : ∀ j : Fin 12, H j = toQModel (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM))
    (sd : SumData) (hF : sd.F = 80) (cb : CellB) (q : Fin 100 → Fin 12 → ℚ)
    (hq : ∀ (r : Fin 100) (j : Fin 12), q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hleaf : centreGateOk (mkCtx N 256 Bw Ww) (fun t => (L.drop 1).getD t zeroTM) cb.dirT cb.dirQ
      (fun r => dRec sd N r) 176 Sc cb.wc cb.cm cb.Er 100 = true) :
    StructuredCenterGate (gateR H (fun (_ : Fin 1) (r : Fin 100) => BsumQ N 160 sd r) q)
      (fun r k => (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ Sc) (fun r => (cb.Er r : ℚ) / 2 ^ 256) := by
  refine centre_gate_of_hint hSc H L hH sd hF cb q hq fun i => ?_
  have h := centreGate_hint hleaf i.val i.isLt
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  simp only [getD_drop_one] at h2
  exact h2

/-! ### Soundness of the fast centre-gate kernel (`D12GateK`) -/

theorem nonnegB_iff (x : ℤ) : nonnegB x = true ↔ 0 ≤ x := by
  cases x with
  | ofNat n => exact ⟨fun _ => show (0 : ℤ) ≤ (n : ℤ) from Int.natCast_nonneg n, fun _ => rfl⟩
  | negSucc n =>
    exact ⟨fun h => by simp [nonnegB] at h, fun h => absurd h (not_le.mpr (Int.negSucc_lt_zero n))⟩

/-- `|P a + r| = P |a| ± r` for `0 ≤ r < P` (`+` iff `a ≥ 0`) -/
theorem abs_split (P a r : ℤ) (hr0 : 0 ≤ r) (hr : r < P) :
    |P * a + r| = P * (a.natAbs : ℤ) + (if 0 ≤ a then r else 0) - (if 0 ≤ a then 0 else r) := by
  have hP : 0 ≤ P := le_trans hr0 hr.le
  rw [Int.natCast_natAbs]
  by_cases ha : 0 ≤ a
  · rw [if_pos ha, if_pos ha, abs_of_nonneg ha, abs_of_nonneg (by nlinarith [mul_nonneg hP ha])]
    ring
  · rw [if_neg ha, if_neg ha]
    have ha' : a + 1 ≤ 0 := by omega
    have h1 : P * a + r < 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hP ha']
    rw [abs_of_neg h1, abs_of_neg (lt_of_not_ge ha)]
    ring

/-- one coefficient: `y - P u = P (⌊y/P⌋ - u) + (y mod P)` -/
theorem term_split (P : ℤ) (hP : 0 < P) (y u : ℤ) :
    |y - P * u| = P * ((y / P - u).natAbs : ℤ) + (if 0 ≤ y / P - u then y % P else 0) -
      (if 0 ≤ y / P - u then 0 else y % P) := by
  have e : y - P * u = P * (y / P - u) + y % P := by
    have := Int.mul_ediv_add_emod y P
    linarith
  rw [e]
  exact abs_split P _ _ (Int.emod_nonneg y hP.ne') (Int.emod_lt_of_pos y hP)

theorem lsum_map_cast (f : ℕ → ℕ) (n : ℕ) :
    ((lsum ((List.range n).map f) : ℕ) : ℤ) = ∑ k : Fin n, (f k : ℤ) := by
  rw [lsum_eq_sum, list_sum_range' f n, Fin.sum_univ_eq_sum_range (fun k => (f k : ℤ)) n]
  push_cast
  rfl

/-- **Soundness of one coordinate of the fast centre gate** (exact). -/
theorem cgateF_spec {N S B W : ℕ} (G F' : ℕ) (Ht : TM) (dq : Bool × ℕ) (dr : List ℕ) (wc cm Er : ℕ)
    (h : cgateF (mkCtx N S B W) Ht dq dr G F' wc cm Er = true) :
    ∑ k : Fin (N + 1), |svK dq * svK (pvGet W (N + 1) Ht.v k) -
        3 * (sdec (dr.getD k 0) * 2 ^ (G + F')) - 3 * svK (smDec (slot wc cm k)) * 2 ^ G| +
      3 * ((dr.getD (N + 1) 0 * 2 ^ (G + F') : ℕ) : ℤ) ≤ 3 * (Er : ℤ) := by
  set c := mkCtx N S B W with hc
  set P : ℤ := ((2 ^ G : ℕ) : ℤ) with hPdef
  have hP : 0 < P := by positivity
  have hterm : ∀ k : ℕ, |svK dq * svK (pvGet W (N + 1) Ht.v k) -
      3 * (sdec (dr.getD k 0) * 2 ^ (G + F')) - 3 * svK (smDec (slot wc cm k)) * 2 ^ G| =
      P * ((aK c Ht dq dr G F' wc cm k).natAbs : ℤ) +
        ((cond (nonnegB (aK c Ht dq dr G F' wc cm k)) (rK c Ht dq G k) 0 : ℕ) : ℤ) -
        ((cond (nonnegB (aK c Ht dq dr G F' wc cm k)) 0 (rK c Ht dq G k) : ℕ) : ℤ) := by
    intro k
    have hy : yK c Ht dq k = svK dq * svK (pvGet W (N + 1) Ht.v k) := rfl
    have hu : uK dr F' wc cm k =
        3 * (sdec (dr.getD k 0) * ((2 ^ F' : ℕ) : ℤ) + svK (smDec (slot wc cm k))) := rfl
    have hak : aK c Ht dq dr G F' wc cm k = yK c Ht dq k / P - uK dr F' wc cm k := rfl
    have hrk : ((rK c Ht dq G k : ℕ) : ℤ) = yK c Ht dq k % P :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hP.ne')
    have hX : svK dq * svK (pvGet W (N + 1) Ht.v k) - 3 * (sdec (dr.getD k 0) * 2 ^ (G + F')) -
        3 * svK (smDec (slot wc cm k)) * 2 ^ G = yK c Ht dq k - P * uK dr F' wc cm k := by
      rw [hy, hu, hPdef, pow_add]
      push_cast
      ring
    rw [hX, term_split P hP, ← hak, ← hrk]
    by_cases hn : 0 ≤ aK c Ht dq dr G F' wc cm k
    · rw [if_pos hn, if_pos hn, (nonnegB_iff _).mpr hn]
      simp
    · have hb : nonnegB (aK c Ht dq dr G F' wc cm k) = false := by
        cases hb : nonnegB (aK c Ht dq dr G F' wc cm k)
        · rfl
        · exact absurd ((nonnegB_iff _).mp hb) hn
      rw [if_neg hn, if_neg hn, hb]
      simp
  have hle := Nat.le_of_ble_eq_true h
  have hle' : (((sumA c Ht dq dr G F' wc cm + 3 * (dr.getD (N + 1) 0 * 2 ^ F')) * 2 ^ G +
      sumP c Ht dq dr G F' wc cm : ℕ) : ℤ) ≤ ((3 * Er + sumN c Ht dq dr G F' wc cm : ℕ) : ℤ) := by
    have e1 : Nat.shiftLeft (Nat.add (sumA c Ht dq dr G F' wc cm) (Nat.mul 3 (Nat.shiftLeft (dr.getD c.m 0) F'))) G =
        (sumA c Ht dq dr G F' wc cm + 3 * (dr.getD (N + 1) 0 * 2 ^ F')) * 2 ^ G := by
      show (sumA c Ht dq dr G F' wc cm + 3 * (dr.getD (N + 1) 0 <<< F')) <<< G = _
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have e2 := hle
    rw [show Nat.add (Nat.shiftLeft (Nat.add (sumA c Ht dq dr G F' wc cm)
      (Nat.mul 3 (Nat.shiftLeft (dr.getD c.m 0) F'))) G) (sumP c Ht dq dr G F' wc cm) =
      (sumA c Ht dq dr G F' wc cm + 3 * (dr.getD (N + 1) 0 * 2 ^ F')) * 2 ^ G + sumP c Ht dq dr G F' wc cm by
        rw [← e1]; rfl] at e2
    exact_mod_cast e2
  have hA : ((sumA c Ht dq dr G F' wc cm : ℕ) : ℤ) = ∑ k : Fin (N + 1), ((aK c Ht dq dr G F' wc cm k).natAbs : ℤ) :=
    lsum_map_cast _ (N + 1)
  have hBp : ((sumP c Ht dq dr G F' wc cm : ℕ) : ℤ) = ∑ k : Fin (N + 1),
      ((cond (nonnegB (aK c Ht dq dr G F' wc cm k)) (rK c Ht dq G k) 0 : ℕ) : ℤ) := lsum_map_cast _ (N + 1)
  have hBn : ((sumN c Ht dq dr G F' wc cm : ℕ) : ℤ) = ∑ k : Fin (N + 1),
      ((cond (nonnegB (aK c Ht dq dr G F' wc cm k)) 0 (rK c Ht dq G k) : ℕ) : ℤ) := lsum_map_cast _ (N + 1)
  rw [Finset.sum_congr rfl (fun (k : Fin (N + 1)) _ => hterm k.val), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← hA, ← hBp, ← hBn]
  rw [hPdef]
  push_cast at hle' ⊢
  rw [pow_add]
  linarith

/-- **Soundness of a fast centre-gate leaf**: every coordinate of its range passes `cgateF`. -/
theorem centreGateF_spec {c : Ctx} {Ht : ℕ → TM} {dirT : ℕ → ℕ} {dirQ : ℕ → Bool × ℕ} {D : ℕ → List ℕ}
    {G F' wc : ℕ} {cm Er : ℕ → ℕ} {i0 : ℕ} : ∀ {n : ℕ},
    centreGateF c Ht dirT dirQ D G F' wc cm Er i0 n = true → ∀ i, i0 ≤ i → i < i0 + n →
      dirT i < 12 ∧ cgateF c (Ht (dirT i)) (dirQ i) (D i) G F' wc (cm i) (Er i) = true
  | 0, _, i, h1, h2 => absurd h2 (by omega)
  | n + 1, h, i, h1, h2 => by
    have h' : ((Nat.blt (dirT (Nat.add i0 n)) 12 && cgateF c (Ht (dirT (Nat.add i0 n))) (dirQ (Nat.add i0 n))
        (D (Nat.add i0 n)) G F' wc (cm (Nat.add i0 n)) (Er (Nat.add i0 n))) &&
        centreGateF c Ht dirT dirQ D G F' wc cm Er i0 n) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    rcases Nat.lt_or_ge i (i0 + n) with h3 | h3
    · exact centreGateF_spec h'.2 i h1 h3
    · have e : i = i0 + n := by omega
      subst e
      exact ⟨Nat.le_of_ble_eq_true h'.1.1, h'.1.2⟩

/-- **Centre gate of the combined W0 sums** from fast centre-gate leaves covering the 100 coordinates. -/
theorem centre_gate_bsumF {N Bw Ww : ℕ} (H : Fin 12 → QModel N) (L : List TM)
    (hH : ∀ j : Fin 12, H j = toQModel (mkCtx N 256 Bw Ww) (L.getD (j.val + 1) zeroTM))
    (sd : SumData) (hF : sd.F = 80) (cb : CellB) (q : Fin 100 → Fin 12 → ℚ)
    (hq : ∀ (r : Fin 100) (j : Fin 12), q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (leaves : List (ℕ × ℕ)) (hcov : ∀ i < 100, ∃ p ∈ leaves, p.1 ≤ i ∧ i < p.1 + p.2)
    (hleaf : ∀ p ∈ leaves, centreGateF (mkCtx N 256 Bw Ww) (fun t => (L.drop 1).getD t zeroTM) cb.dirT cb.dirQ
      (fun r => dRec sd N r) 128 48 cb.wc cb.cm cb.Er p.1 p.2 = true) :
    StructuredCenterGate (gateR H (fun (_ : Fin 1) (r : Fin 100) => BsumQ N 160 sd r) q)
      (fun r k => (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ 128) (fun r => (cb.Er r : ℚ) / 2 ^ 256) := by
  refine centre_gate_of_hint (by norm_num) H L hH sd hF cb q hq fun i => ?_
  obtain ⟨p, hp, h1, h2⟩ := hcov i.val i.isLt
  have h := centreGateF_spec (hleaf p hp) i.val h1 h2
  refine ⟨h.1, ?_⟩
  have h3 := cgateF_spec 128 48 _ _ _ _ _ _ h.2
  simp only [svK_eq, getD_drop_one] at h3
  have e : ∀ k : Fin (N + 1), sv (pvGet Ww (N + 1) ((L.getD (cb.dirT ↑i + 1) zeroTM).v) k) =
      (decode (mkCtx N 256 Bw Ww) (L.getD (cb.dirT ↑i + 1) zeroTM).v).getD k 0 :=
    fun k => pvGet_decode _ _ k.isLt
  simp only [e] at h3
  exact h3

/-- the height leaf puts `aS (s x)` into the D12 box `a0D12 + σD12 uf(t)` (either sign of the box centre) -/
theorem box_of_height12 {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (cb : CellB) (acN rg : ℕ)
    (hok : heightOk (mkCtx N 256 B W) A acN rg = true)
    (hac : (2 : ℤ) ^ 4 * acN = ((19 : ℕ) : ℤ) * 2 ^ (256 - 6 + 4) +
      (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ 4 * rg) (hr : 0 < cb.rN) :
    ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = a0D12 + σD12 * cb.uf t :=
  box_of_heightG hg hA cb acN rg hok 19 6 4 (by norm_num) hac hrg hr

end ThomsonCompact.Cells.D12Asm
