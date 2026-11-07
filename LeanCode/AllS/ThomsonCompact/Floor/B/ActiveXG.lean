import ThomsonCompact.Floor.B.ActiveX

/-!
# Two-piece corrected blocks, degree-generic helpers (F3g)

`half_memX`: the halves `x = (y ∓ 1)/2` map `[-1,1]` into `[-1,1]` (copy of `ActiveX12.half_mem`, without the D12
imports); `hcen_of_reexps`: the centre hypothesis of a half from re-expansion leaves on coordinate ranges
(`reexpOk … i0 n`, any number of coordinates).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

theorem half_memX (neg : Bool) {y : ℝ} (hy : y ∈ cellDomain) : (y + sgnH neg) / 2 ∈ cellDomain := by
  obtain ⟨h1, h2⟩ := hy
  unfold sgnH; cases neg <;> simp <;> constructor <;> linarith

/-- the centre hypothesis of a half from re-expansion leaves covering the `nI` coordinates -/
theorem hcen_of_reexps {N wc wcP : ℕ} {neg : Bool} {cm cmP : ℕ → ℕ} {nI : ℕ} (leaves : List (ℕ × ℕ))
    (hcov : ∀ i < nI, ∃ p ∈ leaves, p.1 ≤ i ∧ i < p.1 + p.2)
    (h : ∀ p ∈ leaves, reexpOk N wc wcP neg cm cmP p.1 p.2 = true) (Sc : ℕ) (r : Fin nI) (y : ℝ) :
    scalarEval (fun k : Fin (N + 1) => (((sv (smDec (slot wc (cm r) k)) : ℚ) / 2 ^ Sc : ℚ) : ℝ))
        ((y + sgnH neg) / 2) =
      scalarEval (fun k : Fin (N + 1) => (((sv (smDec (slot wcP (cmP r) k)) : ℚ) / 2 ^ (Sc + N) : ℚ) : ℝ)) y := by
  obtain ⟨p, hp, h1, h2⟩ := hcov r.val r.isLt
  have := reexpOk_sound (h p hp) Sc (r.val - p.1) (by omega) y
  rw [show p.1 + (r.val - p.1) = r.val by omega] at this
  push_cast
  exact this

end ThomsonCompact.Floor.B
