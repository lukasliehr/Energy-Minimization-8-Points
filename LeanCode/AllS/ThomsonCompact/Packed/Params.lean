import ThomsonCompact.Packed.Rep

/-!
# Production parameters

`S = 256` fractional bits, `B = 264` (coefficient sums `Σ|cₖ| < 2^(B-S) = 256`), slot width `W = 2B + 2 = 530`.
Contexts for the benchmarked orders `N = 12, 22, 32`; `Good` holds by `decide`.
-/

namespace ThomsonCompact.Packed

/-- production context of order `N` -/
abbrev prodCtx (N : Nat) : Ctx := mkCtx N 256 264 530

theorem good_prod (N : Nat) (hN : N + 1 ≤ 2 ^ 264) : Good N 256 264 530 :=
  ⟨by decide, by decide, by decide, hN⟩

theorem good12 : Good 12 256 264 530 := ⟨by decide, by decide, by decide, by decide⟩
theorem good22 : Good 22 256 264 530 := ⟨by decide, by decide, by decide, by decide⟩
theorem good32 : Good 32 256 264 530 := ⟨by decide, by decide, by decide, by decide⟩

#print axioms good32

end ThomsonCompact.Packed
