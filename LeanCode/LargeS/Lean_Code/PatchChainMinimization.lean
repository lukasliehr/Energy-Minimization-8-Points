import Lean_Code.FinitePatchChains

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def patchChainAdvance (q : (ℝ³ × ℝ) × ℝ³) : ℝ³ × ℝ :=
  (q.2, q.1.2 + sphereAngle q.1.1 q.2)

lemma patchChainAdvance_continuous : Continuous patchChainAdvance := by
  unfold patchChainAdvance sphereAngle
  fun_prop

/-- Endpoints and exact lengths of chains with a prescribed number of links.
The recursive image construction makes the compactness argument finite. -/
def patchChainStates {ι : Type*} (patch : ι → Set ℝ³) (a : ℝ³) : ℕ → Set (ℝ³ × ℝ)
  | 0 => {(a, 0)}
  | n + 1 => ⋃ i, patchChainAdvance ''
      ((patchChainStates patch a n ∩ Prod.fst ⁻¹' patch i) ×ˢ patch i)

theorem patchChainStates_compact {ι : Type*} [Finite ι]
    (patch : ι → Set ℝ³) (hcompact : ∀ i, IsCompact (patch i)) (a : ℝ³) (n : ℕ) :
    IsCompact (patchChainStates patch a n) := by
  induction n with
  | zero => exact isCompact_singleton
  | succ n ih =>
    apply isCompact_iUnion
    intro i
    exact ((ih.inter_right ((hcompact i).isClosed.preimage continuous_fst)).prod
      (hcompact i)).image patchChainAdvance_continuous

theorem mem_patchChainStates_iff {ι : Type*} (patch : ι → Set ℝ³)
    (a : ℝ³) (ha : ‖a‖ = 1) (n : ℕ) (b : ℝ³) (L : ℝ) :
    (b, L) ∈ patchChainStates patch a n ↔
      ∃ p : PatchArcChain patch a b, p.labels.length = n ∧ p.length = L := by
  induction n generalizing b L with
  | zero =>
    constructor
    · intro h
      have heq : (b, L) = (a, 0) := h
      have hb := congrArg Prod.fst heq
      have hL := congrArg Prod.snd heq
      dsimp at hb hL
      subst b
      subst L
      exact ⟨.point ha, rfl, rfl⟩
    · rintro ⟨p, hn, hL⟩
      cases p with
      | point ha => simpa [patchChainStates, PatchArcChain.length] using hL.symm
      | tail p i hb hz => simp [PatchArcChain.labels] at hn
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨i, h⟩ := Set.mem_iUnion.mp h
      obtain ⟨⟨⟨y, M⟩, z⟩, ⟨⟨hstate, hy⟩, hz⟩, heq⟩ := h
      change (z, M + sphereAngle y z) = (b, L) at heq
      cases heq
      obtain ⟨p, hn, hL⟩ := (ih y M).mp hstate
      exact ⟨.tail p i b hy hz, by simp [PatchArcChain.labels, hn],
        by simp [PatchArcChain.length, hL]⟩
    · rintro ⟨p, hn, hL⟩
      cases p with
      | point ha => simp [PatchArcChain.labels] at hn
      | @tail y p i z hy hb =>
        have hn' : p.labels.length = n := by simpa [PatchArcChain.labels] using hn
        apply Set.mem_iUnion.mpr
        refine ⟨i, ⟨((y, p.length), b), ⟨⟨?_, hy⟩, hb⟩, ?_⟩⟩
        · exact (ih y p.length).mpr ⟨p, hn', rfl⟩
        · exact Prod.ext rfl hL

def boundedPatchChainStates {ι : Type*} (patch : ι → Set ℝ³) (a : ℝ³) (N : ℕ) :
    Set (ℝ³ × ℝ) := ⋃ n : Fin (N + 1), patchChainStates patch a n.val

theorem boundedPatchChainStates_compact {ι : Type*} [Finite ι]
    (patch : ι → Set ℝ³) (hcompact : ∀ i, IsCompact (patch i)) (a : ℝ³) (N : ℕ) :
    IsCompact (boundedPatchChainStates patch a N) :=
  isCompact_iUnion (fun n => patchChainStates_compact patch hcompact a n.val)

/-- Compact local patches admit a globally shortest patch chain whenever any
chain exists. The bound needed for compactness is proved by eliminating
repeated patch labels; shortest-chain existence is not an assumption. -/
theorem shortest_patch_chain_exists {ι : Type*} [Fintype ι]
    (patch : ι → Set ℝ³) (hcompact : ∀ i, IsCompact (patch i))
    (hunit : ∀ i x, x ∈ patch i → ‖x‖ = 1)
    (a b : ℝ³) (ha : ‖a‖ = 1) (p₀ : PatchArcChain patch a b) :
    ∃ p : PatchArcChain patch a b, ∀ q : PatchArcChain patch a b, p.length ≤ q.length := by
  let N := Fintype.card ι
  let S : Set (ℝ³ × ℝ) := boundedPatchChainStates patch a N ∩ {q | q.1 = b}
  have hS : IsCompact S := (boundedPatchChainStates_compact patch hcompact a N).inter_right
    (isClosed_eq continuous_fst continuous_const)
  have hbounded : ∀ q : PatchArcChain patch a b, q.labels.length ≤ N → (b, q.length) ∈ S := by
    intro q hq
    refine ⟨Set.mem_iUnion.mpr ⟨⟨q.labels.length, by omega⟩, ?_⟩, rfl⟩
    exact (mem_patchChainStates_iff patch a ha q.labels.length b q.length).mpr ⟨q, rfl, rfl⟩
  have hSne : S.Nonempty := by
    obtain ⟨q, hq, _⟩ := p₀.compressed_link_bound hunit
    exact ⟨(b, q.length), hbounded q hq⟩
  obtain ⟨⟨x, L⟩, hxS, hmin⟩ := hS.exists_isMinOn hSne continuous_snd.continuousOn
  have hxb : x = b := hxS.2
  subst x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxS.1
  obtain ⟨p, hpcount, hplen⟩ := (mem_patchChainStates_iff patch a ha n.val b L).mp hn
  refine ⟨p, ?_⟩
  intro q
  obtain ⟨r, hr, hrlen⟩ := q.compressed_link_bound hunit
  have hmin' : L ≤ r.length := hmin (hbounded r hr)
  rw [hplen]
  exact hmin'.trans hrlen

end SquareAntiprismVerification
