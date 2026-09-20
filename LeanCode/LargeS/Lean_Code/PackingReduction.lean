import Lean_Code.PackingPush

open Real
noncomputable section
namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def PackingInnerBound (c : ℝ) (Y : Fin 8 → ℝ³) : Prop :=
  ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ≤ c

def packingContacts (c : ℝ) (Y : Fin 8 → ℝ³) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun ij => ij.1 ≠ ij.2 ∧ inner ℝ (Y ij.1) (Y ij.2) = c)

@[simp] lemma mem_packingContacts (c : ℝ) (Y : Fin 8 → ℝ³) (ij : Fin 8 × Fin 8) :
    ij ∈ packingContacts c Y ↔ ij.1 ≠ ij.2 ∧ inner ℝ (Y ij.1) (Y ij.2) = c := by
  simp [packingContacts]

def PackingIrreducible (c : ℝ) (Y : Fin 8 → ℝ³) : Prop :=
  ∀ i, (∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) →
    ¬ ∃ v : ℝ³, ‖v‖ = 1 ∧ inner ℝ (Y i) v = 0 ∧
      ∀ j, j ≠ i → inner ℝ (Y i) (Y j) = c → inner ℝ v (Y j) ≤ 0

theorem pushing_configuration (Y : Fin 8 → ℝ³) (i : Fin 8) (c : ℝ)
    (hY : ∀ j, ‖Y j‖ = 1) (hc : 0 < c) (hbound : PackingInnerBound c Y)
    (hneighbors : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
    (v : ℝ³) (hv : ‖v‖ = 1) (horth : inner ℝ (Y i) v = 0)
    (hcontact : ∀ j, j ≠ i → inner ℝ (Y i) (Y j) = c → inner ℝ v (Y j) ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Fin 8 → ℝ³, (∀ j, ‖Z j‖ = 1) ∧ PackingInnerBound c Z ∧
      dist Z Y < ε ∧ packingContacts c Z ⊂ packingContacts c Y := by
  classical
  obtain ⟨p, hp, hpdist, hpstrict⟩ := pushing_vertex Y i c hY hc
    (fun j hj => hbound i j hj.symm) v hv horth hcontact ε hε
  let Z : Fin 8 → ℝ³ := fun j => if j = i then p else Y j
  have hZi : Z i = p := by simp [Z]
  have hZother (j : Fin 8) (hj : j ≠ i) : Z j = Y j := by simp [Z, hj]
  have hZunit : ∀ j, ‖Z j‖ = 1 := by
    intro j
    by_cases hj : j = i
    · subst j; rw [hZi]; exact hp
    · rw [hZother j hj]; exact hY j
  have hZstrict (j : Fin 8) (hj : j ≠ i) : inner ℝ (Z i) (Z j) < c := by
    rw [hZi, hZother j hj]
    exact hpstrict j hj
  have hZbound : PackingInnerBound c Z := by
    intro k l hkl
    by_cases hk : k = i
    · subst k
      exact (hZstrict l hkl.symm).le
    · by_cases hl : l = i
      · subst l
        rw [real_inner_comm]
        exact (hZstrict k hk).le
      · rw [hZother k hk, hZother l hl]
        exact hbound k l hkl
  have hZdist : dist Z Y < ε := by
    apply (dist_pi_lt_iff hε).mpr
    intro j
    by_cases hj : j = i
    · subst j; rw [hZi]; exact hpdist
    · rw [hZother j hj, dist_self]; exact hε
  have hsubset : packingContacts c Z ⊆ packingContacts c Y := by
    intro kl hkl
    obtain ⟨hne, heq⟩ := (mem_packingContacts c Z kl).mp hkl
    by_cases hk : kl.1 = i
    · rw [hk] at heq
      exact ((hZstrict kl.2 (by simpa [hk] using hne.symm)).ne heq).elim
    · by_cases hl : kl.2 = i
      · rw [hl, real_inner_comm] at heq
        exact ((hZstrict kl.1 hk).ne heq).elim
      · apply (mem_packingContacts c Y kl).mpr
        exact ⟨hne, by simpa only [hZother kl.1 hk, hZother kl.2 hl] using heq⟩
  have hne : packingContacts c Z ≠ packingContacts c Y := by
    intro heq
    obtain ⟨j, hji, hij⟩ := hneighbors
    have hmem : (i, j) ∈ packingContacts c Y := (mem_packingContacts c Y (i, j)).mpr ⟨hji.symm, hij⟩
    rw [← heq] at hmem
    have hh := ((mem_packingContacts c Z (i, j)).mp hmem).2
    exact (hZstrict j hji).ne hh
  exact ⟨Z, hZunit, hZbound, hZdist, Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩⟩

/-- Arbitrarily close irreducible reduction.  Minimizing the finite contact
count inside an open neighborhood packages the paper's terminating sequence
of pushes without choosing a displacement budget for each step. -/
theorem arbitrarily_close_irreducible_reduction (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ j, ‖Y j‖ = 1) (hc : 0 < c) (hbound : PackingInnerBound c Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Fin 8 → ℝ³, (∀ j, ‖Z j‖ = 1) ∧ PackingInnerBound c Z ∧
      dist Z Y < ε ∧ PackingIrreducible c Z := by
  classical
  let Q : ℕ → Prop := fun n => ∃ Z : Fin 8 → ℝ³,
    (∀ j, ‖Z j‖ = 1) ∧ PackingInnerBound c Z ∧ dist Z Y < ε ∧ (packingContacts c Z).card = n
  have hex : ∃ n, Q n :=
    ⟨(packingContacts c Y).card, Y, hY, hbound, by simpa using hε, rfl⟩
  obtain ⟨Z, hZunit, hZbound, hZdist, hZcard⟩ := Nat.find_spec hex
  refine ⟨Z, hZunit, hZbound, hZdist, ?_⟩
  intro i hneighbor hpush
  obtain ⟨v, hv, horth, hcontact⟩ := hpush
  obtain ⟨W, hWunit, hWbound, hWdist, hWcontacts⟩ := pushing_configuration Z i c
    hZunit hc hZbound hneighbor v hv horth hcontact (ε - dist Z Y) (by linarith)
  have hWY : dist W Y < ε := by
    have htri := dist_triangle W Z Y
    linarith
  have hWQ : Q (packingContacts c W).card := ⟨W, hWunit, hWbound, hWY, rfl⟩
  have hminimal := Nat.find_min' hex hWQ
  have hlt := Finset.card_lt_card hWcontacts
  omega

end SquareAntiprismVerification
