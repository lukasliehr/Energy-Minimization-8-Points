import Lean_Code.RotationSystem
import Lean_Code.PermutationFixedSpace

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma fin_successor_invariant_constant {n : ℕ} {β : Type*} (f : Fin (n + 1) → β)
    (h : ∀ k, f (k + 1) = f k) (i j : Fin (n + 1)) : f i = f j := by
  have hzero (k : Fin (n + 1)) : f k = f 0 := by
    induction k using Fin.induction with
    | zero => rfl
    | succ k ih =>
      have hn : k.castSucc ≠ Fin.last n := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
      have heq : k.castSucc + 1 = k.succ := by
        apply Fin.ext
        rw [Fin.val_add_one, if_neg hn]
        rfl
      have hs : f k.succ = f k.castSucc := by simpa only [heq] using h k.castSucc
      exact hs.trans ih
  exact (hzero i).trans (hzero j).symm

theorem ContactOrderData.successor_invariant_constant
    {Y : Fin 8 → ℝ³} {c : ℝ} {i : Fin 8} (D : ContactOrderData Y c i)
    {β : Type*} (f : ContactNeighbor Y c i → β) (hf : ∀ j, f (D.successor j) = f j)
    (j k : ContactNeighbor Y c i) : f j = f k := by
  obtain ⟨a, rfl⟩ := D.labelEquiv.surjective j
  obtain ⟨b, rfl⟩ := D.labelEquiv.surjective k
  apply fin_successor_invariant_constant (fun l => f (D.labelEquiv l)) _ a b
  intro l
  simpa only [D.successor_label] using hf (D.labelEquiv l)

theorem contactRotate_invariant_at_base (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    {β : Type*} (v : ContactDart Y c → β)
    (hv : ∀ d, v (contactRotate Y c hY hc d) = v d)
    (i : Fin 8) (j k : ContactNeighbor Y c i) : v ⟨i, j⟩ = v ⟨i, k⟩ := by
  classical
  have hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c := ⟨j, j.property⟩
  let D := Classical.choice (contact_order_exists Y c i hY hc hne)
  apply D.successor_invariant_constant (fun j => v ⟨i, j⟩) _ j k
  intro l
  have h := hv ⟨i, l⟩
  change v ⟨i, contactRotateAt Y c hY hc i l⟩ = v ⟨i, l⟩ at h
  simpa only [contactRotateAt, dif_pos hne] using h

def contactBaseDart (Y : Fin 8 → ℝ³) (c : ℝ)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) (i : Fin 8) : ContactDart Y c :=
  ⟨i, ⟨Classical.choose (hne i), Classical.choose_spec (hne i)⟩⟩

/-- Functions fixed by rotation are precisely functions on the eight
vertices, once isolated vertices have been excluded. -/
def contactRotationFixedEquiv (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    (Fin 8 → ℝ) ≃ₗ[ℝ] isometryFixed (permutationIsometry (contactRotate Y c hY hc)) where
  toFun f := ⟨WithLp.toLp 2 (fun d : ContactDart Y c => f d.1), by
    change permutationIsometry (contactRotate Y c hY hc) _ = _
    ext d
    rfl⟩
  invFun v i := v.val (contactBaseDart Y c hne i)
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    ext d
    change v.val (contactBaseDart Y c hne d.1) = v.val d
    exact contactRotate_invariant_at_base Y c hY hc v.val
      (fun d => congrArg (fun w : EuclideanSpace ℝ (ContactDart Y c) => w d) v.property)
      d.1 (contactBaseDart Y c hne d.1).2 d.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contact_rotation_orbit_count (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) :
    Fintype.card (PermutationOrbit (contactRotate Y c hY hc)) = 8 := by
  rw [← permutation_fixed_finrank, ← (contactRotationFixedEquiv Y c hY hc hne).finrank_eq]
  simp

lemma permutation_isometry_fixed_symm {α : Type*} [Fintype α] (e : Equiv.Perm α) :
    isometryFixed (permutationIsometry e.symm) = isometryFixed (permutationIsometry e) := by
  ext v
  constructor
  · intro hv
    change permutationIsometry e v = v
    ext i
    change v (e i) = v i
    have h := congrArg (fun w : EuclideanSpace ℝ α => w (e i)) hv
    change v (e.symm (e i)) = v (e i) at h
    simpa only [e.symm_apply_apply] using h.symm
  · intro hv
    change permutationIsometry e.symm v = v
    ext i
    change v (e.symm i) = v i
    have h := congrArg (fun w : EuclideanSpace ℝ α => w (e.symm i)) hv
    change v (e (e.symm i)) = v (e.symm i) at h
    simpa only [e.apply_symm_apply] using h.symm

lemma permutation_orbit_symm_card {α : Type*} [Fintype α] (e : Equiv.Perm α) :
    Fintype.card (PermutationOrbit e.symm) = Fintype.card (PermutationOrbit e) := by
  rw [← permutation_fixed_finrank, permutation_isometry_fixed_symm, permutation_fixed_finrank]

theorem contact_joint_invariants_constant (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
    (v : EuclideanSpace ℝ (ContactDart Y c))
    (hrev : ∀ d, v (contactReverse Y c d) = v d)
    (hrot : ∀ d, v ((contactRotate Y c hY hc).symm d) = v d) :
    ∀ d e, v d = v e := by
  have hrot' (d : ContactDart Y c) : v (contactRotate Y c hY hc d) = v d := by
    simpa only [Equiv.symm_apply_apply] using (hrot (contactRotate Y c hY hc d)).symm
  let g : Fin 8 → ℝ := fun i => v (contactBaseDart Y c hne i)
  have hbase (d : ContactDart Y c) : v d = g d.1 :=
    contactRotate_invariant_at_base Y c hY hc v hrot' d.1 d.2 (contactBaseDart Y c hne d.1).2
  have hadj (i j : Fin 8) (hij : ContactAdj Y c i j) : g i = g j := by
    let d : ContactDart Y c := ⟨i, ⟨j, hij.1.symm, hij.2⟩⟩
    exact (hbase d).symm.trans ((hrev d).symm.trans (hbase (contactReverse Y c d)))
  have hne' (i : Fin 8) : ∃ j, ContactAdj Y c i j := by
    obtain ⟨j, hj, hc⟩ := hne i
    exact ⟨j, hj.symm, hc⟩
  have hpath (i j : Fin 8) : ContactReachable Y c i j := by
    apply (mem_contactComponent Y c i j).mp
    rw [unique_nontrivial_contact_component Y c hY.1 hc.1 hcupper hirr i j (hne' i) (hne' j)]
    exact contactComponent_root Y c j
  have hg (i j : Fin 8) : g i = g j := by
    have hp := hpath i j
    induction hp with
    | refl => rfl
    | tail hpath hstep ih => exact ih.trans (hadj _ _ hstep)
  intro d e
  exact (hbase d).trans ((hg d.1 e.1).trans (hbase e).symm)

end SquareAntiprismVerification
