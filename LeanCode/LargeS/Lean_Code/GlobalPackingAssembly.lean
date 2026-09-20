import Lean_Code.ContactTilingRigidity
import Lean_Code.OrbitClosure

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The precise remaining contact-cell construction obligation. This is a
proposition, not an axiom or a proof of existence. -/
def IrreducibleContactDecomposition : Prop :=
  ∀ (Y : Fin 8 → ℝ³) (c : ℝ), IsConfiguration Y → 0 < c → c ≤ aInf →
    PackingInnerBound c Y → PackingIrreducible c Y → (packingContacts c Y).Nonempty →
      ∃ D : ContactTilingData Y c, D.BoundaryAdjacency

theorem global_packing_bound_of_decomposition (hdecomp : IrreducibleContactDecomposition)
    (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1) : aInf ≤ packingMaxInner Y := by
  obtain ⟨Z, hZ, hc, hcupper, hmin⟩ := packing_maximum_exists
  obtain ⟨W, hW, _hnear, hmax, hirr, hcontact⟩ := maximizing_irreducible_reduction Z hZ.1 hmin 1 (by norm_num)
  have hbound : PackingInnerBound (packingMaxInner Z) W :=
    (packingMaxInner_le_iff W _).mp hmax.le
  have hWconfig := packingInnerBound_configuration W (packingMaxInner Z) hW
    (hcupper.trans_lt aInf_mem_Ioo.2) hbound
  obtain ⟨D, _hboundary⟩ := hdecomp W (packingMaxInner Z) hWconfig hc hcupper hbound hirr hcontact
  exact (D.packing_bound hWconfig hc hcupper).trans (hmin Y hY)

theorem global_packing_rigidity_of_decomposition (hdecomp : IrreducibleContactDecomposition)
    (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1) (hbound : PackingInnerBound aInf Y) :
    Congruent Y P := by
  have hmax : packingMaxInner Y = aInf := le_antisymm ((packingMaxInner_le_iff Y _).mpr hbound)
    (global_packing_bound_of_decomposition hdecomp Y hY)
  have hmin : ∀ Z : Fin 8 → ℝ³, (∀ i, ‖Z i‖ = 1) → packingMaxInner Y ≤ packingMaxInner Z := by
    intro Z hZ
    rw [hmax]
    exact global_packing_bound_of_decomposition hdecomp Z hZ
  apply congruent_of_arbitrarily_close P Y
  intro ε hε
  obtain ⟨Z, hZ, hnear, hZequal, hirr, hcontact⟩ := maximizing_irreducible_reduction Y hY hmin ε hε
  rw [hmax] at hZequal hirr hcontact
  have hZbound : PackingInnerBound aInf Z := (packingMaxInner_le_iff Z aInf).mp hZequal.le
  have hZconfig := packingInnerBound_configuration Z aInf hZ aInf_mem_Ioo.2 hZbound
  obtain ⟨D, hboundary⟩ := hdecomp Z aInf hZconfig aInf_mem_Ioo.1 le_rfl hZbound hirr hcontact
  exact ⟨Z, hnear, contact_tiling_rigidity Z hZconfig hZbound D hboundary⟩

theorem packing_rigidity_interface_of_decomposition (hdecomp : IrreducibleContactDecomposition)
    (Y : Fin 8 → ℝ³) (hY : ∀ i, Y i ∈ unitSphere)
    (hsep : ∀ i j, i ≠ j → tau ≤ ‖Y i - Y j‖ ^ 2) : Congruent Y P := by
  apply global_packing_rigidity_of_decomposition hdecomp Y hY
  intro i j hij
  have h := hsep i j hij
  rw [sphere_sq_distance _ _ (hY i) (hY j)] at h
  unfold tau at h
  linarith

end SquareAntiprismVerification
