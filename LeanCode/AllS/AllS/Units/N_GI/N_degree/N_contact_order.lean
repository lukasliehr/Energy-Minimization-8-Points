import AllS.Units.N_GI.N_setup.N_aliases
import Lean_Code.ContactOrder

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem degree_contact_order (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (i : Fin 8) (hne : ∃j, j≠i ∧ inner ℝ (Y i) (Y j)=c) :
    ∃ D : ContactOrderData Y c i,
      (∀k, Real.arccos (c/(1+c))≤D.gap k) ∧
      (∀k,D.gap k<Real.pi) ∧ (∑k,D.gap k)=2*Real.pi := by
  have hc1 : c∈Set.Ioo (0:ℝ) 1 := ⟨hc,by linarith⟩
  obtain ⟨D⟩ := contact_order_exists Y c i hY hc1 hne
  exact ⟨D,D.gap_lower_bound hY.1 hc1 hirr hbound,D.gap_lt_pi hY.1 hc1 hirr,D.gap_sum⟩

end Blueprint.Thomson.Tail.Implementation
