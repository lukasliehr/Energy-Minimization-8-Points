import AllS.Units.N_GI.N_push.N_assemble

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail

theorem push (Y : Fin 8 → Point) (i : Fin 8) (c : ℝ)
    (hY : ∀ j, ‖Y j‖ = 1) (hc : 0 < c) (hbound : PackingInnerBound c Y)
    (hneighbors : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
    (v : Point) (hv : ‖v‖ = 1) (horth : inner ℝ (Y i) v = 0)
    (hcontact : ∀ j, j ≠ i → inner ℝ (Y i) (Y j) = c → inner ℝ v (Y j) ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Fin 8 → Point, (∀ j, ‖Z j‖ = 1) ∧ PackingInnerBound c Z ∧
      dist Z Y < ε ∧ packingContacts c Z ⊂ packingContacts c Y :=
  Implementation.push_assemble Y i c hY hc hbound hneighbors v hv horth hcontact ε hε

#print axioms push
end Blueprint.Thomson.Tail
