import AllS.Units.N_F.N_certificate
import AllS.Units.N_F.N_moment_pos
import AllS.Units.N_F.N_counting

noncomputable section
namespace Blueprint.Thomson.Finite

theorem centeredPolynomial_distinctSum (Y : Configuration) (H : Polynomial ℝ) (e : ℝ) :
    distinctPolySum Y (centeredPolynomial H e)=12*(polyPairEnergy H Y-e) := by
  unfold distinctPolySum polyOnTriples
  simp only [centeredPolynomial_eval,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact counting_pair_identity (fun t => H.eval t) e Y

theorem normalizedTarget_distinctSum (s a β : ℝ) (m : Fin 5 → ℕ) (Y : Configuration) :
    distinctPolySum Y (normalizedTarget s a β m)=
      12*β*(polyPairEnergy (hermitePolynomial s a m) Y-Ehat s (X a)) := by
  rw [normalizedTarget,distinctPolySum_C_mul,centeredPolynomial_distinctSum]
  ring

def SummedCertificateContract : Prop := ∀ s a D m,Certificate s a D m →
  ∀ Y : Configuration,IsConfiguration Y →
  ∃ p : MomentPivots (D/2),∃ β : ℝ,∃ W : GramFamily (D/2),
    ValidMomentPivots p ∧ 0<β ∧ (∀ b,(W.val b).PosDef) ∧
      gramPoly a (D/2) p W=normalizedTarget s a β m ∧
      0 ≤ 12*β*(polyPairEnergy (hermitePolynomial s a m) Y-Ehat s (X a))

theorem energy_lower_summed_certificate : SummedCertificateContract := by
  intro s a D m h Y hY
  obtain ⟨p,β,W,hp,hβ,hW,he⟩ := h.witness
  refine ⟨p,β,W,hp,hβ,hW,he,?_⟩
  have hn := moment_pos_nonnegative_pairing a (D/2) p W (fun b => (hW b).posSemidef) Y hY.1
  rwa [he,normalizedTarget_distinctSum] at hn

theorem certificate_hermite_energy_lower {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y) :
    Ehat s (X a) ≤ polyPairEnergy (hermitePolynomial s a m) Y := by
  obtain ⟨p,β,W,hp,hβ,hW,he,hn⟩ := energy_lower_summed_certificate s a D m h Y hY
  have hscale : 0<12*β := by positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hscale).mp hn)

#check energy_lower_summed_certificate
#print axioms energy_lower_summed_certificate
end Blueprint.Thomson.Finite
