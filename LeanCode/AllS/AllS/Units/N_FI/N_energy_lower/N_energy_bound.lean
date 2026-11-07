import AllS.Units.N_FI.N_energy_lower.N_summed_certificate
import AllS.Units.N_F.N_hermite
import AllS.Units.N_F.N_geometry

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def EnergyLowerContract : Prop := ∀ s a D m,Certificate s a D m →
  ∀ Y : Configuration,IsConfiguration Y → E s (X a) ≤ E s Y

theorem hermite_pair_energy_le {s a : ℝ} {D : ℕ} {m : Fin 5 → ℕ}
    (h : Certificate s a D m) (Y : Configuration) (hY : IsConfiguration Y) :
    polyPairEnergy (hermitePolynomial s a m) Y ≤ Ehat s Y := by
  unfold polyPairEnergy Ehat PairSum
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hij : i≠j := ne_of_lt (Finset.mem_filter.mp hj).2
  have hne : Y i≠Y j := fun he => hij (hY.2 he)
  have hd := (geometry_distance_domain (Y i) (Y j) (hY.1 i) (hY.1 j) hne).1
  exact (hermite_minorant s a D m h.s_nonneg h.physical_a h.profile_valid).1 _ hd.1 hd.2 |>.1

theorem energy_eq_iff_normalized (s : ℝ) (hs : 0 ≤ s) (Y Z : Configuration)
    (hY : IsConfiguration Y) (hZ : IsConfiguration Z) :
    E s Y=E s Z ↔ Ehat s Y=Ehat s Z := by
  by_cases hs0 : s=0
  · rw [(geometry_energy_normalization s hs Y hY).1 hs0,
      (geometry_energy_normalization s hs Z hZ).1 hs0]
  · have hsp : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
    rw [(geometry_energy_normalization s hs Y hY).2 hsp,
      (geometry_energy_normalization s hs Z hZ).2 hsp]
    constructor <;> intro he <;> nlinarith

theorem energy_lower_energy_bound : EnergyLowerContract := by
  intro s a D m h Y hY
  have hX := candidate_is_configuration a (physical_mem_Ioo a h.physical_a)
  have hn := le_trans (certificate_hermite_energy_lower h Y hY) (hermite_pair_energy_le h Y hY)
  by_cases hs0 : s=0
  · rwa [(geometry_energy_normalization s h.s_nonneg (X a) hX).1 hs0,
      (geometry_energy_normalization s h.s_nonneg Y hY).1 hs0]
  · have hsp : 0<s := lt_of_le_of_ne h.s_nonneg (Ne.symm hs0)
    rw [(geometry_energy_normalization s h.s_nonneg (X a) hX).2 hsp,
      (geometry_energy_normalization s h.s_nonneg Y hY).2 hsp]
    nlinarith

#check energy_lower_energy_bound
#print axioms energy_lower_energy_bound
end Blueprint.Thomson.Finite
