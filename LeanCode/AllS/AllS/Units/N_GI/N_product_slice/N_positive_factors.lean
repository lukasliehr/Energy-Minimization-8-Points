import AllS.Units.N_G.N_product_gauge

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def productFactor (Y : Fin 8 → Point) (i : Fin 8) : ℝ := inner ℝ (packingReference i) (Y i)
def gnomonicTangent (Y : Fin 8 → Point) (i : Fin 8) : Point :=
  (productFactor Y i)⁻¹ • Y i-packingReference i

def IsProductAligned (Y : Fin 8 → Point) : Prop :=
  ∀a∈gaugeActions,gaugeProduct Y a≤∏i,max (productFactor Y i) 0

theorem productGauge_aligned_value (Y : Fin 8 → Point) (hal : IsProductAligned Y) :
    productGauge Y=∏i,max (productFactor Y i) 0 := by
  obtain ⟨a,ha,he,hm⟩ := (product_gauge_attained_extrema Y).1
  apply le_antisymm
  · rw [he];exact hal a ha
  · exact gaugeProduct_le_productGauge Y (ContinuousLinearMap.id ℝ Point,Equiv.refl _)
      ⟨fun _ => rfl,Set.mem_univ _⟩

theorem product_positive_factors (Y : Fin 8 → Point)
    (hp : 0<∏i,max (productFactor Y i) 0) : ∀i,0<productFactor Y i := by
  intro i
  by_contra hn
  have hz : max (productFactor Y i) 0=0 := max_eq_right (le_of_not_gt hn)
  have hzprod : (∏j,max (productFactor Y j) 0)=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  linarith

theorem gnomonicTangent_orthogonal (Y : Fin 8 → Point) (i : Fin 8) (hi : 0<productFactor Y i) :
    inner ℝ (packingReference i) (gnomonicTangent Y i)=0 := by
  simp only [gnomonicTangent,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,packingReference_norm,one_pow]
  change (productFactor Y i)⁻¹*productFactor Y i-1=0
  rw [inv_mul_cancel₀ hi.ne',sub_self]

theorem product_slice_positive_factors (Y : Fin 8 → Point)
    (hal : IsProductAligned Y) (hp : 0<productGauge Y) :
    ∀i,0<productFactor Y i ∧ inner ℝ (packingReference i) (gnomonicTangent Y i)=0 := by
  rw [productGauge_aligned_value Y hal] at hp
  intro i
  have hi := product_positive_factors Y hp i
  exact ⟨hi,gnomonicTangent_orthogonal Y i hi⟩

#print axioms product_slice_positive_factors
end Blueprint.Thomson.Tail.Implementation
