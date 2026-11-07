import ThomsonNegative.Finalization.SourceRepair

noncomputable section
namespace ThomsonNegative.Finalization
open ThomsonNegative.Structure ThomsonNegative.Certificate ThomsonNegative.Geometry

/-- An exact right inverse together with explicit identifications of its fixed
source maps. No energy, positivity, or cell-certificate statement is a field. -/
structure ExactRepair (a : ℝ) where
  system : HybridCoefficientSystem
  inverse : HybridRightInverse system
  family_eq : system.family=Bridges.sourcePolynomialFamily a
  coefficient_eq : system.coefficientMap=Bridges.coefficientMap a
  value_eq : system.compatibility.ell0=coefficientEll0 a
  slope_eq : system.compatibility.ell1=coefficientEll1 a
  correction_eq : inverse.correction=sourceCorrection (a-83/256)

lemma scalar_interior (c : Fin 5) (t : ℝ)
    (hq : Compact.Target.ScalarCells.parameter c t ∈ Set.Ioo (0:ℝ) 1) :
    Compact.Target.ScalarCells.heightFunction c t=
        aStar (2*Compact.Target.ScalarCells.parameter c t-2) ∧
    Compact.Target.ScalarCells.polynomialFunction c t=
        concreteH (Compact.Target.ScalarCells.parameter c t) (Compact.Target.ScalarCells.heightFunction c t) := by
  obtain ⟨ha,hH⟩ := Compact.Target.ScalarCells.interior_bridge c t hq
  refine ⟨ha,?_⟩
  rw [hH,ha,Compact.Target.sourceContact_eq_contacts]
  rfl

theorem cell_certificate (d : MatrixCell) (c : Fin 5) (f : FourFloors d c)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1)
    (hq : Compact.Target.ScalarCells.parameter c t ∈ Set.Ioo (0:ℝ) 1)
    (r : ExactRepair (Compact.Target.ScalarCells.heightFunction c t)) :
    Certificate (Compact.Target.ScalarCells.parameter c t)
      (aStar (2*Compact.Target.ScalarCells.parameter c t-2))
      (Bridges.sourcePolynomialFamily (aStar (2*Compact.Target.ScalarCells.parameter c t-2))) := by
  obtain ⟨ha,hH⟩ := scalar_interior c t hq
  let v := Bridges.targetCoefficients (Compact.Target.ScalarCells.polynomialFunction c t)
    (MatrixCell.energyFunction c t)
  have hcompatible : coefficientEll0 (Compact.Target.ScalarCells.heightFunction c t) v=0 ∧
      coefficientEll1 (Compact.Target.ScalarCells.heightFunction c t) v=0 := by
    dsimp [v,MatrixCell.energyFunction]
    rw [hH,ha]
    exact Bridges.targetCoefficients_compatible _ hq.1
  have hcorrected : r.inverse.corrected r.system v (d.initialFamily t)=correctedFamily d c t := by
    simp only [HybridRightInverse.corrected,r.coefficient_eq,r.correction_eq,correctedFamily,
      MatrixCell.sourceResidual,v]
  have hid := r.inverse.corrected_gram_identity r.system v (d.initialFamily t)
    (Bridges.targetCoefficients_highCompatible _ _)
    (by rw [r.value_eq]; exact hcompatible.1)
    (by rw [r.slope_eq]; exact hcompatible.2)
  rw [r.family_eq,hcorrected] at hid
  have htarget : physicalSynthesize v=centeredPolynomial
      (concreteH (Compact.Target.ScalarCells.parameter c t)
        (Compact.Target.ScalarCells.heightFunction c t)) (MatrixCell.energyFunction c t) := by
    dsimp [v]
    rw [hH]
    exact Bridges.targetCoefficients_physical _ (concreteH_degree _ _) _
  rw [htarget] at hid
  rw [← ha]
  refine ⟨correctedFamily d c t,fun b => correctedFamily_psd d c f t ht b,?_⟩
  exact hid

theorem cellSpec_of_data (d : MatrixCell) (c : Fin 5) (f : FourFloors d c)
    (repair : ∀ a : ℝ,(5/16:ℝ)<a → a<1/3 → ExactRepair a) :
    CellSpec (cellLower c) (cellUpper c)
      (fun q => Bridges.sourcePolynomialFamily (aStar (2*q-2))) := by
  intro q hc hq
  obtain ⟨t,ht,he⟩ := Compact.Target.ScalarCells.parameter_on_cell c q
    (by simpa [cellLower,cellUpper] using hc)
  have ha := Compact.Target.ScalarCells.height_range c t ht
  simpa only [he] using cell_certificate d c f t ht (by rwa [he]) (repair _ ha.1 ha.2)

theorem negative_thomson_of_data (d : Fin 5 → MatrixCell)
    (floor : ∀ c,FourFloors (d c) c)
    (repair : ∀ a : ℝ,(5/16:ℝ)<a → a<1/3 → ExactRepair a)
    (s : ℝ) (hs : s ∈ Set.Ioo (-2:ℝ) 0) : IsUniqueMinimizer s (X (aStar s)) := by
  apply negative_thomson_of_five_cells
    (fun q => Bridges.sourcePolynomialFamily (aStar (2*q-2)))
    (fun q hq b => Bridges.sourcePolynomialFamily_realization _ b)
    (fun c => cellSpec_of_data (d c) c (floor c) repair) s hs

#print axioms cell_certificate
#print axioms negative_thomson_of_data
end ThomsonNegative.Finalization
