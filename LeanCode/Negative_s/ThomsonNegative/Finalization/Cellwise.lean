import ThomsonNegative.Finalization.Cells

noncomputable section
namespace ThomsonNegative.Finalization
open ThomsonNegative.Structure ThomsonNegative.Certificate ThomsonNegative.Geometry

/-- Only the actually enclosed cell heights need regular source denominators. -/
theorem cellSpec_of_cellwiseRepair (d : MatrixCell) (c : Fin 5) (f : FourFloors d c)
    (repair : ∀ t : ℝ,t ∈ Set.Icc (-1:ℝ) 1 →
      ExactRepair (Compact.Target.ScalarCells.heightFunction c t)) :
    CellSpec (cellLower c) (cellUpper c)
      (fun q => Bridges.sourcePolynomialFamily (aStar (2*q-2))) := by
  intro q hc hq
  obtain ⟨t,ht,he⟩ := Compact.Target.ScalarCells.parameter_on_cell c q
    (by simpa [cellLower,cellUpper] using hc)
  simpa only [he] using cell_certificate d c f t ht (by rwa [he]) (repair t ht)

theorem negative_thomson_of_cellwiseRepair
    (repair : ∀ (c : Fin 5) (t : ℝ),t ∈ Set.Icc (-1:ℝ) 1 →
      ExactRepair (Compact.Target.ScalarCells.heightFunction c t))
    (s : ℝ) (hs : s ∈ Set.Ioo (-2:ℝ) 0) : IsUniqueMinimizer s (X (aStar s)) := by
  apply negative_thomson_of_five_cells
    (fun q => Bridges.sourcePolynomialFamily (aStar (2*q-2)))
    (fun q hq b => Bridges.sourcePolynomialFamily_realization _ b)
    (fun c => cellSpec_of_cellwiseRepair (matrixData c) c (fourFloors c) (repair c)) s hs

#print axioms negative_thomson_of_cellwiseRepair
end ThomsonNegative.Finalization
