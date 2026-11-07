import ThomsonNegative.Finalization.PositiveCorrection
import ThomsonNegative.Certificate.Correction.SourceBlock
import ThomsonNegative.Structure.Recovery
import ThomsonNegative.Geometry.Assembly

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Finalization
open ThomsonNegative.Structure ThomsonNegative.Certificate
open ThomsonNegative.Geometry

def activeBlock : Fin 4 → Block := ![0,1,6,7]

lemma source_blockSize (b : Block) : Correction.Source.blockSize b.val=blockSize b := by fin_cases b <;> rfl

def sourceCorrection (u : ℝ) : ChartSpace →ₗ[ℝ] GramFamily where
  toFun x b i j := Correction.Source.rowLinear u (Correction.Source.blockIndex b.val i.val j.val) x
  map_add' x y := by funext b i j; exact (Correction.Source.rowLinear u _).map_add x y
  map_smul' c x := by funext b i j; exact (Correction.Source.rowLinear u _).map_smul c x

lemma sourceCorrection_shared (u : ℝ) (x : ChartSpace) (b : Block)
    (i j : Fin (blockSize b)) :
    sourceCorrection u x b i j=Correction.Source.blockLinear u b x
      (Fin.cast (source_blockSize b).symm i) (Fin.cast (source_blockSize b).symm j) := rfl

lemma sourceCorrection_symmetric (u : ℝ) (x : ChartSpace) (b : Block)
    (i j : Fin (blockSize b)) : sourceCorrection u x b i j=sourceCorrection u x b j i := by
  simp only [sourceCorrection_shared]
  exact Correction.Source.blockLinear_symmetric u b x _ _

lemma sourceCorrection_inactive (u : ℝ) (x : ChartSpace) (b : Block)
    (h0 : b≠0) (h1 : b≠1) (h6 : b≠6) (h7 : b≠7) : sourceCorrection u x b=0 := by
  funext i j
  change Correction.Source.rowLinear u (Correction.Source.blockIndex b.val i.val j.val) x=0
  fin_cases b <;> simp_all [Correction.Source.blockIndex,Correction.Source.rowLinear_sentinel]

def correctedFamily (d : MatrixCell) (c : Fin 5) (t : ℝ) : GramFamily :=
  d.initialFamily t+sourceCorrection (Compact.Target.ScalarCells.heightFunction c t-83/256) (d.sourceResidual c t)

/-- The four concrete metric inverses and weighted row estimates consumed by
the final PSD proof. All entries refer to the fixed source correction. -/
structure FourFloors (d : MatrixCell) (c : Fin 5) where
  inverse : Fin 4 → FactorData
  weight : (k : Fin 4) → Fin (blockSize (activeBlock k)) → ℝ
  metric_order : ∀ k,(d.metric (activeBlock k).val).order=blockSize (activeBlock k)
  metric_inverse : ∀ k,(d.metric (activeBlock k).val).matrix (blockSize (activeBlock k))*
    (inverse k).matrix (blockSize (activeBlock k))=1
  positive_weights : ∀ k i,0<weight k i
  rows : ∀ t ∈ Set.Icc (-1:ℝ) 1,∀ k i,
    ∑ j,|((inverse k).matrix (blockSize (activeBlock k))*
      sourceCorrection (Compact.Target.ScalarCells.heightFunction c t-83/256) (d.sourceResidual c t) (activeBlock k)*
      ((inverse k).matrix (blockSize (activeBlock k))).transpose) i j| * weight k j/weight k i≤(1/3:ℝ)

theorem correctedFamily_active_posDef (d : MatrixCell) (c : Fin 5) (f : FourFloors d c)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (k : Fin 4) :
    (correctedFamily d c t (activeBlock k)).PosDef := by
  exact gramValue_correction_posDef (d.metric (activeBlock k).val) (f.inverse k)
    (d.factor (activeBlock k).val) _ (f.metric_order k) (f.metric_inverse k)
    (sourceCorrection_symmetric _ _ _) (f.weight k) (f.positive_weights k)
    (f.rows t ht k) t ht

theorem correctedFamily_psd (d : MatrixCell) (c : Fin 5) (f : FourFloors d c)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (b : Block) :
    (correctedFamily d c t b).PosSemidef := by
  by_cases h : ∃ k,activeBlock k=b
  · obtain ⟨k,rfl⟩ := h
    exact (correctedFamily_active_posDef d c f t ht k).posSemidef
  · have h0 : b≠0 := by intro he; exact h ⟨0,he.symm⟩
    have h1 : b≠1 := by intro he; exact h ⟨1,he.symm⟩
    have h6 : b≠6 := by intro he; exact h ⟨2,he.symm⟩
    have h7 : b≠7 := by intro he; exact h ⟨3,he.symm⟩
    change (d.initialFamily t b+sourceCorrection _ _ b).PosSemidef
    rw [sourceCorrection_inactive _ _ b h0 h1 h6 h7,add_zero]
    exact d.initial_psd b t ht

end ThomsonNegative.Finalization
