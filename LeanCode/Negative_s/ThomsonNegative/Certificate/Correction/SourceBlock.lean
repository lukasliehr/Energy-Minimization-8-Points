import ThomsonNegative.Certificate.Correction.SourceSound
import ThomsonNegative.Certificate.Correction.SourceLayout

noncomputable section
namespace ThomsonNegative.Certificate.Correction.Source

/-- Physical symmetric Gram block of the shared correction table. -/
def blockLinear (u : ℝ) (b : Fin 8) (x : Fin 68 → ℝ) :
    Matrix (Fin (blockSize b)) (Fin (blockSize b)) ℝ :=
  fun i j => rowLinear u (blockIndex b i j) x

lemma blockLinear_symmetric (u : ℝ) (b : Fin 8) (x : Fin 68 → ℝ)
    (i j : Fin (blockSize b)) : blockLinear u b x i j=blockLinear u b x j i := by
  simp only [blockLinear,blockIndex_symmetric b i j]

end ThomsonNegative.Certificate.Correction.Source
