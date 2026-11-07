import ThomsonNegative.Certificate.ImageSound
import ThomsonNegative.Certificate.ResidualSound
import ThomsonNegative.Certificate.StoredSound
import ThomsonNegative.Compact.Packed.InputSound

/-! Shared semantic composition for every cell and every Gram block. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

def basisFunction (a : ℝ → ℝ) (b i j : ℕ) (t : ℝ) : ℝ :=
  (BasisData.record (BasisLayout.index b i j)).eval (a t-83/256)

theorem basisMatrix_sound {N S B W : ℕ} (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (hok : basisGate (mkCtx N S B W) A=true)
    (b : Fin 8) (i j : ℕ) (hi : i<BasisLayout.rawOrder b.val) (hj : j<BasisLayout.freeOrder b.val) :
    Encl (mkCtx N S B W) (entry (basisMatrix (basisModels (mkCtx N S B W) A) b.val) i j)
      (basisFunction a b.val i j) := by
  rw [show entry (basisMatrix (basisModels (mkCtx N S B W) A) b.val) i j =
    (basisModels (mkCtx N S B W) A).getD (BasisLayout.index b.val i j) zeroTM from
      entry_tabulate _ hi hj]
  exact basisModels_sound hg ha hok _ (basis_index_lt b i j hi hj)

theorem blockTM_sound {N S B W : ℕ} (hg : Good N S B W) {T : TM} {x : ℝ → ℝ}
    (hT : Encl (mkCtx N S B W) T x) (order degree count : ℕ) (K : FactorData)
    (F : ℕ → FactorData) (hok : allOk (blockTM (mkCtx N S B W) order degree count T K F)=true)
    (i j : ℕ) (hi : i<order) (hj : j<order) :
    Encl (mkCtx N S B W) (entry (blockTM (mkCtx N S B W) order degree count T K F) i j)
      (fun t => gramValue degree count K F (x t) i j) := by
  have he : entry (blockTM (mkCtx N S B W) order degree count T K F) i j=
      blockEntryTM (mkCtx N S B W) degree count T K F i j := entry_tabulate _ hi hj
  rw [he]
  exact blockEntryTM_sound hg hT degree count K F i j (by rw [← he]; exact allOk_entry hok i j)

theorem image_checkpoint_sound {N S B W : ℕ} (hg : Good N S B W)
    {A T : TM} {a x : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (hT : Encl (mkCtx N S B W) T x)
    (b : Fin 8) (degree count : ℕ) (K : FactorData) (F : ℕ → FactorData)
    (hBasis : basisGate (mkCtx N S B W) A=true)
    (hGram : allOk (blockTM (mkCtx N S B W) (BasisLayout.freeOrder b.val) degree count T K F)=true)
    (hImage : (blockImage (mkCtx N S B W) (basisModels (mkCtx N S B W) A) b.val
      (blockTM (mkCtx N S B W) (BasisLayout.freeOrder b.val) degree count T K F)).ok=true)
    (stored : List TM)
    (hStored : sameModels
      (blockImage (mkCtx N S B W) (basisModels (mkCtx N S B W) A) b.val
        (blockTM (mkCtx N S B W) (BasisLayout.freeOrder b.val) degree count T K F)).coefficients stored=true)
    (r : ℕ) (hr : r<68) :
    Encl (mkCtx N S B W) (stored.getD r zeroTM)
      (imageFunction b.val r (basisFunction a b.val)
        (fun i j t => gramValue degree count K F (x t) i j)) := by
  rw [← sameModels_eq hStored]
  exact blockImage_sound hg _ b _ _ _
    (fun i hi j hj => basisMatrix_sound hg ha hBasis b i j hi hj)
    (fun i hi j hj => blockTM_sound hg hT _ degree count K F hGram i j hi hj)
    hImage r hr

def standardContext : Ctx := mkCtx 10 384 448 1024
def standardTau : TM := ofPQ standardContext (Nat.shiftLeft standardContext.twoS standardContext.W) 0 0

theorem standardContext_good : Good 10 384 448 1024 := by
  constructor <;> decide +kernel

theorem standardTau_sound : Encl standardContext standardTau (fun t => t) := by
  have h := affineInput_zero_sound standardContext_good 0 (2^384)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : affineInput standardContext 0 (2^384) 0=standardTau := by
    unfold affineInput standardTau
    rw [Nat.add_eq,zero_add]
    rfl
  change Encl standardContext (affineInput standardContext 0 (2^384) 0) _ at h
  rw [he] at h
  exact h.congr (fun t _ => by push_cast; field_simp <;> ring)

#print axioms image_checkpoint_sound
#print axioms standardTau_sound
end ThomsonNegative.Certificate
