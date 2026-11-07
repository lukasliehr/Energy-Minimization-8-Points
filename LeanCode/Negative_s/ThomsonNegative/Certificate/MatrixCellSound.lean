import ThomsonNegative.Certificate.MatrixCellKernel
import ThomsonNegative.Certificate.Bridges.ProgramBridge
import ThomsonNegative.Compact.Target.ScalarCells

/-! All numerical operations are assembled here into the exact source residual. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Structure

structure MatrixCell.Checked (d : MatrixCell) (i : Fin 5) : Prop where
  basis : basisGate MatrixCell.context (Compact.Target.ScalarCells.heightCheckpoint i)=true
  gram : ∀ b : Fin 8, allOk (d.initial b.val)=true
  image : ∀ b : Fin 8,
    (blockImage MatrixCell.context (basisModels MatrixCell.context
      (Compact.Target.ScalarCells.heightCheckpoint i)) b.val (d.initial b.val)).ok=true
  checkpoint : ∀ b : Fin 8, sameModels
    (blockImage MatrixCell.context (basisModels MatrixCell.context
      (Compact.Target.ScalarCells.heightCheckpoint i)) b.val (d.initial b.val)).coefficients
    (d.checkpoint b.val)=true
  residual : sameModels
    (residualTM MatrixCell.context d.images (Compact.Target.ScalarCells.data i).coefficientCheckpoints)
    d.residualCheckpoint=true

def MatrixCell.gramFunction (d : MatrixCell) (b u v : ℕ) (t : ℝ) : ℝ :=
  gramValue 10 11 (d.metric b) (d.factor b) t u v

def MatrixCell.initialFamily (d : MatrixCell) (t : ℝ) : GramFamily :=
  fun b u v => d.gramFunction b.val u.val v.val t

def MatrixCell.energyFunction (i : Fin 5) (t : ℝ) : ℝ :=
  auxEnergy (Compact.Target.ScalarCells.parameter i t) (X (Compact.Target.ScalarCells.heightFunction i t))

def MatrixCell.sourceResidual (d : MatrixCell) (i : Fin 5) (t : ℝ) : ChartSpace :=
  retain (Bridges.targetCoefficients (Compact.Target.ScalarCells.polynomialFunction i t)
    (MatrixCell.energyFunction i t) -
      Bridges.coefficientMap (Compact.Target.ScalarCells.heightFunction i t) (d.initialFamily t))

theorem MatrixCell.checkpoint_encl {i : Fin 5} {d : MatrixCell} (h : d.Checked i)
    (b : Fin 8) (r : ℕ) (hr : r<68) :
    Encl MatrixCell.context ((d.checkpoint b.val).getD r zeroTM)
      (imageFunction b.val r (basisFunction (Compact.Target.ScalarCells.heightFunction i) b.val)
        (d.gramFunction b.val)) := by
  exact image_checkpoint_sound standardContext_good
    (Compact.Target.ScalarCells.height_encl i) standardTau_sound b 10 11
    (d.metric b.val) (d.factor b.val) h.basis (h.gram b) (h.image b)
    (d.checkpoint b.val) (h.checkpoint b) r hr

theorem MatrixCell.residual_encl {i : Fin 5} {d : MatrixCell} (h : d.Checked i)
    (r : Fin 68) : Encl MatrixCell.context (d.residualCheckpoint.getD r.val zeroTM)
      (fun t => d.sourceResidual i t r) := by
  have hI (b : ℕ) (hb : b<8) (s : ℕ) (hs : s<68) :
      Encl MatrixCell.context ((d.images.getD b []).getD s zeroTM)
        (imageFunction b s (basisFunction (Compact.Target.ScalarCells.heightFunction i) b)
          (d.gramFunction b)) := by
    have he : d.images.getD b []=d.checkpoint b := by
      simp [MatrixCell.images,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hb]
    rw [he]
    exact MatrixCell.checkpoint_encl h ⟨b,hb⟩ s hs
  have hH (n : ℕ) (hn : n<8) :
      Encl MatrixCell.context ((Compact.Target.ScalarCells.data i).coefficientCheckpoints.getD n zeroTM)
        (fun t => (Compact.Target.ScalarCells.polynomialFunction i t).coeff n) :=
    Compact.Target.ScalarCells.coefficient_encl i ⟨n,hn⟩
  have hh := residualRowTM_sound standardContext_good d.images
    (Compact.Target.ScalarCells.data i).coefficientCheckpoints _ _ hI hH r.val r.isLt
  have he : (residualTM MatrixCell.context d.images
      (Compact.Target.ScalarCells.data i).coefficientCheckpoints).getD r.val zeroTM =
      residualRowTM MatrixCell.context d.images
        (Compact.Target.ScalarCells.data i).coefficientCheckpoints r.val := by
    simp [residualTM,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range r.isLt]
  have hc := sameModels_eq h.residual
  have hOk : (residualRowTM MatrixCell.context d.images
      (Compact.Target.ScalarCells.data i).coefficientCheckpoints r.val).ok=true := by
    have hall := sameModels_left_ok h.residual
    rw [← he]
    exact list_all_getD TM.ok _ zeroTM rfl hall r.val
  have hb := hh hOk
  have hout : d.residualCheckpoint.getD r.val zeroTM=
      residualRowTM MatrixCell.context d.images
        (Compact.Target.ScalarCells.data i).coefficientCheckpoints r.val := by rw [← hc,he]
  rw [hout]
  apply hb.congr
  intro t ht
  exact Bridges.residualFunction_retained (Compact.Target.ScalarCells.heightFunction i)
    (MatrixCell.energyFunction i) (Compact.Target.ScalarCells.polynomialFunction i)
    d.initialFamily d.gramFunction (fun b u v t => rfl) r t

theorem MatrixCell.initial_psd (d : MatrixCell) (b : Block) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) : (d.initialFamily t b).PosSemidef :=
  gramValue_psd (blockSize b) 10 11 (d.metric b.val) (d.factor b.val) t ht

#print axioms MatrixCell.residual_encl
end ThomsonNegative.Certificate
