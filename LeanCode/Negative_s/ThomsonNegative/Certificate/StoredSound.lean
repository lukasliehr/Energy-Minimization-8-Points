import ThomsonNegative.Certificate.StoredKernel
import ThomsonNegative.Compact.Packed.Comp

/-! Checked block checkpoints preserve the entire model and its enclosure. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

theorem sameTM_eq {a b : TM} (h : sameTM a b=true) : a=b := by
  cases a with
  | mk av aa as ae ao =>
    cases b with
    | mk bv ba bs be bo =>
      simp only [sameTM,Nat.beq_eq,Bool.and_eq_true] at h
      rcases h with ⟨⟨⟨⟨⟨hv,ha⟩,hs⟩,he⟩,hoa⟩,hob⟩
      simp_all

theorem sameModels_eq : ∀ {as bs : List TM}, sameModels as bs=true → as=bs
  | [], [], _ => rfl
  | [], _::_, h => by simp [sameModels] at h
  | _::_, [], h => by simp [sameModels] at h
  | a::as, b::bs, h => by
    simp only [sameModels,Bool.and_eq_true] at h
    rw [sameTM_eq h.1,sameModels_eq h.2]

theorem sameModels_left_ok : ∀ {as bs : List TM}, sameModels as bs=true → as.all TM.ok=true
  | [], [], _ => rfl
  | [], _::_, _ => rfl
  | _::_, [], h => by simp [sameModels] at h
  | a::as, b::bs, h => by
    simp only [sameModels,Bool.and_eq_true] at h
    have ha := h.1
    simp only [sameTM,Bool.and_eq_true] at ha
    simp only [List.all_cons,Bool.and_eq_true]
    exact ⟨ha.1.2,sameModels_left_ok h.2⟩

theorem checkpoint_encl {c : Ctx} {A B : TM} {f : ℝ → ℝ}
    (h : Encl c A f) (he : sameTM A B=true) : Encl c B f := by
  rwa [← sameTM_eq he]

#print axioms sameModels_eq
end ThomsonNegative.Certificate
