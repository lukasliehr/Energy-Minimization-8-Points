import ThomsonNegative.Certificate.Correction.Inverse.ShiftSound
import ThomsonNegative.Certificate.Correction.Inverse.Kernel
namespace ThomsonNegative.Certificate.Correction.Inverse
open ThomsonNegative.Structure.Exact
lemma segment_true (p : ℕ → Bool) (start count : ℕ)
    (h : allBelow count (fun k => p (Nat.add start k))=true)
    (j : ℕ) (hl : start≤j) (hr : j<start+count) : p j=true := by
  have hh := allBelow_spec _ _ h (j-start) (by omega)
  have he : Nat.add start (j-start)=j := by change start+(j-start)=j; omega
  rwa [he] at hh
end ThomsonNegative.Certificate.Correction.Inverse
