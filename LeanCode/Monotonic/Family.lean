import LeanCode.Monotonic.Scalar
import LeanCode.Monotonic.Operators

noncomputable section
open Real Set
namespace SquareAntiprismCounterexample

lemma dA_hasDerivAt (a : ℝ) : HasDerivAt dA (-2) a := by
  convert! ((hasDerivAt_const a (1:ℝ)).sub (hasDerivAt_id a)).const_mul 2 using 1
  norm_num
lemma dB_hasDerivAt (a : ℝ) : HasDerivAt dB (-4) a := by
  convert! ((hasDerivAt_const a (1:ℝ)).sub (hasDerivAt_id a)).const_mul 4 using 1
  norm_num
lemma dC_hasDerivAt (a : ℝ) : HasDerivAt dC (2+√2) a := by
  convert! ((hasDerivAt_id a).const_mul (2+√2)).const_add (2-√2) using 1
  norm_num
lemma dD_hasDerivAt (a : ℝ) : HasDerivAt dD (2-√2) a := by
  convert! ((hasDerivAt_id a).const_mul (2-√2)).const_add (2+√2) using 1
  norm_num

lemma family_hasDerivAt (v p : ℝ → ℝ)
    (hv : ∀ t, 0 < t → HasDerivAt v (p t) t)
    {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : HasDerivAt (G v) (L a p) a := by
  obtain ⟨haA, haB, haC, haD⟩ := distance_domains ha
  have hA := ((hv _ haA.1).comp a (dA_hasDerivAt a)).const_mul 8
  have hB := ((hv _ haB.1).comp a (dB_hasDerivAt a)).const_mul 4
  have hC := ((hv _ haC.1).comp a (dC_hasDerivAt a)).const_mul 8
  have hD := ((hv _ haD.1).comp a (dD_hasDerivAt a)).const_mul 8
  convert! ((hA.add hB).add hC).add hD using 1
  unfold L
  ring

lemma familySlope_hasDerivAt (p q : ℝ → ℝ)
    (hp : ∀ t, 0 < t → HasDerivAt p (q t) t)
    {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun a => L a p) (familySecond a q) a := by
  obtain ⟨haA, haB, haC, haD⟩ := distance_domains ha
  have hA := ((hp _ haA.1).comp a (dA_hasDerivAt a)).const_mul (-16)
  have hB := ((hp _ haB.1).comp a (dB_hasDerivAt a)).const_mul 16
  have hC := ((hp _ haC.1).comp a (dC_hasDerivAt a)).const_mul (8*(2+√2))
  have hD := ((hp _ haD.1).comp a (dD_hasDerivAt a)).const_mul (8*(2-√2))
  convert! ((hA.sub hB).add hC).add hD using 1
  unfold familySecond
  ring

lemma familySecond_pos (q : ℝ → ℝ) (hq : ∀ t, 0 < t → 0 < q t)
    {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : 0 < familySecond a q := by
  obtain ⟨haA, haB, haC, haD⟩ := distance_domains ha
  have hA := hq _ haA.1
  have hB := hq _ haB.1
  have hC := hq _ haC.1
  have hD := hq _ haD.1
  unfold familySecond
  positivity

lemma family_g_deriv {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : deriv (G g) a = L a g1 :=
  (family_hasDerivAt g g1 (fun _ ht => g_hasDerivAt ht) ha).deriv
lemma family_h_deriv {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : deriv (G h) a = L a h1 :=
  (family_hasDerivAt h h1 (fun _ ht => h_hasDerivAt ht) ha).deriv
lemma family_f_deriv {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) : deriv (G f) a = L a f1 :=
  (family_hasDerivAt f f1 (fun _ ht => f_hasDerivAt ht) ha).deriv

lemma lambda_eq : lambda = -(L aStar g1) / L aStar h1 := by
  unfold lambda
  rw [family_g_deriv aStar_mem, family_h_deriv aStar_mem]

end SquareAntiprismCounterexample
