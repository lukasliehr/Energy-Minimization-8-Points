import ThomsonNegative.Certificate.Correction.RowKernel
import ThomsonNegative.Certificate.Correction.RatioSound
import ThomsonNegative.Certificate.Correction.CenterSound
import ThomsonNegative.Certificate.StoredSound
import ThomsonNegative.Certificate.MetricSound
import ThomsonNegative.Certificate.ResidualBound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Structure.Exact (recCoeffs)
local notation "seval" => ThomsonNegative.Structure.Packed.evalZ

lemma context_good : Good 0 384 640 1408 := by
  constructor
  · omega
  · omega
  · omega
  · exact Nat.one_le_two_pow

/-- The exact coefficient centers of the verified residual checkpoints. -/
def residualCenters (residual : ℕ → TM) (k : Fin 11) (j : Fin 68) : ℝ :=
  (((decode sourceContext (residual j).v).getD k 0:ℤ):ℝ)/2^384

/-- A row of the exact rational correction operator, with its shared denominator. -/
def rowMap (numerator : ℕ → ℕ) (denominator : ℕ) (a : ℝ) :
    (Fin 68 → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j : Fin 68, (seval (recCoeffs (numerator j)) a/seval (recCoeffs denominator) a) •
    (LinearMap.proj j : (Fin 68 → ℝ) →ₗ[ℝ] ℝ)

lemma rowMap_apply (numerator : ℕ → ℕ) (denominator : ℕ) (a : ℝ) (x : Fin 68 → ℝ) :
    rowMap numerator denominator a x=
      ∑ j : Fin 68,(seval (recCoeffs (numerator j)) a/seval (recCoeffs denominator) a)*x j := by
  simp only [rowMap,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul]

lemma rowMap_unit (numerator : ℕ → ℕ) (denominator : ℕ) (a : ℝ) (j : Fin 68) :
    rowMap numerator denominator a (unitVector 68 j)=
      seval (recCoeffs (numerator j)) a/seval (recCoeffs denominator) a := by
  classical
  rw [rowMap_apply]
  simp [unitVector,Pi.single_apply]

structure RowCertified (A : TM) (residual : ℕ → TM) (r : RowWitness) : Prop where
  normalizer_pos : 0<r.normalizer
  inverse_checked : sameTM (denominatorInverse context A r.denominator r.normalizer) r.inverse=true
  columns_checked : allBelow 68 (fun j =>
    let M := ratioTM context A r.inverse (r.numerator j) r.normalizer 1
    M.ok && Nat.beq (rangeX context M) (r.columns j))=true
  centers_checked : allBelow 11 (fun k => sameTM
    (ratioTM context A r.inverse (r.centers k) r.normalizer (Nat.pow 2 384)) (r.models k))=true
  contraction_checked : ∀ k : Fin 11,
    (centerEquation r.numerator residual (r.centers k) r.radix r.length r.width k).check=true

theorem RowCertified.inverse_encl {A : TM} {residual : ℕ → TM} {r : RowWitness}
    (h : RowCertified A residual r) {a : ℝ → ℝ} (ha : Encl context A a) :
    Encl context r.inverse
      (fun t => (seval (recCoeffs r.denominator) (a t)/(r.normalizer:ℝ))⁻¹) := by
  have hok : (denominatorInverse context A r.denominator r.normalizer).ok=true := by
    have hh := h.inverse_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hi := denominatorInverse_sound context_good ha r.denominator r.normalizer hok
  change Encl context (denominatorInverse context A r.denominator r.normalizer) _ at hi
  rwa [sameTM_eq h.inverse_checked] at hi

theorem RowCertified.column_bound {A : TM} {residual : ℕ → TM} {r : RowWitness}
    (h : RowCertified A residual r) {a : ℝ → ℝ} (ha : Encl context A a)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) (j : Fin 68) :
    |rowMap r.numerator r.denominator (a t) (unitVector 68 j)|≤(r.columns j:ℝ)/2^384 := by
  have hc := allBelow_sound _ _ h.columns_checked j j.isLt
  simp only [Bool.and_eq_true,Nat.beq_eq] at hc
  have hn := ratioTM_sound context_good ha (r.numerator j) r.denominator r.normalizer 1
    (Nat.ne_of_gt h.normalizer_pos) (h.inverse_encl ha) hc.1
  have hb := rangeX_sound context_good hn t ht
  rw [rowMap_unit]
  simp only [context] at hc
  simpa only [Nat.cast_one,div_one,hc.2] using hb

theorem RowCertified.center_encl {A : TM} {residual : ℕ → TM} {r : RowWitness}
    (h : RowCertified A residual r) {a : ℝ → ℝ} (ha : Encl context A a) (k : Fin 11) :
    Encl context (r.models k)
      (fun t => rowMap r.numerator r.denominator (a t) (residualCenters residual k)) := by
  have he := sameTM_eq (allBelow_sound _ _ h.centers_checked k k.isLt)
  have hok : (ratioTM context A r.inverse (r.centers k) r.normalizer (Nat.pow 2 384)).ok=true := by
    have hh := allBelow_sound _ _ h.centers_checked k k.isLt
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hh := ratioTM_sound context_good ha (r.centers k) r.denominator r.normalizer
    (Nat.pow 2 384) (Nat.ne_of_gt h.normalizer_pos) (h.inverse_encl ha) hok
  change Encl context (ratioTM context A r.inverse (r.centers k) r.normalizer (Nat.pow 2 384)) _ at hh
  rw [he] at hh
  apply hh.congr
  intro t ht
  have hc := centerEquation_sound r.numerator residual (r.centers k)
    r.radix r.length r.width k k.isLt (h.contraction_checked k) (a t)
  simp only [Nat.pow_eq,Nat.cast_pow,Nat.cast_ofNat]
  rw [hc,rowMap_apply,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [residualCenters]
  ring

#print axioms RowCertified.center_encl
#print axioms RowCertified.column_bound
end ThomsonNegative.Certificate.Correction
