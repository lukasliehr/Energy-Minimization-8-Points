import ThomsonNegative.Certificate.CoefficientKernel
import ThomsonNegative.Certificate.GramSound

/-! Soundness of the common coefficient contraction, before its geometric bridge. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
open Bridges

theorem list_all_getD {α : Type*} (p : α → Bool) (xs : List α) (default : α)
    (hd : p default=true) (h : xs.all p=true) (i : ℕ) : p (xs.getD i default)=true := by
  induction xs generalizing i with
  | nil => simpa using hd
  | cons x xs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using ih h.2 i

theorem allOk_entry {A : TMMatrix} (h : allOk A=true) (i j : ℕ) : (entry A i j).ok=true := by
  have hi := list_all_getD (fun row : List TM => row.all TM.ok) A [] rfl h i
  exact list_all_getD TM.ok (A.getD i []) zeroTM rfl hi j

theorem shiftedHeight_sound {N S B W : ℕ} (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (hok : (shiftedHeight (mkCtx N S B W) A).ok=true) :
    Encl (mkCtx N S B W) (shiftedHeight (mkCtx N S B W) A) (fun t => a t-83/256) := by
  have h := refresh_sound hg (addC_sound ha true (ratMag (mkCtx N S B W) 83 256) 1
    (qval (true,83,256)) (ratMag_err (true,83,256)) hok hg)
  exact h.congr (fun t _ => by simp [qval]; ring)

theorem getD_map {α β : Type*} (f : α → β) (L : List α) (d : α) (e : β)
    (i : ℕ) (hi : i<L.length) : (L.map f).getD i e=f (L.getD i d) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

theorem basisModels_sound {N S B W : ℕ} (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (hok : basisGate (mkCtx N S B W) A=true)
    (i : ℕ) (hi : i<BasisData.records.length) :
    Encl (mkCtx N S B W) ((basisModels (mkCtx N S B W) A).getD i zeroTM)
      (fun t => (BasisData.record i).eval (a t-83/256)) := by
  have hh : (shiftedHeight (mkCtx N S B W) A).ok=true ∧
      (basisModels (mkCtx N S B W) A).all TM.ok=true := by
    simpa only [basisGate,Bool.and_eq_true] using hok
  have he : (basisModels (mkCtx N S B W) A).getD i zeroTM =
      rationalFunctionTM (mkCtx N S B W) 9 1 (shiftedHeight (mkCtx N S B W) A) (BasisData.record i) :=
    getD_map _ _ BasisData.rf0 zeroTM i hi
  rw [he]
  exact rationalFunctionTM_sound hg (shiftedHeight_sound hg ha hh.1) 9 1 _
    (by rw [← he]; exact list_all_getD TM.ok _ zeroTM rfl hh.2 i)

theorem rationalScale_sound {N S B W : ℕ} (hg : Good N S B W) {A : TM} {a : ℝ → ℝ}
    (ha : Encl (mkCtx N S B W) A a) (ng : Bool) (n d : ℕ)
    (hok : (rationalScale (mkCtx N S B W) ng n d A).ok=true) :
    Encl (mkCtx N S B W) (rationalScale (mkCtx N S B W) ng n d A)
      (fun t => qval (ng,n,d) * a t) :=
  smul_sound hg ha ng _ 1 _ (ratMag_err (ng,n,d)) hok

def rawCoefficient (b row i j : ℕ) : ℝ :=
  ((RawData.coefficient b row i j : ℤ):ℝ) / RawData.denominator b

theorem rawTermTM_sound {N S B W : ℕ} (hg : Good N S B W) (b row i j : ℕ)
    (G : TMMatrix) (g : ℝ → ℝ)
    (hG : Encl (mkCtx N S B W) (entry G i j) g)
    (hok : (rawTermTM (mkCtx N S B W) b row i j G).ok=true) :
    Encl (mkCtx N S B W) (rawTermTM (mkCtx N S B W) b row i j G)
      (fun t => rawCoefficient b row i j * g t) := by
  let p := RawData.positiveSlot b row i j
  let n := RawData.negativeSlot b row i j
  have he : rawCoefficient b row i j = ((p:ℝ)-n)/RawData.denominator b := by
    simp [rawCoefficient,RawData.coefficient,p,n]
  by_cases hp : p=n
  · have hz : rawTermTM (mkCtx N S B W) b row i j G=zeroTM := by
      simp only [rawTermTM,Bool.cond_eq_ite,Nat.beq_eq]
      exact if_pos hp
    rw [hz]
    exact zero_sound.congr (fun t _ => by rw [he,hp]; simp)
  · have hz : rawTermTM (mkCtx N S B W) b row i j G =
        rationalScale (mkCtx N S B W) (Nat.blt p n) (Nat.add (Nat.sub p n) (Nat.sub n p))
          (RawData.denominator b) (entry G i j) := by
      simp only [rawTermTM,Bool.cond_eq_ite,Nat.beq_eq]
      exact if_neg hp
    rw [hz] at hok ⊢
    have h := rationalScale_sound hg hG _ _ _ hok
    apply h.congr
    intro t ht
    have hv := differenceArg_val (p,n) (RawData.denominator b)
    change qval (differenceArg (p,n) (RawData.denominator b)) * g t = _
    rw [hv,he]
    rfl

theorem rawRowTM_sound {N S B W : ℕ} (hg : Good N S B W) (b row : ℕ)
    (G : TMMatrix) (g : ℕ → ℕ → ℝ → ℝ)
    (hG : ∀ i<RawData.size b, ∀ j<RawData.size b,
      Encl (mkCtx N S B W) (entry G i j) (g i j))
    (hok : (rawRowTM (mkCtx N S B W) b row G).ok=true) :
    Encl (mkCtx N S B W) (rawRowTM (mkCtx N S B W) b row G)
      (fun t => ∑ i ∈ Finset.range (RawData.size b),
        ∑ j ∈ Finset.range (RawData.size b), rawCoefficient b row i j * g i j t) := by
  apply refresh_sound hg
  apply sumTM_sound hg _ _ (RawData.size b) _ hok
  intro i hi
  have hrow := sumTM_ok _ _ (RawData.size b) hok i hi
  apply sumTM_sound hg _ _ (RawData.size b) _ hrow
  intro j hj
  exact rawTermTM_sound hg b row i j G _ (hG i hi j hj)
    (sumTM_ok _ _ (RawData.size b) hrow j hj)

#print axioms basisModels_sound
#print axioms rawRowTM_sound
end ThomsonNegative.Certificate
