import AllS.Units.N_F.N_compatibility

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

abbrev RetainedIndex (D : ℕ) := {t : Tag // t ∈ RetainedTags D}

theorem mem_RetainedTags {D : ℕ} {t : Tag} :
    t∈RetainedTags D ↔ tagWeight t≤D ∧ t≠(0,0,0) ∧ t≠(2,0,0) := by
  simp only [RetainedTags,Finset.mem_erase,mem_InvariantTags]
  tauto

def retainedInclusion (D : ℕ) (t : RetainedIndex D) : TagIndex D :=
  ⟨t.val,mem_InvariantTags.mpr (mem_RetainedTags.mp t.property).1⟩

def extendRetained (D : ℕ) : (RetainedIndex D → ℝ) →ₗ[ℝ] (TagIndex D → ℝ) where
  toFun x t := if h : t.val∈RetainedTags D then x ⟨t.val,h⟩ else 0
  map_add' x y := by
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext t
    simp only [Pi.smul_apply]
    split_ifs <;> simp

def retainedSynthesis (D : ℕ) : (RetainedIndex D → ℝ) →ₗ[ℝ] Poly3 :=
  (invariantSynthesis D).comp (extendRetained D)

def recoverySigmaCoefficient (a : ℝ) (D : ℕ) (x : RetainedIndex D → ℝ) : ℝ :=
  -ell1 a (retainedSynthesis D x)/(128*(3*a-1))

def recoveryConstantCoefficient (a : ℝ) (D : ℕ) (x : RetainedIndex D → ℝ) : ℝ :=
  -(ell0 a (retainedSynthesis D x)+(192*a^2-128*a+56)*recoverySigmaCoefficient a D x)/56

def recoveredPolynomial (a : ℝ) (D : ℕ) (x : RetainedIndex D → ℝ) : Poly3 :=
  retainedSynthesis D x+recoverySigmaCoefficient a D x • sigma^2+
    recoveryConstantCoefficient a D x • (1 : Poly3)

def zeroTag (D : ℕ) : TagIndex D := ⟨(0,0,0),mem_InvariantTags.mpr (by simp [tagWeight])⟩
def squareTag (D : ℕ) (hD : 2≤D) : TagIndex D :=
  ⟨(2,0,0),mem_InvariantTags.mpr (by simpa [tagWeight] using hD)⟩

theorem invariantSynthesis_single (D : ℕ) (t : TagIndex D) (c : ℝ) :
    invariantSynthesis D (Pi.single t c)=c • invariantMonomial t.val := by
  classical
  rw [invariantSynthesis_eq]
  simp [Pi.single_apply]

@[simp] theorem invariantMonomial_zero : invariantMonomial (0,0,0)=1 := by
  simp [invariantMonomial]
@[simp] theorem invariantMonomial_square : invariantMonomial (2,0,0)=sigma^2 := by
  simp [invariantMonomial]

def recoveredCoordinates (a : ℝ) (D : ℕ) (hD : 2≤D) (x : RetainedIndex D → ℝ) : TagIndex D → ℝ :=
  extendRetained D x+Pi.single (squareTag D hD) (recoverySigmaCoefficient a D x)+
    Pi.single (zeroTag D) (recoveryConstantCoefficient a D x)

theorem invariantSynthesis_recoveredCoordinates (a : ℝ) (D : ℕ) (hD : 2≤D)
    (x : RetainedIndex D → ℝ) :
    invariantSynthesis D (recoveredCoordinates a D hD x)=recoveredPolynomial a D x := by
  simp only [recoveredCoordinates,map_add,invariantSynthesis_single,squareTag,zeroTag,
    invariantMonomial_square,invariantMonomial_zero,recoveredPolynomial]
  rfl

theorem recoveredPolynomial_bounded (a : ℝ) (D : ℕ) (hD : 2≤D)
    (x : RetainedIndex D → ℝ) : recoveredPolynomial a D x∈boundedSymmetric D := by
  rw [← invariantSynthesis_recoveredCoordinates a D hD x]
  exact invariantSynthesis_mem D _

theorem recoveredPolynomial_ell (a : ℝ) (ha : physical a) (D : ℕ) (x : RetainedIndex D → ℝ) :
    ell0 a (recoveredPolynomial a D x)=0 ∧ ell1 a (recoveredPolynomial a D x)=0 := by
  rcases compatibility_low_values a ha with ⟨h01,h11,h02,h12,hn,_⟩
  have hden : 128*(3*a-1)≠0 := by nlinarith [ha.2]
  simp only [recoveredPolynomial,map_add,map_smul,smul_eq_mul,h01,h11,h02,h12,
    mul_zero,add_zero,recoveryConstantCoefficient,recoverySigmaCoefficient]
  constructor <;> field_simp [show 3*a-1≠0 by nlinarith [ha.2]] <;> ring

theorem quotient_recover (a : ℝ) (ha : physical a) (D : ℕ) (hD : 2≤D)
    (x : RetainedIndex D → ℝ) : recoveredPolynomial a D x∈Compatible a D := by
  rw [mem_Compatible]
  have h := (mem_boundedSymmetric D _).mp (recoveredPolynomial_bounded a D hD x)
  have he := recoveredPolynomial_ell a ha D x
  simp only [ell0,ell1,LinearMap.smul_apply,smul_eq_mul] at he
  exact ⟨h.1,h.2,by linarith [he.1],by linarith [he.2]⟩

#check quotient_recover
#print axioms quotient_recover
end Blueprint.Thomson.Finite
