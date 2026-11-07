import ThomsonNegative.Certificate.Bridges.PowerSums
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 1000000
def powerTable00 : Poly3 := MvPolynomial.C (3:ℝ)*coordinateMonomial (0,0,0)
theorem powerTable00_eq : powerTable00=coordinatePowerSum 0 := by
  rw [coordinatePowerSum]
  apply MvPolynomial.funext
  intro x
  simp [powerTable00,coordinateMonomial] <;> ring
def powerTable01 : Poly3 := MvPolynomial.C (1:ℝ)*coordinateMonomial (1,0,0)
theorem powerTable01_eq : powerTable01=coordinatePowerSum 1 := by
  rw [coordinatePowerSum]
  apply MvPolynomial.funext
  intro x
  simp [powerTable01,coordinateMonomial] <;> ring
def powerTable02 : Poly3 := MvPolynomial.C (-2:ℝ)*coordinateMonomial (0,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (2,0,0)
theorem powerTable02_eq : powerTable02=coordinatePowerSum 2 := by
  rw [coordinatePowerSum]
  apply MvPolynomial.funext
  intro x
  simp [powerTable02,coordinateMonomial] <;> ring
def powerTable03 : Poly3 := MvPolynomial.C (3:ℝ)*coordinateMonomial (0,0,1) + MvPolynomial.C (-3:ℝ)*coordinateMonomial (1,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (3,0,0)
theorem powerTable03_eq : powerTable03=coordinatePowerSum 3 := by
  rw [coordinatePowerSum]
  rw [← powerTable02_eq, ← powerTable01_eq, ← powerTable00_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable03,powerTable02,powerTable01,powerTable00,coordinateMonomial] <;> ring
def powerTable04 : Poly3 := MvPolynomial.C (2:ℝ)*coordinateMonomial (0,2,0) + MvPolynomial.C (4:ℝ)*coordinateMonomial (1,0,1) + MvPolynomial.C (-4:ℝ)*coordinateMonomial (2,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (4,0,0)
theorem powerTable04_eq : powerTable04=coordinatePowerSum 4 := by
  rw [coordinatePowerSum]
  rw [← powerTable03_eq, ← powerTable02_eq, ← powerTable01_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable04,powerTable03,powerTable02,powerTable01,coordinateMonomial] <;> ring
def powerTable05 : Poly3 := MvPolynomial.C (-5:ℝ)*coordinateMonomial (0,1,1) + MvPolynomial.C (5:ℝ)*coordinateMonomial (1,2,0) + MvPolynomial.C (5:ℝ)*coordinateMonomial (2,0,1) + MvPolynomial.C (-5:ℝ)*coordinateMonomial (3,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (5,0,0)
theorem powerTable05_eq : powerTable05=coordinatePowerSum 5 := by
  rw [coordinatePowerSum]
  rw [← powerTable04_eq, ← powerTable03_eq, ← powerTable02_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable05,powerTable04,powerTable03,powerTable02,coordinateMonomial] <;> ring
def powerTable06 : Poly3 := MvPolynomial.C (3:ℝ)*coordinateMonomial (0,0,2) + MvPolynomial.C (-2:ℝ)*coordinateMonomial (0,3,0) + MvPolynomial.C (-12:ℝ)*coordinateMonomial (1,1,1) + MvPolynomial.C (9:ℝ)*coordinateMonomial (2,2,0) + MvPolynomial.C (6:ℝ)*coordinateMonomial (3,0,1) + MvPolynomial.C (-6:ℝ)*coordinateMonomial (4,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (6,0,0)
theorem powerTable06_eq : powerTable06=coordinatePowerSum 6 := by
  rw [coordinatePowerSum]
  rw [← powerTable05_eq, ← powerTable04_eq, ← powerTable03_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable06,powerTable05,powerTable04,powerTable03,coordinateMonomial] <;> ring
def powerTable07 : Poly3 := MvPolynomial.C (7:ℝ)*coordinateMonomial (0,2,1) + MvPolynomial.C (7:ℝ)*coordinateMonomial (1,0,2) + MvPolynomial.C (-7:ℝ)*coordinateMonomial (1,3,0) + MvPolynomial.C (-21:ℝ)*coordinateMonomial (2,1,1) + MvPolynomial.C (14:ℝ)*coordinateMonomial (3,2,0) + MvPolynomial.C (7:ℝ)*coordinateMonomial (4,0,1) + MvPolynomial.C (-7:ℝ)*coordinateMonomial (5,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (7,0,0)
theorem powerTable07_eq : powerTable07=coordinatePowerSum 7 := by
  rw [coordinatePowerSum]
  rw [← powerTable06_eq, ← powerTable05_eq, ← powerTable04_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable07,powerTable06,powerTable05,powerTable04,coordinateMonomial] <;> ring
def powerTable08 : Poly3 := MvPolynomial.C (-8:ℝ)*coordinateMonomial (0,1,2) + MvPolynomial.C (2:ℝ)*coordinateMonomial (0,4,0) + MvPolynomial.C (24:ℝ)*coordinateMonomial (1,2,1) + MvPolynomial.C (12:ℝ)*coordinateMonomial (2,0,2) + MvPolynomial.C (-16:ℝ)*coordinateMonomial (2,3,0) + MvPolynomial.C (-32:ℝ)*coordinateMonomial (3,1,1) + MvPolynomial.C (20:ℝ)*coordinateMonomial (4,2,0) + MvPolynomial.C (8:ℝ)*coordinateMonomial (5,0,1) + MvPolynomial.C (-8:ℝ)*coordinateMonomial (6,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (8,0,0)
theorem powerTable08_eq : powerTable08=coordinatePowerSum 8 := by
  rw [coordinatePowerSum]
  rw [← powerTable07_eq, ← powerTable06_eq, ← powerTable05_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable08,powerTable07,powerTable06,powerTable05,coordinateMonomial] <;> ring
def powerTable09 : Poly3 := MvPolynomial.C (3:ℝ)*coordinateMonomial (0,0,3) + MvPolynomial.C (-9:ℝ)*coordinateMonomial (0,3,1) + MvPolynomial.C (-27:ℝ)*coordinateMonomial (1,1,2) + MvPolynomial.C (9:ℝ)*coordinateMonomial (1,4,0) + MvPolynomial.C (54:ℝ)*coordinateMonomial (2,2,1) + MvPolynomial.C (18:ℝ)*coordinateMonomial (3,0,2) + MvPolynomial.C (-30:ℝ)*coordinateMonomial (3,3,0) + MvPolynomial.C (-45:ℝ)*coordinateMonomial (4,1,1) + MvPolynomial.C (27:ℝ)*coordinateMonomial (5,2,0) + MvPolynomial.C (9:ℝ)*coordinateMonomial (6,0,1) + MvPolynomial.C (-9:ℝ)*coordinateMonomial (7,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (9,0,0)
theorem powerTable09_eq : powerTable09=coordinatePowerSum 9 := by
  rw [coordinatePowerSum]
  rw [← powerTable08_eq, ← powerTable07_eq, ← powerTable06_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable09,powerTable08,powerTable07,powerTable06,coordinateMonomial] <;> ring
def powerTable10 : Poly3 := MvPolynomial.C (15:ℝ)*coordinateMonomial (0,2,2) + MvPolynomial.C (-2:ℝ)*coordinateMonomial (0,5,0) + MvPolynomial.C (10:ℝ)*coordinateMonomial (1,0,3) + MvPolynomial.C (-40:ℝ)*coordinateMonomial (1,3,1) + MvPolynomial.C (-60:ℝ)*coordinateMonomial (2,1,2) + MvPolynomial.C (25:ℝ)*coordinateMonomial (2,4,0) + MvPolynomial.C (100:ℝ)*coordinateMonomial (3,2,1) + MvPolynomial.C (25:ℝ)*coordinateMonomial (4,0,2) + MvPolynomial.C (-50:ℝ)*coordinateMonomial (4,3,0) + MvPolynomial.C (-60:ℝ)*coordinateMonomial (5,1,1) + MvPolynomial.C (35:ℝ)*coordinateMonomial (6,2,0) + MvPolynomial.C (10:ℝ)*coordinateMonomial (7,0,1) + MvPolynomial.C (-10:ℝ)*coordinateMonomial (8,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (10,0,0)
theorem powerTable10_eq : powerTable10=coordinatePowerSum 10 := by
  rw [coordinatePowerSum]
  rw [← powerTable09_eq, ← powerTable08_eq, ← powerTable07_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable10,powerTable09,powerTable08,powerTable07,coordinateMonomial] <;> ring
def powerTable11 : Poly3 := MvPolynomial.C (-11:ℝ)*coordinateMonomial (0,1,3) + MvPolynomial.C (11:ℝ)*coordinateMonomial (0,4,1) + MvPolynomial.C (66:ℝ)*coordinateMonomial (1,2,2) + MvPolynomial.C (-11:ℝ)*coordinateMonomial (1,5,0) + MvPolynomial.C (22:ℝ)*coordinateMonomial (2,0,3) + MvPolynomial.C (-110:ℝ)*coordinateMonomial (2,3,1) + MvPolynomial.C (-110:ℝ)*coordinateMonomial (3,1,2) + MvPolynomial.C (55:ℝ)*coordinateMonomial (3,4,0) + MvPolynomial.C (165:ℝ)*coordinateMonomial (4,2,1) + MvPolynomial.C (33:ℝ)*coordinateMonomial (5,0,2) + MvPolynomial.C (-77:ℝ)*coordinateMonomial (5,3,0) + MvPolynomial.C (-77:ℝ)*coordinateMonomial (6,1,1) + MvPolynomial.C (44:ℝ)*coordinateMonomial (7,2,0) + MvPolynomial.C (11:ℝ)*coordinateMonomial (8,0,1) + MvPolynomial.C (-11:ℝ)*coordinateMonomial (9,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (11,0,0)
theorem powerTable11_eq : powerTable11=coordinatePowerSum 11 := by
  rw [coordinatePowerSum]
  rw [← powerTable10_eq, ← powerTable09_eq, ← powerTable08_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable11,powerTable10,powerTable09,powerTable08,coordinateMonomial] <;> ring
def powerTable12 : Poly3 := MvPolynomial.C (3:ℝ)*coordinateMonomial (0,0,4) + MvPolynomial.C (-24:ℝ)*coordinateMonomial (0,3,2) + MvPolynomial.C (2:ℝ)*coordinateMonomial (0,6,0) + MvPolynomial.C (-48:ℝ)*coordinateMonomial (1,1,3) + MvPolynomial.C (60:ℝ)*coordinateMonomial (1,4,1) + MvPolynomial.C (180:ℝ)*coordinateMonomial (2,2,2) + MvPolynomial.C (-36:ℝ)*coordinateMonomial (2,5,0) + MvPolynomial.C (40:ℝ)*coordinateMonomial (3,0,3) + MvPolynomial.C (-240:ℝ)*coordinateMonomial (3,3,1) + MvPolynomial.C (-180:ℝ)*coordinateMonomial (4,1,2) + MvPolynomial.C (105:ℝ)*coordinateMonomial (4,4,0) + MvPolynomial.C (252:ℝ)*coordinateMonomial (5,2,1) + MvPolynomial.C (42:ℝ)*coordinateMonomial (6,0,2) + MvPolynomial.C (-112:ℝ)*coordinateMonomial (6,3,0) + MvPolynomial.C (-96:ℝ)*coordinateMonomial (7,1,1) + MvPolynomial.C (54:ℝ)*coordinateMonomial (8,2,0) + MvPolynomial.C (12:ℝ)*coordinateMonomial (9,0,1) + MvPolynomial.C (-12:ℝ)*coordinateMonomial (10,1,0) + MvPolynomial.C (1:ℝ)*coordinateMonomial (12,0,0)
theorem powerTable12_eq : powerTable12=coordinatePowerSum 12 := by
  rw [coordinatePowerSum]
  rw [← powerTable11_eq, ← powerTable10_eq, ← powerTable09_eq]
  apply MvPolynomial.funext
  intro x
  simp [powerTable12,powerTable11,powerTable10,powerTable09,coordinateMonomial] <;> ring
#print axioms powerTable12_eq
end ThomsonNegative.Certificate.Bridges
