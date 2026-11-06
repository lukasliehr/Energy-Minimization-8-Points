import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin

/-!
# TailC.Centered: integer mirror of the centered contact Gram (kernel side; workstream TC1)

`AZ = ℤ√2 × ℤ√2`, `(u, v) ↦ u + v H` with `H = packingZHeight`, `H² = a = (2√2 - 1)/7`; `mul7 x y` is `7 x y`.
Every real quantity of `centeredContactRawGram (meanTangentRaw j) (meanTangentRaw k)` has an integer mirror at a fixed
scale (`fZ`: 28 · `contactMComponents`, `gZ`: 56 · `contactMBilinear` with the rotations `0, 1`, `bZ`: 56 · the
`packingRadius`-free factor of the third rotation, `hZ`: 7 · `meanHEntry`, `qEZ`: 5488 · `centeredQEntry`).
`gramZ j k = 17210368 · Gram(j, k)` (`Centered.Sound`); the leaves check `gramZ j k = 3136 • qEZ j k`.
-/

namespace ThomsonCompact.TailC.Centered

abbrev AZ := ℤ√2 × ℤ√2

/-- `7 · x · y` in `ℤ√2[H]/(7H² - (2√2 - 1))`. -/
def mul7 (x y : AZ) : AZ :=
  (7 * (x.1 * y.1) + ⟨-1, 2⟩ * (x.2 * y.2), 7 * (x.1 * y.2 + x.2 * y.1))

/-- Scalar multiplication by `ℤ√2`. -/
def zs (z : ℤ√2) (x : AZ) : AZ := (z * x.1, z * x.2)

/-- The generator `H`. -/
def hZ1 : AZ := (0, 1)

/-! ## Primitive tables (scaled) -/

/-- `2 angularCos`, `2 angularSin`. -/
def acZ : Fin 8 → ℤ√2 := ![⟨2, 0⟩, ⟨0, 1⟩, 0, ⟨0, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩, 0, ⟨0, 1⟩]
def asZ : Fin 8 → ℤ√2 := ![0, ⟨0, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩, 0, ⟨0, -1⟩, ⟨-2, 0⟩, ⟨0, -1⟩]
/-- `layerSign`, `boundaryCos2`, `boundarySin2`. -/
def lsZ : Fin 8 → ℤ√2 := ![1, -1, 1, -1, 1, -1, 1, -1]
def c2Z : Fin 8 → ℤ√2 := ![1, 0, -1, 0, 1, 0, -1, 0]
def s2Z : Fin 8 → ℤ√2 := ![0, 1, 0, -1, 0, 1, 0, -1]

/-- `2 meanScalarRaw j i`. -/
def msrZ (j i : Fin 8) : ℤ√2 :=
  (![2, acZ i, asZ i, 2 * c2Z i, 2 * s2Z i, lsZ i * acZ i, -(lsZ i * asZ i), 2 * lsZ i] : Fin 8 → ℤ√2) j

/-- `2 (meanTangentRaw j) (i, b)`. -/
def qZ (j : Fin 8 × Fin 2) (i : Fin 8) (b : Fin 2) : ℤ√2 := if b = j.2 then msrZ j.1 i else 0

/-- `2 contactCosine`, `2 contactSine`, `contactParity`. -/
def ccZ (b : Fin 2) : ℤ√2 := if b = 0 then ⟨0, 1⟩ else 0
def csZ (b : Fin 2) : ℤ√2 := if b = 0 then ⟨0, 1⟩ else ⟨2, 0⟩
def cpZ (b : Fin 2) : ℤ√2 := if b = 0 then -1 else 1

/-- `7 packingHeight`. -/
def aZ : ℤ√2 := ⟨-1, 2⟩

/-- `14 (packingHeight · contactCosine + (1 - packingHeight) contactParity)`. -/
def dZ (b : Fin 2) : ℤ√2 := aZ * ccZ b + (14 - 2 * aZ) * cpZ b

/-- The other endpoint of a contact. -/
def cnext (e : Fin 8 × Fin 2) : Fin 8 := e.1 + if e.2 = 0 then 1 else 2

/-- Embedding `ℤ√2 → AZ`. -/
def em (z : ℤ√2) : AZ := (z, 0)

/-! ## Contact components and bilinear forms -/

/-- `28 contactMComponents e (meanTangentRaw j)`. -/
def fZ (e : Fin 8 × Fin 2) (j : Fin 8 × Fin 2) : Fin 4 → AZ :=
  ![em (2 * (aZ * qZ j e.1 0) - 7 * (ccZ e.2 * qZ j (cnext e) 0)) + zs (7 * (csZ e.2 * qZ j (cnext e) 1)) hZ1,
    em (2 * (aZ * qZ j e.1 1) - dZ e.2 * qZ j (cnext e) 1) - zs (7 * (csZ e.2 * qZ j (cnext e) 0)) hZ1,
    em (2 * (aZ * qZ j (cnext e) 0) - 7 * (ccZ e.2 * qZ j e.1 0)) - zs (7 * (csZ e.2 * qZ j e.1 1)) hZ1,
    em (2 * (aZ * qZ j (cnext e) 1) - dZ e.2 * qZ j e.1 1) + zs (7 * (csZ e.2 * qZ j e.1 0)) hZ1]

/-- Rotation coordinates `2 (boundaryRotation r) (i, b)` for `r = 0, 1` (`-H c3, -s3`; `H s3, -c3`). -/
def rotZ (r : Fin 2) (i : Fin 8) (b : Fin 2) : AZ :=
  if r = 0 then (if b = 0 then zs (-(lsZ i * acZ i)) hZ1 else em (lsZ i * asZ i))
  else (if b = 0 then zs (-(lsZ i * asZ i)) hZ1 else em (-(lsZ i * acZ i)))

/-- `392 contactFrameDot x v e` from the scaled coordinates `X = 2x`, `V = 2v` (both in `AZ`). -/
def fdZ (X V : Fin 8 → Fin 2 → AZ) (e : Fin 8 × Fin 2) : AZ :=
  zs (7 * ccZ e.2) (mul7 (X e.1 0) (V (cnext e) 0)) -
    zs (csZ e.2) (mul7 (mul7 hZ1 (X e.1 0)) (V (cnext e) 1)) +
    zs (csZ e.2) (mul7 (mul7 hZ1 (X e.1 1)) (V (cnext e) 0)) +
    zs (dZ e.2) (mul7 (X e.1 1) (V (cnext e) 1))

/-- `392 contactMBilinear e x v` from `X = 2x`, `V = 2v`. -/
def gZ7 (X V : Fin 8 → Fin 2 → AZ) (e : Fin 8 × Fin 2) : AZ :=
  zs (2 * aZ) (mul7 (X e.1 0) (V e.1 0) + mul7 (X e.1 1) (V e.1 1) +
      (mul7 (X (cnext e) 0) (V (cnext e) 0) + mul7 (X (cnext e) 1) (V (cnext e) 1))) -
    fdZ X V e - fdZ V X e

/-- `qZ` as an `AZ`-valued coordinate function. -/
def qA (j : Fin 8 × Fin 2) : Fin 8 → Fin 2 → AZ := fun i b => em (qZ j i b)

/-- `56 β` for the third rotation `(R, 0)`: `contactMBilinear e rot₂ q = R β`,
`β = a (q(e,0) + q(n,0)) - c q(n,0) + H s q(n,1) - c q(e,0) - H s q(e,1)`. -/
def bZ (e : Fin 8 × Fin 2) (j : Fin 8 × Fin 2) : AZ :=
  em (4 * (aZ * (qZ j e.1 0 + qZ j (cnext e) 0)) - 14 * (ccZ e.2 * qZ j (cnext e) 0) -
      14 * (ccZ e.2 * qZ j e.1 0)) +
    zs (14 * (csZ e.2 * qZ j (cnext e) 1) - 14 * (csZ e.2 * qZ j e.1 1)) hZ1

/-! ## Spectral data (scaled) -/

def mPartner : Fin 8 → Fin 8 := ![0, 2, 1, 4, 3, 6, 5, 7]
def mSinZ : Fin 8 → ℤ√2 := ![0, 1, -1, 1, -1, 1, -1, 0]
def mswZ (j : Fin 8) : ℤ√2 := if j = 0 ∨ j = 7 then 8 else 4
/-- `8 / meanScalarWeight`. -/
def mswN (j : Fin 8) : ℤ√2 := if j = 0 ∨ j = 7 then 1 else 2

/-- `7 meanPhiEigen`, `7 meanMeridianEigen`, `7 meanBetaFactor`. -/
def mPhiZ : Fin 8 → ℤ√2 := ![0, ⟨-7, 7⟩, ⟨-7, 7⟩, ⟨0, 7⟩, ⟨0, 7⟩, ⟨7, 7⟩, ⟨7, 7⟩, ⟨0, 14⟩]
def mMerZ : Fin 8 → ℤ√2 := ![0, ⟨-3, 13⟩, ⟨-3, 13⟩, ⟨12, 11⟩, ⟨12, 11⟩, ⟨3, 1⟩, ⟨3, 1⟩, ⟨-24, 6⟩]
def mBetaZ : Fin 8 → ℤ√2 := ![0, ⟨21, 7⟩, ⟨21, 7⟩, ⟨0, 7⟩, ⟨0, 7⟩, ⟨-7, -7⟩, ⟨-7, -7⟩, 0]

/-- `7 meanHEntry j k`. -/
def hZ (j k : Fin 8 × Fin 2) : AZ :=
  if j = k then em (mswZ j.1 * (if j.2 = 0 then mPhiZ j.1 else mMerZ j.1))
  else if j.1 = mPartner k.1 ∧ j.2 ≠ k.2 then
    zs (mswZ j.1 * mBetaZ j.1 * mSinZ j.1 * (if j.2 = 0 then 1 else -1)) hZ1
  else 0

/-- `5488 centeredPhiEigen`, `5488 centeredMeridianEigen`, `5488 centeredBetaFactor`. -/
def cPhiZ : Fin 8 → ℤ√2 := ![⟨3892, 2996⟩, ⟨9590, -1099⟩, ⟨9590, -1099⟩, ⟨9478, 1428⟩, ⟨9478, 1428⟩,
  ⟨7406, 3759⟩, ⟨7406, 3759⟩, ⟨12488, 700⟩]
def cMerZ : Fin 8 → ℤ√2 := ![⟨10976, 2744⟩, ⟨15714, 1689⟩, ⟨15714, 1689⟩, ⟨13690, 5240⟩, ⟨13690, 5240⟩,
  ⟨10282, 4027⟩, ⟨10282, 4027⟩, ⟨10884, -2224⟩]
def cBetaZ : Fin 8 → ℤ√2 := ![0, ⟨2702, 4249⟩, ⟨2702, 4249⟩, ⟨3318, -1246⟩, ⟨3318, -1246⟩,
  ⟨-3066, -1267⟩, ⟨-3066, -1267⟩, 0]

/-- `5488 centeredQEntry j k`. -/
def qEZ (j k : Fin 8 × Fin 2) : AZ :=
  if j = k then em (mswZ j.1 * (if j.2 = 0 then cPhiZ j.1 else cMerZ j.1))
  else if j.1 = mPartner k.1 ∧ j.2 ≠ k.2 then
    zs (mswZ j.1 * cBetaZ j.1 * mSinZ j.1 * (if j.2 = 0 then 1 else -1)) hZ1
  else 0

/-! ## The scaled Gram -/

/-- `2 contactWeight`. -/
def kwZ (e : Fin 8 × Fin 2) : ℤ√2 := if e.2 = 0 then 2 else ⟨2, 1⟩

/-- `8 / boundaryWeight 13 = 8 / boundaryWeight 14 = 3 - √2`; `56 / contactTotalWeight = 4 - √2`. -/
def wZ : ℤ√2 := ⟨3, -1⟩
def tZ : ℤ√2 := ⟨4, -1⟩

/-- `17210368 · centeredContactRawGram (meanTangentRaw j) (meanTangentRaw k)` (`17210368 = 2^10 7^5`). -/
def gramZ (j k : Fin 8 × Fin 2) : AZ :=
  (∑ e : Fin 8 × Fin 2, zs (kwZ e)
    (zs 1568 (∑ c : Fin 4, mul7 (fZ e j c) (fZ e k c)) -
      (zs wZ (mul7 (gZ7 (rotZ 0) (qA j) e) (gZ7 (rotZ 0) (qA k) e)) +
        zs wZ (mul7 (gZ7 (rotZ 1) (qA j) e) (gZ7 (rotZ 1) (qA k) e)) +
        zs 49 (mul7 (bZ e j) (bZ e k))))) -
    ∑ j' : Fin 8 × Fin 2, zs (112 * mswN j'.1 * tZ) (mul7 (hZ j j') (hZ k j'))

/-- Row check: `gramZ j k = 3136 qEZ j k` for all `k`. -/
def rowOk (j : Fin 8 × Fin 2) : Prop := ∀ k : Fin 8 × Fin 2, gramZ j k = zs 3136 (qEZ j k)

instance (j : Fin 8 × Fin 2) : Decidable (rowOk j) := by unfold rowOk; infer_instance

end ThomsonCompact.TailC.Centered
