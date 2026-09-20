import Thomson8.Polynomial

namespace Thomson8

abbrev Affine := List K
abbrev KMatrix := List (List K)

structure Block where
  n : ℕ
  moment : Bool
  k : ℕ
  basis : KMatrix
  polys : List Poly
  weighted : Bool
  upper : List Affine
  preconditioner : List (List ℚ)

namespace Block

def entry (b : Block) (i j ell : ℕ) : K :=
  let i' := min i j
  let j' := max i j
  ((b.upper.getD (i'*b.n - i'*(i'+1)/2 + j') []).getD ell K.zero)

def tangentBase : Poly :=
  Poly.add (Poly.monomial ⟨0,0,1⟩) (Poly.scale (K.ofRat (-1)) (Poly.monomial ⟨1,1,0⟩))

def tangentFactor : Poly :=
  Poly.mul (Poly.add (Poly.const K.one) (Poly.scale (K.ofRat (-1)) (Poly.monomial ⟨2,0,0⟩)))
    (Poly.add (Poly.const K.one) (Poly.scale (K.ofRat (-1)) (Poly.monomial ⟨0,2,0⟩)))

def Q : ℕ → Poly
  | 0 => Poly.const K.one
  | 1 => tangentBase
  | k+2 => Poly.add (Poly.scale (K.ofRat 2) (Poly.mul tangentBase (Q (k+1))))
      (Poly.scale (K.ofRat (-1)) (Poly.mul tangentFactor (Q k)))

def S (k i j : ℕ) : Poly := Poly.symmetrize (Poly.shift ⟨i,j,0⟩ K.one (Q k))

def R (k i j : ℕ) : Poly :=
  let s := S k i j
  Poly.sum [Poly.scale (K.ofRat 6) s, Poly.repeated 0 s,
    Poly.repeated 1 s, Poly.repeated 2 s,
    Poly.const (K.ofRat (if k=0 then 1/7 else 0))]

def basisEntry (b : Block) (i j : ℕ) : K := (b.basis.getD i []).getD j K.zero

def column (b : Block) (i j : ℕ) : Poly :=
  if b.moment then
    Poly.sum ((List.range b.basis.length).flatMap fun a =>
      (List.range b.basis.length).map fun c =>
        Poly.scale (K.mul (b.basisEntry a i) (b.basisEntry c j)) (R b.k a c))
  else
    let g := if b.weighted then
      Poly.add (Poly.const K.one) (Poly.scale (K.ofRat (-1)) (Poly.monomial ⟨2,0,0⟩))
      else Poly.const K.one
    Poly.symmetrize (Poly.mul g (Poly.mul (b.polys.getD i []) (b.polys.getD j [])))

def component (b : Block) (ell : ℕ) : Poly :=
  Poly.sum ((List.range b.n).flatMap fun i => (List.range b.n).map fun j =>
    Poly.scale (b.entry i j ell) (b.column i j))

end Block

def nodeA : K := ⟨-13/7,0,2/7,0⟩
def nodeB : K := ⟨-33/7,0,4/7,0⟩
def nodeC : K := ⟨13/7,10/7,-2/7,-1/7⟩
def nodeD : K := ⟨13/7,-10/7,-2/7,1/7⟩
def nodes : List K := [nodeA,nodeB,nodeC,nodeD]

def hermiteComponent (h : List Affine) (ell : ℕ) : Poly :=
  h.zipIdx |>.map fun (c,j) => (⟨j,0,0⟩,c.getD ell K.zero)

def targetComponent (h : List Affine) (ell : ℕ) : Poly :=
  Poly.add (Poly.symmetrize (hermiteComponent h ell))
    (Poly.const (K.ofRat (([0,4,12,8,8] : List ℚ).getD ell 0 / 56)))

def rhsComponent (blocks : List Block) (ell : ℕ) : Poly :=
  Poly.sum (blocks.map fun b => b.component ell)

def checkComponent (h : List Affine) (blocks : List Block) (ell : ℕ) : Prop :=
  (Poly.add (targetComponent h ell)
    (Poly.scale (K.ofRat (-1)) (rhsComponent blocks ell))).isZero

theorem component_sound (h : List Affine) (blocks : List Block) (ell : ℕ)
    (hc : checkComponent h blocks ell) (u v t : ℝ) :
    (targetComponent h ell).eval u v t = (rhsComponent blocks ell).eval u v t :=
  Poly.eval_eq_of_check _ _ hc u v t

end Thomson8
