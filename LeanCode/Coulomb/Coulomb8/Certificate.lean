import Coulomb8.Polynomial

namespace Coulomb8

abbrev KMatrix := List (List K)

structure Block where
  n : ℕ
  moment : Bool
  k : ℕ
  basis : KMatrix
  polys : List Poly
  weighted : Bool
  offset : ℕ

namespace Block

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


def upperColumn (b : Block) (i j : ℕ) : Poly :=
  Poly.scale (K.ofRat (if i=j then 1 else 2)) (b.column i j)

def coordinate (b : Block) (i j : ℕ) : ℕ :=
  let i' := min i j
  let j' := max i j
  b.offset+i'*b.n-i'*(i'+1)/2+j'

end Block
end Coulomb8
