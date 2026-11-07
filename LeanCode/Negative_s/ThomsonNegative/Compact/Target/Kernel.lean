import ThomsonNegative.Compact.Packed.Core2

/-! Init-only packed positive-series, cached-root, and H7 target constructor.
The bit-exact mirror is `analysis/formalization_compact/target_reference.py`.
-/
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed

structure Parameters where
  anchorTerms : Nat := 120
  heightTerms : Nat := 76
  reducedCTerms : Nat := 63
  reducedDTerms : Nat := 40
  newtonFuel : Nat := 6
  tolerance : Nat := 1

def defaultParameters : Parameters := {}

def radd (c : Ctx) (A B : TM) : TM := refresh c (add c A B)
def rmul (c : Ctx) (A B : TM) : TM := refresh c (mul c A B)
def rdiv (c : Ctx) (A : TM) (n : Nat) : TM :=
  refresh c (smul c false (ratMag c 1 n) 1 A)
def half (c : Ctx) (A : TM) : TM :=
  refresh c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 A)
def addNat (c : Ctx) (A : TM) (n : Nat) : TM :=
  addC c false (Nat.mul n c.twoS) 0 A
def divUp (n d : Nat) : Nat := Nat.div (Nat.add n (Nat.sub d 1)) d

structure SeriesState where
  term : TM
  value : TM
  slope : TM

def seriesEvaluate (c : Ctx) (Q X : TM) : Nat → SeriesState
  | 0 => ⟨X,zeroTM,zeroTM⟩
  | n+1 =>
    let Z := seriesEvaluate c Q X n
    let U := rdiv c (rmul c Z.term X) (n+2)
    ⟨rmul c U (addNat c Q (n+1)), radd c Z.value U, radd c Z.slope Z.term⟩

structure JetPair where
  value : TM
  slope : TM

def zeroPair : JetPair := ⟨zeroTM,zeroTM⟩

def valueTail (c : Ctx) (N rnum rden : Nat) : Nat :=
  divUp (Nat.mul c.twoS (Nat.pow rnum (N+2)))
    (Nat.mul (Nat.mul (N+2) (Nat.pow rden (N+1))) (Nat.sub rden rnum))
def slopeTail (c : Ctx) (N rnum rden : Nat) : Nat :=
  divUp (Nat.mul c.twoS (Nat.pow rnum (N+1)))
    (Nat.mul (Nat.pow rden N) (Nat.sub rden rnum))

def positivePair (c : Ctx) (Q X : TM) (N rnum rden : Nat) : JetPair :=
  let Z := seriesEvaluate c Q X N
  let V := widen Z.value (valueTail c N rnum rden)
  let S := widen Z.slope (slopeTail c N rnum rden)
  ⟨{ V with ok := V.ok && Nat.blt rnum rden },
   { S with ok := S.ok && Nat.blt rnum rden }⟩

/-- Checked dyadic enclosure of `1/sqrt(2)`. -/
def ir2TM (c : Ctx) (r2 : Nat) : TM :=
  let T := constTM c false r2 1
  let X := Nat.pow 2 (Nat.sub (Nat.mul 2 c.S) 1)
  { T with ok := T.ok && Nat.ble 1 c.S && Nat.ble (Nat.mul r2 r2) X &&
    Nat.blt X (Nat.mul (r2+1) (r2+1)) }

/-- Canonical order A,B,C,D; slopes are derivatives in the x variable. -/
def proposedJets (c : Ctx) (Q P IR : TM) (p : Parameters) : List JetPair :=
  let oneMinus := refresh c (addC c false c.twoS 0 (neg c P))
  let plus := refresh c (addC c false c.twoS 0 IR)
  let minus := refresh c (addC c false c.twoS 0 (neg c IR))
  let yc := refresh c (addC c true c.twoS 0 (rmul c oneMinus plus))
  let xd := half c (rmul c oneMinus minus)
  let HJ := positivePair c Q (constTM c false (Nat.pow 2 (Nat.sub c.S 1)) 0) p.anchorTerms 1 2
  let BS := positivePair c Q P p.heightTerms 1 3
  let CT := positivePair c Q yc p.reducedCTerms 17 64
  let DU := positivePair c Q xd p.reducedDTerms 1 8
  let W := addC c false c.twoS 0 (rmul c Q HJ.slope)
  let VA := radd c (radd c HJ.value (rmul c (half c P) HJ.slope)) (rmul c (half c W) BS.value)
  let SA := radd c HJ.slope (rmul c W BS.slope)
  let VC := radd c (radd c HJ.value (rmul c (half c yc) HJ.slope)) (rmul c (half c W) CT.value)
  let SC := radd c HJ.slope (rmul c W CT.slope)
  [⟨VA,SA⟩,BS,⟨VC,SC⟩,DU]

def rootFromJets (c : Ctx) (IR : TM) (jets : List JetPair) : TM :=
  let plus := refresh c (addC c false c.twoS 0 IR)
  let minus := refresh c (addC c false c.twoS 0 (neg c IR))
  let Z := radd c (jets.getD 0 zeroPair).slope (jets.getD 1 zeroPair).slope
  let Z := radd c Z (neg c (rmul c plus (jets.getD 2 zeroPair).slope))
  let Z := radd c Z (neg c (rmul c minus (jets.getD 3 zeroPair).slope))
  refresh c (smul c false (Nat.mul 16 c.twoS) 0 Z)

/-- Source order A,C,B,D, followed by the unused endpoint dummy. -/
def sourceNodes (c : Ctx) (IR A : TM) : List TM :=
  let w := rmul c IR (addC c false c.twoS 0 (neg c A))
  [refresh c A, radd c (neg c A) w,
   refresh c (addC c true c.twoS 0 (add c A A)),
   refresh c (neg c (add c A w)), constTM c true c.twoS 0]

/-! The following confluent-table and Horner routines are adapted from the
read-only positive project's `ThomsonCompact.Target.Core`. -/
def colStep (c : Ctx) (Vs Hs Gs : List (List TM)) (k : Nat) : List Nat → List Nat → List TM → List TM
  | l :: ls, h :: hs, x :: y :: rest =>
    cond (Nat.beq h l) ((Vs.getD l []).getD (k+1) zeroTM)
      (divR c (add c y (neg c x)) ((Hs.getD h []).getD l zeroTM) ((Gs.getD h []).getD l zeroTM)) ::
      colStep c Vs Hs Gs k ls hs (y :: rest)
  | _, _, _ => []

def newtonCoeffs (c : Ctx) (Vs Hs Gs : List (List TM)) (labels : List Nat) : Nat → Nat → List TM → List TM
  | 0, _, _ => []
  | r+1,k,col => col.headD zeroTM ::
      newtonCoeffs c Vs Hs Gs labels r (k+1) (colStep c Vs Hs Gs k labels (labels.drop (k+1)) col)

def timesNode (c : Ctx) (x : TM) (neg1 : Bool) (p : TM) : TM :=
  cond neg1 (neg c p) (mul c x p)

def hrest (c : Ctx) (x : TM) (neg1 : Bool) : List TM → List TM
  | p :: q :: rest => refresh c (add c p (neg c (timesNode c x neg1 q))) :: hrest c x neg1 (q :: rest)
  | L => L

def hstep (c : Ctx) (x : TM) (neg1 : Bool) (ci : TM) : List TM → List TM
  | [] => [ci]
  | p :: ps => refresh c (add c ci (neg c (timesNode c x neg1 p))) :: hrest c x neg1 (p :: ps)

def hornerN (c : Ctx) (Xs : List TM) : List Nat → List TM → List TM
  | l :: ls,ci :: cs => hstep c (Xs.getD l zeroTM) (Nat.beq l 4) ci (hornerN c Xs ls cs)
  | _,_ => []

def labels : List Nat := [0,0,1,1,2,2,3,3]

def hermiteCoefficients (c : Ctx) (p : Parameters) (nodes : List TM) (jets : List JetPair) : List TM :=
  let Vs := ([0,2,1,3] : List Nat).map (fun i =>
    [(jets.getD i zeroPair).value, half c (jets.getD i zeroPair).slope])
  let Hs := (List.range 4).map (fun h => (List.range 4).map (fun l =>
    radd c (nodes.getD h zeroTM) (neg c (nodes.getD l zeroTM))))
  let Gs := (List.range 4).map (fun h => (List.range 4).map (fun l =>
    if Nat.beq h l then zeroTM else invN c p.newtonFuel p.tolerance ((Hs.getD h []).getD l zeroTM)))
  let col := labels.map (fun l => (Vs.getD l []).getD 0 zeroTM)
  hornerN c nodes labels (newtonCoeffs c Vs Hs Gs labels 8 0 col)

def allOK : List TM → Bool
  | [] => true
  | T :: ts => T.ok && allOK ts

def allJetsOK : List JetPair → Bool
  | [] => true
  | J :: js => J.value.ok && J.slope.ok && allJetsOK js

def proposalTube (c : Ctx) (P : TM) : TM :=
  addC c true (ratMag c 31 96) 1 P
def proposalTubeOK (c : Ctx) (P : TM) : Bool :=
  (proposalTube c P).ok && Nat.blt (Nat.mul 96 (rangeX c (proposalTube c P))) c.twoS

structure Result where
  rootResidual : TM
  rootError : Nat
  height : TM
  jets : List JetPair
  nodes : List TM
  coefficients : List TM
  ok : Bool

def build (c : Ctx) (Q P : TM) (ir2 : Nat) (p : Parameters := defaultParameters) : Result :=
  let IR := ir2TM c ir2
  let originalJets := proposedJets c Q P IR p
  let R := rootFromJets c IR originalJets
  let eps := divUp (rangeX c R) 96
  let A := widen P eps
  let jets := originalJets.map (fun J =>
    JetPair.mk (widen J.value (Nat.mul 2 eps)) (widen J.slope (Nat.mul 9 eps)))
  let nodes := sourceNodes c IR A
  let coefficients := hermiteCoefficients c p nodes jets
  ⟨R,eps,A,jets,nodes,coefficients,
   Nat.ble 1 c.S && IR.ok && Q.ok && P.ok && R.ok && proposalTubeOK c P &&
     allJetsOK jets && allOK coefficients⟩

end ThomsonNegative.Compact.Target
