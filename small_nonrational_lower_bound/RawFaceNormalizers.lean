module
prelude
public import RawFacePlacement
public import FiniteMaskSets

@[expose] public section

namespace Papers.RationalityTen.RawFaceNormalizers

open ConcreteGrowth RawFacePlacement

def permutationAt (n forward inverse i : Nat) : Bool :=
  decide (digit forward i < n ∧ digit inverse i < n ∧
    digit inverse (digit forward i) = i ∧ digit forward (digit inverse i) = i)

def permutationCheck (n forward inverse : Nat) : Bool :=
  (List.range n).all (permutationAt n forward inverse)

def blockValidCheck (size : Nat) (B : Block) : Bool :=
  decide (B.shared ≤ size ∧ size - B.shared ≤ B.outside ∧ B.shared + B.outside ≤ 10) &&
    (permutationCheck size B.sourceForward B.sourceInverse &&
      permutationCheck 10 B.targetForward B.targetInverse)

def normalizationCheck (size sourceFace rootFace rootVertices : Nat) (B : Block) : Bool :=
  blockValidCheck size B &&
    ((List.range size).all (fun i => decide
      (sourceFace.testBit (digit B.sourceForward i) = decide (i < B.shared))) &&
    ((List.range 10).all (fun i => decide
      (rootFace.testBit (digit B.targetForward i) = decide (i < B.shared))) &&
    (List.range 10).all (fun i => decide
      (!rootVertices.testBit (digit B.targetForward i) =
        decide (B.shared ≤ i ∧ i < B.shared + B.outside)))))

/-- All proper faces, with complete edge and polygon masks retained. -/
def faces (size : Nat) (C : Cell) : List Nat :=
  [0] ++ (((FiniteMaskSets.elements size C.vertices).map fun i => 2 ^ i.val) ++
    (C.edges ++ C.ridgeMasks))

def pairFits (size : Nat) (template root : Cell) (sourceFace rootFace : Nat) : Prop :=
  FiniteMaskSets.card size sourceFace = FiniteMaskSets.card 10 rootFace ∧
    size - FiniteMaskSets.card size sourceFace ≤
      10 - FiniteMaskSets.card 10 root.vertices

instance (size : Nat) (template root : Cell) (sourceFace rootFace : Nat) :
    Decidable (pairFits size template root sourceFace rootFace) :=
  inferInstanceAs (Decidable
    (FiniteMaskSets.card size sourceFace = FiniteMaskSets.card 10 rootFace ∧
      size - FiniteMaskSets.card size sourceFace ≤
        10 - FiniteMaskSets.card 10 root.vertices))

def completeCheck {n : Nat} (size : Nat) (template root : Cell)
    (blocks : Fin n → Block) (witness : Nat → Nat → Fin n) : Bool :=
  (faces size template).all fun sourceFace => (faces 10 root).all fun rootFace =>
    if pairFits size template root sourceFace rootFace then
      normalizationCheck size sourceFace rootFace root.vertices
        (blocks (witness sourceFace rootFace))
    else true

end Papers.RationalityTen.RawFaceNormalizers
