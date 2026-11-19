module
prelude
public import WitnessGrowthDAG
public import Init.Data.Nat.Bitwise.Basic

@[expose] public section

/-!
# Literal masked cells and balanced certificate tables

All masks denote subsets of the ten vertex labels. A cell contains its vertex
mask, edge masks, and ridge masks. Pair compatibility is computed directly from
those masks; no producer-supplied compatibility matrix is trusted. Balanced
tables give the kernel logarithmic access to literal records.
-/

namespace Papers.RationalityTen.ConcreteGrowth

open GrowthDAG SparseGrowthDAG GrowthPruning

inductive Table (α : Type) where
  | leaf (value : α)
  | branch (cut : Nat) (left right : Table α)

def Table.get {α : Type} : Table α → Nat → α
  | .leaf value, _ => value
  | .branch cut left right, i => if i < cut then left.get i else right.get i

structure Cell where
  kind : Nat
  vertices : Nat
  edges : List Nat
  ridgeMasks : List Nat

def hasMask (values : List Nat) (mask : Nat) : Bool :=
  values.any fun value => decide (value = mask)

/-- Empty sets, singleton vertices, edges, and ridges are the proper faces.
The singleton test is applied only to an intersection of cell vertex masks. -/
def proper (cell : Cell) (mask : Nat) : Bool :=
  decide (Nat.land mask (mask - 1) = 0) ||
    hasMask cell.edges mask || hasMask cell.ridgeMasks mask

def compatible (a b : Cell) : Bool :=
  let common := Nat.land a.vertices b.vertices
  (proper a common && proper b common) &&
    decide ((a.edges.filter fun e => decide (Nat.land e common = e)) =
            (b.edges.filter fun e => decide (Nat.land e common = e)))

def ridgeList {n : Nat} (cells : Fin n → Cell) (c : Fin n) : List (Fin 1024) :=
  (cells c).ridgeMasks.map (Fin.ofNat 1024)

inductive RawRejection where
  | selected
  | quota
  | incompatible (cell : Nat)
  | closedRidge (ridge : Nat)

inductive RawChoice where
  | rejected (reason : RawRejection)
  | child (index : Nat)

inductive RawAction where
  | terminal (entry : Nat)
  | split (ridge witness : Nat) (records : List (Nat × RawChoice))

structure RawNode where
  cells : List Nat
  action : RawAction

def decodeRejection {n : Nat} [NeZero n] : RawRejection → WitnessGrowthDAG.Rejection n 1024
  | .selected => .selected
  | .quota => .quota
  | .incompatible a => .incompatible (Fin.ofNat n a)
  | .closedRidge q => .closedRidge (Fin.ofNat 1024 q)

def decodeChoice {n t : Nat} [NeZero n] [NeZero t] :
    RawChoice → WitnessGrowthDAG.Choice n 1024 t
  | .rejected reason => .rejected (decodeRejection reason)
  | .child j => .child (Fin.ofNat t j)

def decodeAction {n k t : Nat} [NeZero n] [NeZero k] [NeZero t] :
    RawAction → WitnessGrowthDAG.Action n 1024 k t
  | .terminal j => .terminal (Fin.ofNat k j)
  | .split q a records => .split (Fin.ofNat 1024 q) (Fin.ofNat n a)
      (records.map fun row => (Fin.ofNat n row.1, decodeChoice row.2))

def decodeNode {n k t : Nat} [NeZero n] [NeZero k] [NeZero t]
    (raw : RawNode) : WitnessGrowthDAG.Node n 1024 k t :=
  ⟨raw.cells.map (Fin.ofNat n), decodeAction raw.action⟩

end Papers.RationalityTen.ConcreteGrowth
