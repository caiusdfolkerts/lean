module
prelude
public import FastBatchedGrowth
public import ConcreteGrowth

@[expose] public section

/-! Direct natural-number records avoid proof-bearing literals and repeated
packed-field decoding while keeping all semantic checks unchanged. -/

namespace Papers.RationalityTen.RawBatchGrowth

structure Closed where
  ridge : Nat
  first : Nat
  second : Nat

structure Child where
  cell : Nat
  node : Nat
  frame : Nat

inductive Action where
  | terminal (entry : Nat)
  | split (ridge owner : Nat) (closed : List Closed) (children : List Child)

structure Node where
  cells : List Nat
  mask : Nat
  action : Action

def decodeClosed {n r : Nat} [NeZero n] [NeZero r] (w : Closed) :
    BatchedGrowthPruning.ClosedWitness n r :=
  ⟨Fin.ofNat r w.ridge,Fin.ofNat n w.first,Fin.ofNat n w.second⟩

def decodeChild {n g t : Nat} [NeZero n] [NeZero g] [NeZero t] (c : Child) :
    BatchedOrbitGrowth.Child n g t :=
  ⟨Fin.ofNat n c.cell,Fin.ofNat t c.node,Fin.ofNat g c.frame⟩

def decodeAction {n r g k t : Nat}
    [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t] :
    Action → BatchedOrbitGrowth.Action n r g k t
  | .terminal j => .terminal (Fin.ofNat k j)
  | .split q a closed children => .split (Fin.ofNat r q) (Fin.ofNat n a)
      (closed.map decodeClosed) (children.map decodeChild)

def decodeNode {n r g k t : Nat}
    [NeZero n] [NeZero r] [NeZero g] [NeZero k] [NeZero t]
    (raw : Node) : BatchedOrbitGrowth.Node n r g k t :=
  ⟨raw.cells.map (Fin.ofNat n),raw.mask,decodeAction raw.action⟩

end Papers.RationalityTen.RawBatchGrowth
