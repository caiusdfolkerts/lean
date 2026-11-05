module
prelude
public import PackedGrowthData
public import FiniteChecks

@[expose] public section

/-! Generic finite-ridge decoding for the polygon-growth certificates.
The producer supplies data only; every decoded branch is checked by the
already proved WitnessGrowthDAG checker. -/

namespace Papers.RationalityTen.PolygonGrowth

open ConcreteGrowth

/-- Decoding is total, and its output is checked; no producer bound is trusted. -/
def decodeRejection {n r : Nat} [NeZero n] [NeZero r] :
    RawRejection → WitnessGrowthDAG.Rejection n r
  | .selected => .selected
  | .quota => .quota
  | .incompatible a => .incompatible (Fin.ofNat n a)
  | .closedRidge q => .closedRidge (Fin.ofNat r q)

def decodeChoice {n r t : Nat} [NeZero n] [NeZero r] [NeZero t] :
    RawChoice → WitnessGrowthDAG.Choice n r t
  | .rejected reason => .rejected (decodeRejection reason)
  | .child j => .child (Fin.ofNat t j)

def decodeAction {n r k t : Nat} [NeZero n] [NeZero r] [NeZero k] [NeZero t] :
    RawAction → WitnessGrowthDAG.Action n r k t
  | .terminal j => .terminal (Fin.ofNat k j)
  | .split q a records => .split (Fin.ofNat r q) (Fin.ofNat n a)
      (records.map fun row => (Fin.ofNat n row.1, decodeChoice row.2))

def decodeNode {n r k t : Nat} [NeZero n] [NeZero r] [NeZero k] [NeZero t]
    (raw : RawNode) : WitnessGrowthDAG.Node n r k t :=
  ⟨raw.cells.map (Fin.ofNat n), decodeAction raw.action⟩

end Papers.RationalityTen.PolygonGrowth
