module
prelude
public import SharedSmallGraph
public import GraphRootExclusion

@[expose] public section

/-!
# Compact shared empty-root certificates

The stored natural numbers contain only a graph mask, one pruning rule,
explicit ridge-support removals, and finite covering lists. The complete
candidate mask is recomputed from the checked global incidence rows.
All decoding is transparent and the decoded certificate is checked by the
same semantic checker used for an ordinary explicit record.
-/

namespace Papers.RationalityTen.SharedSmallRootReplay

open ConcreteGrowth GrowthBitsets GraphGrowthConstraints UnsupportedRidgePruning

def complement (code : Nat) : Nat := Nat.land code (2^48-1)

def rule (code : Nat) : Rule 1024 45 10 5 :=
  let word := Nat.land (code >>> 48) (2^48-1)
  let value := word >>> 3
  if Nat.land word 7 = 0 then .edge (Fin.ofNat 45 value)
  else if Nat.land word 7 = 1 then .kindCapacity (Fin.ofNat 5 value)
  else if Nat.land word 7 = 2 then .vertexCapacity (Fin.ofNat 10 value)
  else .nonedgeCapacity value

def unpackRemovals : Nat → Nat → List (Removal 6510 1024) × Nat
  | 0, code => ([], code)
  | count+1, code =>
      let tail := unpackRemovals count (code / 4294967296)
      (⟨Fin.ofNat 6510 (code % 65536),
        Fin.ofNat 1024 ((code / 65536) % 65536)⟩ :: tail.1, tail.2)

def unpackBounds : Nat → Nat → FastGraphRuleCheck.Bounds 6510 × Nat
  | 0, code => ([], code)
  | count+1, code =>
      if code % 65536 = 0 then
        let tail := unpackBounds count (code / 65536)
        (none :: tail.1, tail.2)
      else
        let values := unpackList (code / 65536)
        let tail := unpackBounds count values.2
        (some (values.1.map (Fin.ofNat 6510)) :: tail.1, tail.2)

def removalsAndRest (code : Nat) : List (Removal 6510 1024) × Nat :=
  let body := code >>> 96
  unpackRemovals (body % 65536) (body / 65536)

noncomputable def certificate (quota : Nat → Nat) (code : Nat) :
    GraphRootExclusion.Certificate 6510 1024 45 10 5 :=
  let eligible := GraphCandidateCoverage.eligibleMask SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask quota) (complement code)
  let removals := (removalsAndRest code).1
  let blocked := Nat.xor (FiniteMaskSets.allMask 6510) eligible
  let final := resultingMask blocked removals
  ⟨eligible, Nat.xor (FiniteMaskSets.allMask 6510) final, removals,
    (unpackBounds 5 (removalsAndRest code).2).1, rule code⟩

noncomputable def check (quota : Nat → Nat) (missingCount code : Nat) : Bool :=
  GraphRootExclusion.check
    (SharedSmallGraph.problem quota
      (SharedSmallGraph.requiredMask (complement code)) missingCount)
    (certificate quota code)

theorem certificate_eligible (quota : Nat → Nat) (code : Nat) :
    (certificate quota code).eligible =
      GraphCandidateCoverage.eligibleMask SharedSmallGraph.graphRows
        (SharedSmallGraph.allowedMask quota) (complement code) := rfl

end Papers.RationalityTen.SharedSmallRootReplay
