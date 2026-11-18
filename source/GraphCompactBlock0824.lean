module
prelude
public import ResidualBatch.Graph
public import GraphInputsRow31Part00036Data
public import InducedTerminalMatches.M078
public import InducedTerminalMatches.M079

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0824
open Papers.RationalityTen ConcreteGrowth FiniteChecks ResidualBatch GraphFiniteDispatch
open Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00036

private def record000Leaf : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2521))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2522))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2523))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2524))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2525)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2526))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M078.r2527)))))

private def record000Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 650777994000 650777994000)))

private def record001Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.vertexLink 0))

private def record001Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))
(.branch 3
(.leaf (.permutation 650777997840 650777997840))
(.leaf (.permutation 650777997825 650777997825))))

private def record002Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.matching Nonrational.InducedTerminalMatches.M079.r2528))

private def record002Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))
(.branch 3
(.leaf (.permutation 650777936400 650777936400))
(.leaf (.permutation 650777936385 650777936385))))

private def table : Table Packet :=
(.branch 1
(.leaf ⟨record000, 7562502144000, (fun j => record000Frame.get j.val), fun j => record000Leaf.get j.val⟩)
(.branch 2
(.leaf ⟨record001, 7562774708224, (fun j => record001Frame.get j.val), fun j => record001Leaf.get j.val⟩)
(.leaf ⟨record002, 7564855083008, (fun j => record002Frame.get j.val), fun j => record002Leaf.get j.val⟩)))

private def packets (i : Fin 3) : Packet := table.get i.val

private def metadataVerifiedTest : Nat → Bool := metadataAt packets

private theorem metadataVerified000 : Interval metadataVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem metadataVerified001 : Interval metadataVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem metadataVerified002 : Interval metadataVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem metadataVerified : Interval metadataVerifiedTest 0 3 :=
(interval_append _ 0 1 3 metadataVerified000 (interval_append _ 1 2 3 metadataVerified001 metadataVerified002))

private def nodesVerifiedTest : Nat → Bool := PackedGraphCertificate.batchNodeTest (fun i => (packets i).data) (checkedMetadata packets metadataVerified)

private theorem nodesVerified000 : Interval nodesVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem nodesVerified001 : Interval nodesVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem nodesVerified002 : Interval nodesVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem nodesVerified : Interval nodesVerifiedTest 0 3 :=
(interval_append _ 0 1 3 nodesVerified000 (interval_append _ 1 2 3 nodesVerified001 nodesVerified002))

private def sideVerifiedTest : Nat → Bool := fun j => sideCheck (packets (Fin.ofNat 3 j))

private theorem sideVerified000 : Interval sideVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem sideVerified001 : Interval sideVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem sideVerified002 : Interval sideVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem sideVerified : Interval sideVerifiedTest 0 3 :=
(interval_append _ 0 1 3 sideVerified000 (interval_append _ 1 2 3 sideVerified001 sideVerified002))

private def rowsVerifiedTest : Nat → Bool := fun j => rowCheck 31 (packets (Fin.ofNat 3 j))

private theorem rowsVerified000 : Interval rowsVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem rowsVerified001 : Interval rowsVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem rowsVerified002 : Interval rowsVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem rowsVerified : Interval rowsVerifiedTest 0 3 :=
(interval_append _ 0 1 3 rowsVerified000 (interval_append _ 1 2 3 rowsVerified001 rowsVerified002))

private def keysVerifiedTest : Nat → Bool := fun j => keysCheck 25786 31 (packets (Fin.ofNat 3 j)) j

private theorem keysVerified000 : Interval keysVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem keysVerified001 : Interval keysVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem keysVerified002 : Interval keysVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem keysVerified : Interval keysVerifiedTest 0 3 :=
(interval_append _ 0 1 3 keysVerified000 (interval_append _ 1 2 3 keysVerified001 keysVerified002))

public theorem complete : Block 25786 25789 :=
  completeBlock 25786 31 packets metadataVerified nodesVerified sideVerified rowsVerified keysVerified

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0824
