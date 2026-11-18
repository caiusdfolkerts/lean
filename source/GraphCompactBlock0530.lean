module
prelude
public import ResidualBatch.Graph
public import GraphInputsRow29Part00096Data
public import InducedTerminalMatches.M053
public import InducedTerminalMatches.M054

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0530
open Papers.RationalityTen ConcreteGrowth FiniteChecks ResidualBatch GraphFiniteDispatch
open Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096

private def record000Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record000Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258080 654820258080)))
(.branch 3
(.leaf (.permutation 654819275280 654819275280))
(.leaf (.permutation 654819275040 654819275040))))

private def record001Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record001Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 590394765600 590394765600)))

private def record002Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record002Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))
(.branch 3
(.leaf (.permutation 590394765840 590394765840))
(.leaf (.permutation 590394765825 590394765825))))

private def record003Leaf : Table RawLeafCertificate.Certificate :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1724))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1725)))
 (.branch 3
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1726))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1727))))
 (.branch 6
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1728))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1729)))
 (.branch 7
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1730))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1731)))))

private def record003Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654568538640 654568538640)))

private def record004Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record004Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654568538640 654568538640)))

private def record005Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record006Leaf : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1732))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1733))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1734))))
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1735))
 (.branch 5
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1736))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M054.r1737)))))

private def table : Table Packet :=
(.branch 3
(.branch 1
(.leaf ⟨record000, 16711793311744, (fun j => record000Frame.get j.val), fun j => record000Leaf.get j.val⟩)
(.branch 2
(.leaf ⟨record001, 16720379052032, (fun j => record001Frame.get j.val), fun j => record001Leaf.get j.val⟩)
(.leaf ⟨record002, 16721114038272, (fun j => record002Frame.get j.val), fun j => record002Leaf.get j.val⟩)))
(.branch 5
(.branch 4
(.leaf ⟨record003, 16769851359488, (fun j => record003Frame.get j.val), fun j => record003Leaf.get j.val⟩)
(.leaf ⟨record004, 16769863389184, (fun j => record004Frame.get j.val), fun j => record004Leaf.get j.val⟩))
(.branch 6
(.leaf ⟨record005, 16769995509760, (fun _ => .identity), fun j => record005Leaf.get j.val⟩)
(.leaf ⟨record006, 16770253996160, (fun _ => .identity), fun j => record006Leaf.get j.val⟩))))

private def packets (i : Fin 7) : Packet := table.get i.val

private def metadataVerifiedTest : Nat → Bool := metadataAt packets

private theorem metadataVerified000 : Interval metadataVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem metadataVerified001 : Interval metadataVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem metadataVerified002 : Interval metadataVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem metadataVerified003 : Interval metadataVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem metadataVerified004 : Interval metadataVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem metadataVerified005 : Interval metadataVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem metadataVerified006 : Interval metadataVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem metadataVerified : Interval metadataVerifiedTest 0 7 :=
(interval_append _ 0 3 7 (interval_append _ 0 1 3 metadataVerified000 (interval_append _ 1 2 3 metadataVerified001 metadataVerified002)) (interval_append _ 3 5 7 (interval_append _ 3 4 5 metadataVerified003 metadataVerified004) (interval_append _ 5 6 7 metadataVerified005 metadataVerified006)))

private def nodesVerifiedTest : Nat → Bool := PackedGraphCertificate.batchNodeTest (fun i => (packets i).data) (checkedMetadata packets metadataVerified)

private theorem nodesVerified000 : Interval nodesVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem nodesVerified001 : Interval nodesVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem nodesVerified002 : Interval nodesVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem nodesVerified003 : Interval nodesVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem nodesVerified004 : Interval nodesVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem nodesVerified005 : Interval nodesVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem nodesVerified006 : Interval nodesVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem nodesVerified : Interval nodesVerifiedTest 0 7 :=
(interval_append _ 0 3 7 (interval_append _ 0 1 3 nodesVerified000 (interval_append _ 1 2 3 nodesVerified001 nodesVerified002)) (interval_append _ 3 5 7 (interval_append _ 3 4 5 nodesVerified003 nodesVerified004) (interval_append _ 5 6 7 nodesVerified005 nodesVerified006)))

private def sideVerifiedTest : Nat → Bool := fun j => sideCheck (packets (Fin.ofNat 7 j))

private theorem sideVerified000 : Interval sideVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem sideVerified001 : Interval sideVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem sideVerified002 : Interval sideVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem sideVerified003 : Interval sideVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem sideVerified004 : Interval sideVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem sideVerified005 : Interval sideVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem sideVerified006 : Interval sideVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem sideVerified : Interval sideVerifiedTest 0 7 :=
(interval_append _ 0 3 7 (interval_append _ 0 1 3 sideVerified000 (interval_append _ 1 2 3 sideVerified001 sideVerified002)) (interval_append _ 3 5 7 (interval_append _ 3 4 5 sideVerified003 sideVerified004) (interval_append _ 5 6 7 sideVerified005 sideVerified006)))

private def rowsVerifiedTest : Nat → Bool := fun j => rowCheck 29 (packets (Fin.ofNat 7 j))

private theorem rowsVerified000 : Interval rowsVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem rowsVerified001 : Interval rowsVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem rowsVerified002 : Interval rowsVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem rowsVerified003 : Interval rowsVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem rowsVerified004 : Interval rowsVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem rowsVerified005 : Interval rowsVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem rowsVerified006 : Interval rowsVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem rowsVerified : Interval rowsVerifiedTest 0 7 :=
(interval_append _ 0 3 7 (interval_append _ 0 1 3 rowsVerified000 (interval_append _ 1 2 3 rowsVerified001 rowsVerified002)) (interval_append _ 3 5 7 (interval_append _ 3 4 5 rowsVerified003 rowsVerified004) (interval_append _ 5 6 7 rowsVerified005 rowsVerified006)))

private def keysVerifiedTest : Nat → Bool := fun j => keysCheck 21850 29 (packets (Fin.ofNat 7 j)) j

private theorem keysVerified000 : Interval keysVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem keysVerified001 : Interval keysVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem keysVerified002 : Interval keysVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem keysVerified003 : Interval keysVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem keysVerified004 : Interval keysVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem keysVerified005 : Interval keysVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem keysVerified006 : Interval keysVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem keysVerified : Interval keysVerifiedTest 0 7 :=
(interval_append _ 0 3 7 (interval_append _ 0 1 3 keysVerified000 (interval_append _ 1 2 3 keysVerified001 keysVerified002)) (interval_append _ 3 5 7 (interval_append _ 3 4 5 keysVerified003 keysVerified004) (interval_append _ 5 6 7 keysVerified005 keysVerified006)))

public theorem complete : Block 21850 21857 :=
  completeBlock 21850 29 packets metadataVerified nodesVerified sideVerified rowsVerified keysVerified

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0530
