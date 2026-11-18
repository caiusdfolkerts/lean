module
prelude
public import ResidualBatch.Graph
public import GraphInputsRow29Part00093Data
public import InducedTerminalMatches.M053

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0527
open Papers.RationalityTen ConcreteGrowth FiniteChecks ResidualBatch GraphFiniteDispatch
open Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093

private def record000Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record000Frame : Table FrameWitness :=
(.branch 3
(.branch 1
(.leaf (.identity))
(.branch 2
(.leaf (.permutation 590143103760 590143103760))
(.leaf (.permutation 509359576080 509359576080))))
(.branch 5
(.branch 4
(.leaf (.permutation 444682421520 444682421520))
(.leaf (.permutation 654820258305 654820258305)))
(.branch 6
(.leaf (.permutation 590143103745 590143103745))
(.leaf (.permutation 509359576065 509359576065)))))

private def record001Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record002Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1713))

private def record003Leaf : Table RawLeafCertificate.Certificate :=
(.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1714))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1715)))

private def record003Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654567613200 654567613200)))

private def record004Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record005Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record005Frame : Table FrameWitness :=
(.branch 5
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820254480 654820254480)))
(.branch 3
(.leaf (.permutation 654820258305 654820258305))
(.branch 4
(.leaf (.permutation 654820254465 654820254465))
(.leaf (.permutation 590395740210 590395740210)))))
(.branch 7
(.branch 6
(.leaf (.permutation 590395736370 590395740195))
(.leaf (.permutation 654567617040 654567617040)))
(.branch 8
(.leaf (.permutation 654567613200 654567613200))
(.branch 9
(.leaf (.permutation 654567617025 654567617025))
(.leaf (.permutation 654567613185 654567613185))))))

private def record006Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record006Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820254480 654820254480)))
(.branch 3
(.leaf (.permutation 654567617040 654567617040))
(.leaf (.permutation 654567613200 654567613200))))

private def record007Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record007Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654567617040 654567617040)))
(.branch 3
(.leaf (.permutation 590395748640 590395748640))
(.leaf (.permutation 590143107360 590143107360))))

private def record008Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record008Frame : Table FrameWitness :=
(.branch 3
(.branch 1
(.leaf (.identity))
(.branch 2
(.leaf (.permutation 654567617040 654567617040))
(.leaf (.permutation 654820254480 654820254480))))
(.branch 4
(.leaf (.permutation 654567613200 654567613200))
(.branch 5
(.leaf (.permutation 654820258305 654820258305))
(.leaf (.permutation 654567617025 654567617025)))))

private def record009Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def table : Table Packet :=
(.branch 5
(.branch 2
(.branch 1
(.leaf ⟨record000, 16531623247873, (fun j => record000Frame.get j.val), fun j => record000Leaf.get j.val⟩)
(.leaf ⟨record001, 16531623313408, (fun _ => .identity), fun j => record001Leaf.get j.val⟩))
(.branch 3
(.leaf ⟨record002, 16531883327744, (fun _ => .identity), fun j => record002Leaf.get j.val⟩)
(.branch 4
(.leaf ⟨record003, 16531891716096, (fun j => record003Frame.get j.val), fun j => record003Leaf.get j.val⟩)
(.leaf ⟨record004, 16531895357440, (fun _ => .identity), fun j => record004Leaf.get j.val⟩))))
(.branch 7
(.branch 6
(.leaf ⟨record005, 16532675559680, (fun j => record005Frame.get j.val), fun j => record005Leaf.get j.val⟩)
(.leaf ⟨record006, 16532948287488, (fun j => record006Frame.get j.val), fun j => record006Leaf.get j.val⟩))
(.branch 8
(.leaf ⟨record007, 16533212430336, (fun j => record007Frame.get j.val), fun j => record007Leaf.get j.val⟩)
(.branch 9
(.leaf ⟨record008, 16533220753408, (fun j => record008Frame.get j.val), fun j => record008Leaf.get j.val⟩)
(.leaf ⟨record009, 16536188227584, (fun _ => .identity), fun j => record009Leaf.get j.val⟩)))))

private def packets (i : Fin 10) : Packet := table.get i.val

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

private theorem metadataVerified007 : Interval metadataVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem metadataVerified008 : Interval metadataVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem metadataVerified009 : Interval metadataVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem metadataVerified : Interval metadataVerifiedTest 0 10 :=
(interval_append _ 0 5 10 (interval_append _ 0 2 5 (interval_append _ 0 1 2 metadataVerified000 metadataVerified001) (interval_append _ 2 3 5 metadataVerified002 (interval_append _ 3 4 5 metadataVerified003 metadataVerified004))) (interval_append _ 5 7 10 (interval_append _ 5 6 7 metadataVerified005 metadataVerified006) (interval_append _ 7 8 10 metadataVerified007 (interval_append _ 8 9 10 metadataVerified008 metadataVerified009))))

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

private theorem nodesVerified007 : Interval nodesVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem nodesVerified008 : Interval nodesVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem nodesVerified009 : Interval nodesVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem nodesVerified : Interval nodesVerifiedTest 0 10 :=
(interval_append _ 0 5 10 (interval_append _ 0 2 5 (interval_append _ 0 1 2 nodesVerified000 nodesVerified001) (interval_append _ 2 3 5 nodesVerified002 (interval_append _ 3 4 5 nodesVerified003 nodesVerified004))) (interval_append _ 5 7 10 (interval_append _ 5 6 7 nodesVerified005 nodesVerified006) (interval_append _ 7 8 10 nodesVerified007 (interval_append _ 8 9 10 nodesVerified008 nodesVerified009))))

private def sideVerifiedTest : Nat → Bool := fun j => sideCheck (packets (Fin.ofNat 10 j))

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

private theorem sideVerified007 : Interval sideVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem sideVerified008 : Interval sideVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem sideVerified009 : Interval sideVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem sideVerified : Interval sideVerifiedTest 0 10 :=
(interval_append _ 0 5 10 (interval_append _ 0 2 5 (interval_append _ 0 1 2 sideVerified000 sideVerified001) (interval_append _ 2 3 5 sideVerified002 (interval_append _ 3 4 5 sideVerified003 sideVerified004))) (interval_append _ 5 7 10 (interval_append _ 5 6 7 sideVerified005 sideVerified006) (interval_append _ 7 8 10 sideVerified007 (interval_append _ 8 9 10 sideVerified008 sideVerified009))))

private def rowsVerifiedTest : Nat → Bool := fun j => rowCheck 29 (packets (Fin.ofNat 10 j))

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

private theorem rowsVerified007 : Interval rowsVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem rowsVerified008 : Interval rowsVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem rowsVerified009 : Interval rowsVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem rowsVerified : Interval rowsVerifiedTest 0 10 :=
(interval_append _ 0 5 10 (interval_append _ 0 2 5 (interval_append _ 0 1 2 rowsVerified000 rowsVerified001) (interval_append _ 2 3 5 rowsVerified002 (interval_append _ 3 4 5 rowsVerified003 rowsVerified004))) (interval_append _ 5 7 10 (interval_append _ 5 6 7 rowsVerified005 rowsVerified006) (interval_append _ 7 8 10 rowsVerified007 (interval_append _ 8 9 10 rowsVerified008 rowsVerified009))))

private def keysVerifiedTest : Nat → Bool := fun j => keysCheck 21806 29 (packets (Fin.ofNat 10 j)) j

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

private theorem keysVerified007 : Interval keysVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem keysVerified008 : Interval keysVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem keysVerified009 : Interval keysVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem keysVerified : Interval keysVerifiedTest 0 10 :=
(interval_append _ 0 5 10 (interval_append _ 0 2 5 (interval_append _ 0 1 2 keysVerified000 keysVerified001) (interval_append _ 2 3 5 keysVerified002 (interval_append _ 3 4 5 keysVerified003 keysVerified004))) (interval_append _ 5 7 10 (interval_append _ 5 6 7 keysVerified005 keysVerified006) (interval_append _ 7 8 10 keysVerified007 (interval_append _ 8 9 10 keysVerified008 keysVerified009))))

public theorem complete : Block 21806 21816 :=
  completeBlock 21806 29 packets metadataVerified nodesVerified sideVerified rowsVerified keysVerified

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0527
