module
prelude
public import ResidualBatch.Graph
public import GraphInputsRow29Part00095Data
public import InducedTerminalMatches.M053

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0529
open Papers.RationalityTen ConcreteGrowth FiniteChecks ResidualBatch GraphFiniteDispatch
open Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00095

private def record000Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record001Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record001Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654819275280 654819275280)))

private def record002Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record002Frame : Table FrameWitness :=
(.branch 4
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))
(.branch 3
(.leaf (.permutation 654819275280 654819275280))
(.leaf (.permutation 654819275265 654819275265))))
(.branch 6
(.branch 5
(.leaf (.permutation 654568596240 654568596240))
(.leaf (.permutation 654568596225 654568596225)))
(.branch 7
(.leaf (.permutation 654567613200 654567613200))
(.leaf (.permutation 654567613185 654567613185)))))

private def record003Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record004Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1723))

private def record004Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654568596240 654568596240)))
(.branch 3
(.leaf (.permutation 590394765825 590394765825))
(.leaf (.permutation 590143103745 590143103745))))

private def record005Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record005Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.branch 2
(.leaf (.permutation 590394765600 590394765600))
(.leaf (.permutation 654568600080 654568600080))))

private def record006Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record006Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))
(.branch 3
(.leaf (.permutation 590394765840 590394765840))
(.branch 4
(.leaf (.permutation 590394765825 590394765825))
(.leaf (.permutation 654568600080 654568600080)))))

private def record007Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record008Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record008Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 590143103760 590143103760)))
(.branch 3
(.leaf (.permutation 654820258305 654820258305))
(.leaf (.permutation 590143103745 590143103745))))

private def record009Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record009Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654568599840 654568599840)))
(.branch 3
(.leaf (.permutation 590394765840 590394765840))
(.leaf (.permutation 590143107360 590143107360))))

private def record010Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record011Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record011Frame : Table FrameWitness :=
(.branch 2
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258080 654820258080)))
(.branch 3
(.leaf (.permutation 654568538640 654568538640))
(.leaf (.permutation 654568538400 654568538400))))

private def record012Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record013Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record013Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))

private def record014Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record015Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record015Frame : Table FrameWitness :=
(.branch 1
(.leaf (.identity))
(.leaf (.permutation 654820258305 654820258305)))

private def table : Table Packet :=
(.branch 8
(.branch 4
(.branch 2
(.branch 1
(.leaf ⟨record000, 16632824991744, (fun _ => .identity), fun j => record000Leaf.get j.val⟩)
(.leaf ⟨record001, 16640383188992, (fun j => record001Frame.get j.val), fun j => record001Leaf.get j.val⟩))
(.branch 3
(.leaf ⟨record002, 16640391512064, (fun j => record002Frame.get j.val), fun j => record002Leaf.get j.val⟩)
(.leaf ⟨record003, 16641522466816, (fun _ => .identity), fun j => record003Leaf.get j.val⟩)))
(.branch 6
(.branch 5
(.leaf ⟨record004, 16648436220160, (fun j => record004Frame.get j.val), fun j => record004Leaf.get j.val⟩)
(.leaf ⟨record005, 16648572567552, (fun j => record005Frame.get j.val), fun j => record005Leaf.get j.val⟩))
(.branch 7
(.leaf ⟨record006, 16648580890624, (fun j => record006Frame.get j.val), fun j => record006Leaf.get j.val⟩)
(.leaf ⟨record007, 16648704688128, (fun _ => .identity), fun j => record007Leaf.get j.val⟩))))
(.branch 12
(.branch 10
(.branch 9
(.leaf ⟨record008, 16648713011200, (fun j => record008Frame.get j.val), fun j => record008Leaf.get j.val⟩)
(.leaf ⟨record009, 16649173352448, (fun j => record009Frame.get j.val), fun j => record009Leaf.get j.val⟩))
(.branch 11
(.leaf ⟨record010, 16649476407552, (fun _ => .identity), fun j => record010Leaf.get j.val⟩)
(.leaf ⟨record011, 16650111812112, (fun j => record011Frame.get j.val), fun j => record011Leaf.get j.val⟩)))
(.branch 14
(.branch 13
(.leaf ⟨record012, 16650246569984, (fun _ => .identity), fun j => record012Leaf.get j.val⟩)
(.leaf ⟨record013, 16678037487616, (fun j => record013Frame.get j.val), fun j => record013Leaf.get j.val⟩))
(.branch 15
(.leaf ⟨record014, 16686086422528, (fun _ => .identity), fun j => record014Leaf.get j.val⟩)
(.leaf ⟨record015, 16701118808320, (fun j => record015Frame.get j.val), fun j => record015Leaf.get j.val⟩)))))

private def packets (i : Fin 16) : Packet := table.get i.val

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

private theorem metadataVerified010 : Interval metadataVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem metadataVerified011 : Interval metadataVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem metadataVerified012 : Interval metadataVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem metadataVerified013 : Interval metadataVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem metadataVerified014 : Interval metadataVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem metadataVerified015 : Interval metadataVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem metadataVerified : Interval metadataVerifiedTest 0 16 :=
(interval_append _ 0 8 16 (interval_append _ 0 4 8 (interval_append _ 0 2 4 (interval_append _ 0 1 2 metadataVerified000 metadataVerified001) (interval_append _ 2 3 4 metadataVerified002 metadataVerified003)) (interval_append _ 4 6 8 (interval_append _ 4 5 6 metadataVerified004 metadataVerified005) (interval_append _ 6 7 8 metadataVerified006 metadataVerified007))) (interval_append _ 8 12 16 (interval_append _ 8 10 12 (interval_append _ 8 9 10 metadataVerified008 metadataVerified009) (interval_append _ 10 11 12 metadataVerified010 metadataVerified011)) (interval_append _ 12 14 16 (interval_append _ 12 13 14 metadataVerified012 metadataVerified013) (interval_append _ 14 15 16 metadataVerified014 metadataVerified015))))

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

private theorem nodesVerified010 : Interval nodesVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem nodesVerified011 : Interval nodesVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem nodesVerified012 : Interval nodesVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem nodesVerified013 : Interval nodesVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem nodesVerified014 : Interval nodesVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem nodesVerified015 : Interval nodesVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem nodesVerified : Interval nodesVerifiedTest 0 16 :=
(interval_append _ 0 8 16 (interval_append _ 0 4 8 (interval_append _ 0 2 4 (interval_append _ 0 1 2 nodesVerified000 nodesVerified001) (interval_append _ 2 3 4 nodesVerified002 nodesVerified003)) (interval_append _ 4 6 8 (interval_append _ 4 5 6 nodesVerified004 nodesVerified005) (interval_append _ 6 7 8 nodesVerified006 nodesVerified007))) (interval_append _ 8 12 16 (interval_append _ 8 10 12 (interval_append _ 8 9 10 nodesVerified008 nodesVerified009) (interval_append _ 10 11 12 nodesVerified010 nodesVerified011)) (interval_append _ 12 14 16 (interval_append _ 12 13 14 nodesVerified012 nodesVerified013) (interval_append _ 14 15 16 nodesVerified014 nodesVerified015))))

private def sideVerifiedTest : Nat → Bool := fun j => sideCheck (packets (Fin.ofNat 16 j))

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

private theorem sideVerified010 : Interval sideVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem sideVerified011 : Interval sideVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem sideVerified012 : Interval sideVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem sideVerified013 : Interval sideVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem sideVerified014 : Interval sideVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem sideVerified015 : Interval sideVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem sideVerified : Interval sideVerifiedTest 0 16 :=
(interval_append _ 0 8 16 (interval_append _ 0 4 8 (interval_append _ 0 2 4 (interval_append _ 0 1 2 sideVerified000 sideVerified001) (interval_append _ 2 3 4 sideVerified002 sideVerified003)) (interval_append _ 4 6 8 (interval_append _ 4 5 6 sideVerified004 sideVerified005) (interval_append _ 6 7 8 sideVerified006 sideVerified007))) (interval_append _ 8 12 16 (interval_append _ 8 10 12 (interval_append _ 8 9 10 sideVerified008 sideVerified009) (interval_append _ 10 11 12 sideVerified010 sideVerified011)) (interval_append _ 12 14 16 (interval_append _ 12 13 14 sideVerified012 sideVerified013) (interval_append _ 14 15 16 sideVerified014 sideVerified015))))

private def rowsVerifiedTest : Nat → Bool := fun j => rowCheck 29 (packets (Fin.ofNat 16 j))

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

private theorem rowsVerified010 : Interval rowsVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem rowsVerified011 : Interval rowsVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem rowsVerified012 : Interval rowsVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem rowsVerified013 : Interval rowsVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem rowsVerified014 : Interval rowsVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem rowsVerified015 : Interval rowsVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem rowsVerified : Interval rowsVerifiedTest 0 16 :=
(interval_append _ 0 8 16 (interval_append _ 0 4 8 (interval_append _ 0 2 4 (interval_append _ 0 1 2 rowsVerified000 rowsVerified001) (interval_append _ 2 3 4 rowsVerified002 rowsVerified003)) (interval_append _ 4 6 8 (interval_append _ 4 5 6 rowsVerified004 rowsVerified005) (interval_append _ 6 7 8 rowsVerified006 rowsVerified007))) (interval_append _ 8 12 16 (interval_append _ 8 10 12 (interval_append _ 8 9 10 rowsVerified008 rowsVerified009) (interval_append _ 10 11 12 rowsVerified010 rowsVerified011)) (interval_append _ 12 14 16 (interval_append _ 12 13 14 rowsVerified012 rowsVerified013) (interval_append _ 14 15 16 rowsVerified014 rowsVerified015))))

private def keysVerifiedTest : Nat → Bool := fun j => keysCheck 21834 29 (packets (Fin.ofNat 16 j)) j

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

private theorem keysVerified010 : Interval keysVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem keysVerified011 : Interval keysVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem keysVerified012 : Interval keysVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem keysVerified013 : Interval keysVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem keysVerified014 : Interval keysVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem keysVerified015 : Interval keysVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem keysVerified : Interval keysVerifiedTest 0 16 :=
(interval_append _ 0 8 16 (interval_append _ 0 4 8 (interval_append _ 0 2 4 (interval_append _ 0 1 2 keysVerified000 keysVerified001) (interval_append _ 2 3 4 keysVerified002 keysVerified003)) (interval_append _ 4 6 8 (interval_append _ 4 5 6 keysVerified004 keysVerified005) (interval_append _ 6 7 8 keysVerified006 keysVerified007))) (interval_append _ 8 12 16 (interval_append _ 8 10 12 (interval_append _ 8 9 10 keysVerified008 keysVerified009) (interval_append _ 10 11 12 keysVerified010 keysVerified011)) (interval_append _ 12 14 16 (interval_append _ 12 13 14 keysVerified012 keysVerified013) (interval_append _ 14 15 16 keysVerified014 keysVerified015))))

public theorem complete : Block 21834 21850 :=
  completeBlock 21834 29 packets metadataVerified nodesVerified sideVerified rowsVerified keysVerified

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0529
