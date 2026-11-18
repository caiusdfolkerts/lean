module
prelude
public import ResidualBatch.Graph
public import GraphInputsRow29Part00094Data
public import InducedTerminalMatches.M053

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0528
open Papers.RationalityTen ConcreteGrowth FiniteChecks ResidualBatch GraphFiniteDispatch
open Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094

private def record000Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record001Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record002Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record003Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record004Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record005Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record006Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record007Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record008Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record009Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record010Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record011Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record012Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record013Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record014Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record015Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record016Leaf : Table RawLeafCertificate.Certificate :=
(.leaf (.quota 1))

private def record017Leaf : Table RawLeafCertificate.Certificate :=
(.branch 3
 (.branch 1
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1716))
 (.branch 2
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1717))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1718))))
 (.branch 5
 (.branch 4
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1719))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1720)))
 (.branch 6
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1721))
 (.leaf (.matching Nonrational.InducedTerminalMatches.M053.r1722)))))

private def table : Table Packet :=
(.branch 9
(.branch 4
(.branch 2
(.branch 1
(.leaf ⟨record000, 16536295444736, fun _ => .identity, fun j => record000Leaf.get j.val⟩)
(.leaf ⟨record001, 16536836309248, fun _ => .identity, fun j => record001Leaf.get j.val⟩))
(.branch 3
(.leaf ⟨record002, 16537108938752, fun _ => .identity, fun j => record002Leaf.get j.val⟩)
(.leaf ⟨record003, 16537368920832, fun j => if j.val = 0 then .identity else .permutation 654820258080 654820258080, fun j => record003Leaf.get j.val⟩)))
(.branch 6
(.branch 5
(.leaf ⟨record004, 16537373179904, fun _ => .identity, fun j => record004Leaf.get j.val⟩)
(.leaf ⟨record005, 16537381502976, fun j => if j.val = 0 then .identity else .permutation 654820258305 654820258305, fun j => record005Leaf.get j.val⟩))
(.branch 7
(.leaf ⟨record006, 16537505300480, fun _ => .identity, fun j => record006Leaf.get j.val⟩)
(.branch 8
(.leaf ⟨record007, 16539956871424, fun j => if j.val = 0 then .identity else .permutation 654820258305 654820258305, fun j => record007Leaf.get j.val⟩)
(.leaf ⟨record008, 16540724953088, fun _ => .identity, fun j => record008Leaf.get j.val⟩)))))
(.branch 13
(.branch 11
(.branch 10
(.leaf ⟨record009, 16544616943872, fun _ => .identity, fun j => record009Leaf.get j.val⟩)
(.leaf ⟨record010, 16544768213120, fun j => if j.val = 0 then .identity else .permutation 654820196880 654820196880, fun j => record010Leaf.get j.val⟩))
(.branch 12
(.leaf ⟨record011, 16544773967872, fun j => if j.val = 0 then .identity else .permutation 654820196880 654820196880, fun j => record011Leaf.get j.val⟩)
(.leaf ⟨record012, 16544885379200, fun _ => .identity, fun j => record012Leaf.get j.val⟩)))
(.branch 15
(.branch 14
(.leaf ⟨record013, 16545958855296, fun j => if j.val = 0 then .identity else .permutation 654820258080 654820258080, fun j => record013Leaf.get j.val⟩)
(.leaf ⟨record014, 16549314298384, fun j => if j.val = 0 then .identity else .permutation 654820258080 654820258080, fun j => record014Leaf.get j.val⟩))
(.branch 16
(.leaf ⟨record015, 16608915423232, fun _ => .identity, fun j => record015Leaf.get j.val⟩)
(.branch 17
(.leaf ⟨record016, 16609452228608, fun _ => .identity, fun j => record016Leaf.get j.val⟩)
(.leaf ⟨record017, 16632420827136, fun j => if j.val = 0 then .identity else .permutation 654568538640 654568538640, fun j => record017Leaf.get j.val⟩))))))

private def packets (i : Fin 18) : Packet := table.get i.val

private def metadataVerifiedTest : Nat → Bool := metadataAt packets

private theorem metadataVerified00 : Interval metadataVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem metadataVerified01 : Interval metadataVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem metadataVerified02 : Interval metadataVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem metadataVerified03 : Interval metadataVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem metadataVerified04 : Interval metadataVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem metadataVerified05 : Interval metadataVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem metadataVerified06 : Interval metadataVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem metadataVerified07 : Interval metadataVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem metadataVerified08 : Interval metadataVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem metadataVerified09 : Interval metadataVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem metadataVerified10 : Interval metadataVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem metadataVerified11 : Interval metadataVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem metadataVerified12 : Interval metadataVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem metadataVerified13 : Interval metadataVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem metadataVerified14 : Interval metadataVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem metadataVerified15 : Interval metadataVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem metadataVerified16 : Interval metadataVerifiedTest 16 17 :=
  interval_of_check _ 16 1 (by decide +kernel)

private theorem metadataVerified17 : Interval metadataVerifiedTest 17 18 :=
  interval_of_check _ 17 1 (by decide +kernel)

private theorem metadataVerified : Interval metadataVerifiedTest 0 18 :=
(interval_append _ 0 9 18 (interval_append _ 0 4 9 (interval_append _ 0 2 4 (interval_append _ 0 1 2 metadataVerified00 metadataVerified01) (interval_append _ 2 3 4 metadataVerified02 metadataVerified03)) (interval_append _ 4 6 9 (interval_append _ 4 5 6 metadataVerified04 metadataVerified05) (interval_append _ 6 7 9 metadataVerified06 (interval_append _ 7 8 9 metadataVerified07 metadataVerified08)))) (interval_append _ 9 13 18 (interval_append _ 9 11 13 (interval_append _ 9 10 11 metadataVerified09 metadataVerified10) (interval_append _ 11 12 13 metadataVerified11 metadataVerified12)) (interval_append _ 13 15 18 (interval_append _ 13 14 15 metadataVerified13 metadataVerified14) (interval_append _ 15 16 18 metadataVerified15 (interval_append _ 16 17 18 metadataVerified16 metadataVerified17)))))

private def nodesVerifiedTest : Nat → Bool := PackedGraphCertificate.batchNodeTest (fun i => (packets i).data) (checkedMetadata packets metadataVerified)

private theorem nodesVerified00 : Interval nodesVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem nodesVerified01 : Interval nodesVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem nodesVerified02 : Interval nodesVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem nodesVerified03 : Interval nodesVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem nodesVerified04 : Interval nodesVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem nodesVerified05 : Interval nodesVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem nodesVerified06 : Interval nodesVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem nodesVerified07 : Interval nodesVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem nodesVerified08 : Interval nodesVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem nodesVerified09 : Interval nodesVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem nodesVerified10 : Interval nodesVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem nodesVerified11 : Interval nodesVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem nodesVerified12 : Interval nodesVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem nodesVerified13 : Interval nodesVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem nodesVerified14 : Interval nodesVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem nodesVerified15 : Interval nodesVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem nodesVerified16 : Interval nodesVerifiedTest 16 17 :=
  interval_of_check _ 16 1 (by decide +kernel)

private theorem nodesVerified17 : Interval nodesVerifiedTest 17 18 :=
  interval_of_check _ 17 1 (by decide +kernel)

private theorem nodesVerified : Interval nodesVerifiedTest 0 18 :=
(interval_append _ 0 9 18 (interval_append _ 0 4 9 (interval_append _ 0 2 4 (interval_append _ 0 1 2 nodesVerified00 nodesVerified01) (interval_append _ 2 3 4 nodesVerified02 nodesVerified03)) (interval_append _ 4 6 9 (interval_append _ 4 5 6 nodesVerified04 nodesVerified05) (interval_append _ 6 7 9 nodesVerified06 (interval_append _ 7 8 9 nodesVerified07 nodesVerified08)))) (interval_append _ 9 13 18 (interval_append _ 9 11 13 (interval_append _ 9 10 11 nodesVerified09 nodesVerified10) (interval_append _ 11 12 13 nodesVerified11 nodesVerified12)) (interval_append _ 13 15 18 (interval_append _ 13 14 15 nodesVerified13 nodesVerified14) (interval_append _ 15 16 18 nodesVerified15 (interval_append _ 16 17 18 nodesVerified16 nodesVerified17)))))

private def sideVerifiedTest : Nat → Bool := fun j => sideCheck (packets (Fin.ofNat 18 j))

private theorem sideVerified00 : Interval sideVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem sideVerified01 : Interval sideVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem sideVerified02 : Interval sideVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem sideVerified03 : Interval sideVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem sideVerified04 : Interval sideVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem sideVerified05 : Interval sideVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem sideVerified06 : Interval sideVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem sideVerified07 : Interval sideVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem sideVerified08 : Interval sideVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem sideVerified09 : Interval sideVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem sideVerified10 : Interval sideVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem sideVerified11 : Interval sideVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem sideVerified12 : Interval sideVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem sideVerified13 : Interval sideVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem sideVerified14 : Interval sideVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem sideVerified15 : Interval sideVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem sideVerified16 : Interval sideVerifiedTest 16 17 :=
  interval_of_check _ 16 1 (by decide +kernel)

private theorem sideVerified17 : Interval sideVerifiedTest 17 18 :=
  interval_of_check _ 17 1 (by decide +kernel)

private theorem sideVerified : Interval sideVerifiedTest 0 18 :=
(interval_append _ 0 9 18 (interval_append _ 0 4 9 (interval_append _ 0 2 4 (interval_append _ 0 1 2 sideVerified00 sideVerified01) (interval_append _ 2 3 4 sideVerified02 sideVerified03)) (interval_append _ 4 6 9 (interval_append _ 4 5 6 sideVerified04 sideVerified05) (interval_append _ 6 7 9 sideVerified06 (interval_append _ 7 8 9 sideVerified07 sideVerified08)))) (interval_append _ 9 13 18 (interval_append _ 9 11 13 (interval_append _ 9 10 11 sideVerified09 sideVerified10) (interval_append _ 11 12 13 sideVerified11 sideVerified12)) (interval_append _ 13 15 18 (interval_append _ 13 14 15 sideVerified13 sideVerified14) (interval_append _ 15 16 18 sideVerified15 (interval_append _ 16 17 18 sideVerified16 sideVerified17)))))

private def rowsVerifiedTest : Nat → Bool := fun j => rowCheck 29 (packets (Fin.ofNat 18 j))

private theorem rowsVerified00 : Interval rowsVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem rowsVerified01 : Interval rowsVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem rowsVerified02 : Interval rowsVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem rowsVerified03 : Interval rowsVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem rowsVerified04 : Interval rowsVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem rowsVerified05 : Interval rowsVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem rowsVerified06 : Interval rowsVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem rowsVerified07 : Interval rowsVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem rowsVerified08 : Interval rowsVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem rowsVerified09 : Interval rowsVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem rowsVerified10 : Interval rowsVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem rowsVerified11 : Interval rowsVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem rowsVerified12 : Interval rowsVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem rowsVerified13 : Interval rowsVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem rowsVerified14 : Interval rowsVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem rowsVerified15 : Interval rowsVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem rowsVerified16 : Interval rowsVerifiedTest 16 17 :=
  interval_of_check _ 16 1 (by decide +kernel)

private theorem rowsVerified17 : Interval rowsVerifiedTest 17 18 :=
  interval_of_check _ 17 1 (by decide +kernel)

private theorem rowsVerified : Interval rowsVerifiedTest 0 18 :=
(interval_append _ 0 9 18 (interval_append _ 0 4 9 (interval_append _ 0 2 4 (interval_append _ 0 1 2 rowsVerified00 rowsVerified01) (interval_append _ 2 3 4 rowsVerified02 rowsVerified03)) (interval_append _ 4 6 9 (interval_append _ 4 5 6 rowsVerified04 rowsVerified05) (interval_append _ 6 7 9 rowsVerified06 (interval_append _ 7 8 9 rowsVerified07 rowsVerified08)))) (interval_append _ 9 13 18 (interval_append _ 9 11 13 (interval_append _ 9 10 11 rowsVerified09 rowsVerified10) (interval_append _ 11 12 13 rowsVerified11 rowsVerified12)) (interval_append _ 13 15 18 (interval_append _ 13 14 15 rowsVerified13 rowsVerified14) (interval_append _ 15 16 18 rowsVerified15 (interval_append _ 16 17 18 rowsVerified16 rowsVerified17)))))

private def keysVerifiedTest : Nat → Bool := fun j => keysCheck 21816 29 (packets (Fin.ofNat 18 j)) j

private theorem keysVerified00 : Interval keysVerifiedTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)

private theorem keysVerified01 : Interval keysVerifiedTest 1 2 :=
  interval_of_check _ 1 1 (by decide +kernel)

private theorem keysVerified02 : Interval keysVerifiedTest 2 3 :=
  interval_of_check _ 2 1 (by decide +kernel)

private theorem keysVerified03 : Interval keysVerifiedTest 3 4 :=
  interval_of_check _ 3 1 (by decide +kernel)

private theorem keysVerified04 : Interval keysVerifiedTest 4 5 :=
  interval_of_check _ 4 1 (by decide +kernel)

private theorem keysVerified05 : Interval keysVerifiedTest 5 6 :=
  interval_of_check _ 5 1 (by decide +kernel)

private theorem keysVerified06 : Interval keysVerifiedTest 6 7 :=
  interval_of_check _ 6 1 (by decide +kernel)

private theorem keysVerified07 : Interval keysVerifiedTest 7 8 :=
  interval_of_check _ 7 1 (by decide +kernel)

private theorem keysVerified08 : Interval keysVerifiedTest 8 9 :=
  interval_of_check _ 8 1 (by decide +kernel)

private theorem keysVerified09 : Interval keysVerifiedTest 9 10 :=
  interval_of_check _ 9 1 (by decide +kernel)

private theorem keysVerified10 : Interval keysVerifiedTest 10 11 :=
  interval_of_check _ 10 1 (by decide +kernel)

private theorem keysVerified11 : Interval keysVerifiedTest 11 12 :=
  interval_of_check _ 11 1 (by decide +kernel)

private theorem keysVerified12 : Interval keysVerifiedTest 12 13 :=
  interval_of_check _ 12 1 (by decide +kernel)

private theorem keysVerified13 : Interval keysVerifiedTest 13 14 :=
  interval_of_check _ 13 1 (by decide +kernel)

private theorem keysVerified14 : Interval keysVerifiedTest 14 15 :=
  interval_of_check _ 14 1 (by decide +kernel)

private theorem keysVerified15 : Interval keysVerifiedTest 15 16 :=
  interval_of_check _ 15 1 (by decide +kernel)

private theorem keysVerified16 : Interval keysVerifiedTest 16 17 :=
  interval_of_check _ 16 1 (by decide +kernel)

private theorem keysVerified17 : Interval keysVerifiedTest 17 18 :=
  interval_of_check _ 17 1 (by decide +kernel)

private theorem keysVerified : Interval keysVerifiedTest 0 18 :=
(interval_append _ 0 9 18 (interval_append _ 0 4 9 (interval_append _ 0 2 4 (interval_append _ 0 1 2 keysVerified00 keysVerified01) (interval_append _ 2 3 4 keysVerified02 keysVerified03)) (interval_append _ 4 6 9 (interval_append _ 4 5 6 keysVerified04 keysVerified05) (interval_append _ 6 7 9 keysVerified06 (interval_append _ 7 8 9 keysVerified07 keysVerified08)))) (interval_append _ 9 13 18 (interval_append _ 9 11 13 (interval_append _ 9 10 11 keysVerified09 keysVerified10) (interval_append _ 11 12 13 keysVerified11 keysVerified12)) (interval_append _ 13 15 18 (interval_append _ 13 14 15 keysVerified13 keysVerified14) (interval_append _ 15 16 18 keysVerified15 (interval_append _ 16 17 18 keysVerified16 keysVerified17)))))

public theorem complete : Block 21816 21834 :=
  completeBlock 21816 29 packets metadataVerified nodesVerified sideVerified rowsVerified keysVerified

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0528
