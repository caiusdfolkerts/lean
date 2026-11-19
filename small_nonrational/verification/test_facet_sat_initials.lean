module
prelude
public import FacetSatCoverage
public import FacetSatGroups
public import FacetSatEdges
public meta import FacetSatInitials

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Papers.RationalityTen.FacetSatInitials.Tests

namespace Exact
def data : FacetSat.Data where
  count := 2
  embedding := ⟨1, 2⟩
  vertices := ⟨2, 15⟩
  faces := ⟨4, 0⟩
  kinds := ⟨1, 0⟩
  cellCodes := ⟨1, 0⟩
  ridgeMatrix := 0
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 2 else 0
def first : List (Fin data.count) := [facetIndex 0]
def second : List (Fin data.count) := [facetIndex 1]
def kind0 : List (Fin data.count) := [facetIndex 0, facetIndex 1]
theorem kind0_checked : FacetSat.Boundary.kindListCheck data.toData.kind 0 kind0 = true := by decide
def model (S : List (Fin data.count)) (i : Nat) : Prop :=
  if i = 1 then facetIndex 0 ∈ S else if i = 2 then facetIndex 1 ∈ S else
    SequentialCounter.reached (fun c => c ∈ S) kind0 2
theorem atom00001_eq (S : List (Fin data.count)) : model S 1 = (facetIndex 0 ∈ S) := rfl
theorem atom00002_eq (S : List (Fin data.count)) : model S 2 = (facetIndex 1 ∈ S) := rfl
theorem atom00003_eq (S : List (Fin data.count)) : model S 3 = SequentialCounter.reached (fun c => c ∈ S) kind0 2 := rfl

facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.Exact" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.Exact\",\"lower_only\":false,\"coverage\":false,\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"totalizer\"}],\"clauses\":[[-1,-2],[-3,1],[-3,2],[3]],\"rules\":[{\"tag\":\"incompatible\",\"a\":0,\"b\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"a\":0,\"b\":1,\"direction\":\"backward\",\"left_name\":\"first\",\"right_name\":\"second\",\"joined_name\":\"kind0\",\"full_literals\":[-3,1,false]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"a\":1,\"b\":0,\"direction\":\"backward\",\"left_name\":\"first\",\"right_name\":\"second\",\"joined_name\":\"kind0\",\"full_literals\":[-3,false,2]},{\"tag\":\"quota_lower\",\"kind\":0,\"quota\":2}]}" "p cnf 3 4\n-1 -2 0\n-3 1 0\n-3 2 0\n3 0\n" "5 0 4 2 3 1 0\n"

#print axioms boundary_unsat
end Exact

namespace Lower
def data : FacetSat.Data where
  count := 2
  embedding := ⟨1, 2⟩
  vertices := ⟨2, 15⟩
  faces := ⟨4, 0⟩
  kinds := ⟨1, 0⟩
  cellCodes := ⟨1, 0⟩
  ridgeMatrix := 0
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 2 else 0
def first : List (Fin data.count) := [facetIndex 0]
def second : List (Fin data.count) := [facetIndex 1]
def kind0 : List (Fin data.count) := [facetIndex 0, facetIndex 1]
theorem kind0_checked : FacetSat.Boundary.kindListCheck data.toData.kind 0 kind0 = true := by decide
def model (S : List (Fin data.count)) (i : Nat) : Prop :=
  if i = 1 then facetIndex 0 ∈ S else if i = 2 then facetIndex 1 ∈ S else
    SequentialCounter.reached (fun c => c ∈ S) kind0 2
theorem atom00001_eq (S : List (Fin data.count)) : model S 1 = (facetIndex 0 ∈ S) := rfl
theorem atom00002_eq (S : List (Fin data.count)) : model S 2 = (facetIndex 1 ∈ S) := rfl
theorem atom00003_eq (S : List (Fin data.count)) : model S 3 = SequentialCounter.reached (fun c => c ∈ S) kind0 2 := rfl

facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.Lower" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.Lower\",\"lower_only\":true,\"coverage\":false,\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"totalizer\"}],\"clauses\":[[-1,-2],[-3,1],[-3,2],[3]],\"rules\":[{\"tag\":\"incompatible\",\"a\":0,\"b\":1},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"a\":0,\"b\":1,\"direction\":\"backward\",\"left_name\":\"first\",\"right_name\":\"second\",\"joined_name\":\"kind0\",\"full_literals\":[-3,1,false]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"a\":1,\"b\":0,\"direction\":\"backward\",\"left_name\":\"first\",\"right_name\":\"second\",\"joined_name\":\"kind0\",\"full_literals\":[-3,false,2]},{\"tag\":\"quota_lower\",\"kind\":0,\"quota\":2}]}" "p cnf 3 4\n-1 -2 0\n-3 1 0\n-3 2 0\n3 0\n" "5 0 4 2 3 1 0\n"

#print axioms boundary_unsat
end Lower

namespace Coverage
def data : FacetSat.Data where
  count := 2
  embedding := ⟨1, 2⟩
  vertices := ⟨2, 15⟩
  faces := ⟨4, 0⟩
  kinds := ⟨1, 0⟩
  cellCodes := ⟨1, 0⟩
  ridgeMatrix := 0
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 1 else 0
def first : List (Fin data.count) := [facetIndex 0]
def second : List (Fin data.count) := [facetIndex 1]
def kind0 : List (Fin data.count) := [facetIndex 0, facetIndex 1]
theorem kind0_checked : FacetSat.Boundary.kindListCheck data.toData.kind 0 kind0 = true := by decide
def model (S : List (Fin data.count)) (i : Nat) : Prop :=
  if i = 1 then facetIndex 0 ∈ S else if i = 2 then facetIndex 1 ∈ S else
    SequentialCounter.reached (fun c => c ∈ S) kind0 1
theorem atom00001_eq (S : List (Fin data.count)) : model S 1 = (facetIndex 0 ∈ S) := rfl
theorem atom00002_eq (S : List (Fin data.count)) : model S 2 = (facetIndex 1 ∈ S) := rfl
theorem atom00003_eq (S : List (Fin data.count)) : model S 3 = SequentialCounter.reached (fun c => c ∈ S) kind0 1 := rfl
def leafCount : Nat := 2
def leaf0000 : List (Fin data.count) := first
def leaf0001 : List (Fin data.count) := second
def leaves (j : Fin leafCount) : List (Fin data.count) := if j.val = 0 then leaf0000 else leaf0001
theorem leaf0000_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true := by decide
theorem leaf0001_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true := by decide

facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.Coverage" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.Coverage\",\"lower_only\":false,\"coverage\":true,\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"totalizer\"}],\"clauses\":[[-1],[-2],[-3,1,2],[3]],\"rules\":[{\"tag\":\"block\",\"leaf\":0,\"vertices\":[0]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[1]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"a\":0,\"b\":0,\"direction\":\"backward\",\"left_name\":\"first\",\"right_name\":\"second\",\"joined_name\":\"kind0\",\"full_literals\":[-3,1,2]},{\"tag\":\"quota_lower\",\"kind\":0,\"quota\":1}]}" "p cnf 3 4\n-1 0\n-2 0\n-3 1 2 0\n3 0\n" "5 0 1 2 4 3 0\n"

#print axioms boundary_unsat
end Coverage

end Papers.RationalityTen.FacetSatInitials.Tests

/- A malformed semantic witness must be rejected by the kernel.  Restoring
   the elaborator state keeps rejected test declarations out of the module. -/
open Lean Elab Command in
run_cmd do
  let saved ← get
  let rejected ← try
    elabCommand (← `(facet_initials% "Papers.RationalityTen.FacetSatInitials.Tests.Exact" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.Exact\",\"lower_only\":false,\"coverage\":false,\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1}],\"clauses\":[[-1,-2]],\"rules\":[{\"tag\":\"incompatible\",\"a\":0,\"b\":0}]}"))
    pure (← get).messages.hasErrors
  catch _ => pure true
  set saved
  unless rejected do throwError "accepted a false incompatibility witness"

namespace Papers.RationalityTen.FacetSatInitials.Tests.GroupedCoverage
def data : FacetSat.Data := Papers.RationalityTen.FacetSatInitials.Tests.Exact.data
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 1 else 0
def grouping0 : FacetSat.Grouping data.count where
  count := 2
  members := fun i => if i = 0 then [facetIndex 0] else if i = 1 then [facetIndex 1] else []
  color := Fin.val
def groupKind0 : List Nat := List.range grouping0.count
def first : List Nat := [0]
def second : List Nat := [1]
theorem grouping0_checked : grouping0.check data.toData.kind data.toData.relation 0 = true := by decide
def model (S : List (Fin data.count)) (i : Nat) : Prop :=
  if i = 1 then facetIndex 0 ∈ S else if i = 2 then facetIndex 1 ∈ S else
  if i = 3 then grouping0.selected S 0 else if i = 4 then grouping0.selected S 1 else
    SequentialCounter.reached (grouping0.selected S) groupKind0 1
theorem atom00001_eq (S : List (Fin data.count)) : model S 1 = (facetIndex 0 ∈ S) := rfl
theorem atom00002_eq (S : List (Fin data.count)) : model S 2 = (facetIndex 1 ∈ S) := rfl
theorem atom00003_eq (S : List (Fin data.count)) : model S 3 = grouping0.selected S 0 := rfl
theorem atom00004_eq (S : List (Fin data.count)) : model S 4 = grouping0.selected S 1 := rfl
theorem atom00005_eq (S : List (Fin data.count)) : model S 5 = SequentialCounter.reached (grouping0.selected S) groupKind0 1 := rfl
def leafCount : Nat := 2
def leaf0000 : List (Fin data.count) := [facetIndex 0]
def leaf0001 : List (Fin data.count) := [facetIndex 1]
def leaves (j : Fin leafCount) : List (Fin data.count) := if j.val = 0 then leaf0000 else leaf0001
theorem leaf0000_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true := by decide
theorem leaf0001_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true := by decide
facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.GroupedCoverage" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.GroupedCoverage\",\"lower_only\":false,\"coverage\":true,\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"group\",\"kind\":0,\"index\":0},{\"tag\":\"group\",\"kind\":0,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":0}],\"clauses\":[[-1],[-2],[-3,1],[-4,2],[-1,3],[-2,4],[-5,3,4],[5]],\"rules\":[{\"tag\":\"block\",\"leaf\":0,\"vertices\":[0]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[1]},{\"tag\":\"group_or\",\"kind\":0,\"index\":0,\"members\":[0]},{\"tag\":\"group_or\",\"kind\":0,\"index\":1,\"members\":[1]},{\"tag\":\"group_take\",\"kind\":0,\"index\":0,\"member\":0},{\"tag\":\"group_take\",\"kind\":0,\"index\":1,\"member\":1},{\"tag\":\"merge\",\"grouped\":true,\"kind\":0,\"left\":[0],\"right\":[1],\"a\":0,\"b\":0,\"direction\":\"backward\",\"left_name\":\"first\",\"right_name\":\"second\",\"joined_name\":\"groupKind0\",\"full_literals\":[-5,3,4]},{\"tag\":\"quota_lower\",\"kind\":0,\"quota\":1,\"grouped\":true}]}" "p cnf 5 8\n-1 0\n-2 0\n-3 1 0\n-4 2 0\n-1 3 0\n-2 4 0\n-5 3 4 0\n5 0\n" "9 0 1 2 3 4 8 7 0\n"
#print axioms boundary_unsat
end Papers.RationalityTen.FacetSatInitials.Tests.GroupedCoverage

namespace Papers.RationalityTen.FacetSatInitials.Tests.GroupedEmpty
def data : FacetSat.Data := Papers.RationalityTen.FacetSatInitials.Tests.Exact.data
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 2 else 0
def grouping0 : FacetSat.Grouping data.count where
  count := 1
  members := fun _ => [facetIndex 0, facetIndex 1]
  color := fun _ => 0
def groupKind0 : List Nat := List.range grouping0.count
theorem grouping0_checked : grouping0.check data.toData.kind data.toData.relation 0 = true := by decide
def model (_ : List (Fin data.count)) (_ : Nat) : Prop := False
facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.GroupedEmpty" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.GroupedEmpty\",\"lower_only\":false,\"coverage\":false,\"atoms\":[],\"clauses\":[[]],\"rules\":[{\"tag\":\"quota_lower\",\"kind\":0,\"quota\":2,\"grouped\":true}]}" "p cnf 0 1\n0\n" "2 0 1 0\n"
#print axioms boundary_unsat
end Papers.RationalityTen.FacetSatInitials.Tests.GroupedEmpty

namespace Papers.RationalityTen.FacetSatInitials.Tests.EdgeCoverage
def data : FacetSat.Data := Papers.RationalityTen.FacetSatInitials.Tests.Exact.data
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 1 else 0
def edgeCount : Nat := 1
def requiredEdges : Nat := 1
def edgeRows (_ : Fin edgeCount) : Nat := 1
def edgeIndex (_ : Nat) : Fin edgeCount := ⟨0, by decide⟩
def edgeOwners_0 : List (Fin data.count) := [facetIndex 0]
theorem edge_0_required : requiredEdges.testBit (edgeIndex 0).val = true := by decide
theorem edge_0_owners_checked : FacetSat.EdgeCover.ownersCheck (edgeRows (edgeIndex 0)) edgeOwners_0 = true := by decide
def model (S : List (Fin data.count)) (_ : Nat) : Prop := facetIndex 0 ∈ S
def leafCount : Nat := 1
def leaf0000 : List (Fin data.count) := [facetIndex 0]
def leaves (_ : Fin leafCount) : List (Fin data.count) := leaf0000
theorem leaf0000_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true := by decide
facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.EdgeCoverage" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.EdgeCoverage\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"atoms\":[{\"tag\":\"facet\",\"index\":0}],\"clauses\":[[1],[-1]],\"rules\":[{\"tag\":\"edge\",\"edge\":0,\"owners\":[0]},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[0]}]}" "p cnf 1 2\n1 0\n-1 0\n" "3 0 2 1 0\n"
#print axioms boundary_unsat
end Papers.RationalityTen.FacetSatInitials.Tests.EdgeCoverage

namespace Papers.RationalityTen.FacetSatInitials.Tests.EmptyEdge
def data : FacetSat.Data := Papers.RationalityTen.FacetSatInitials.Tests.Exact.data
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 1 else 0
def edgeCount : Nat := 1
def requiredEdges : Nat := 1
def edgeRows (_ : Fin edgeCount) : Nat := 0
def edgeIndex (_ : Nat) : Fin edgeCount := ⟨0, by decide⟩
def edgeOwners_0 : List (Fin data.count) := []
theorem edge_0_required : requiredEdges.testBit (edgeIndex 0).val = true := by decide
theorem edge_0_owners_checked : FacetSat.EdgeCover.ownersCheck (edgeRows (edgeIndex 0)) edgeOwners_0 = true := by decide
def model (S : List (Fin data.count)) (_ : Nat) : Prop := facetIndex 0 ∈ S
facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.EmptyEdge" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.EmptyEdge\",\"lower_only\":true,\"coverage\":false,\"edge_cover\":true,\"atoms\":[],\"clauses\":[[]],\"rules\":[{\"tag\":\"edge\",\"edge\":0,\"owners\":[]}]}" "p cnf 0 1\n0\n" "2 0 1 0\n"
#print axioms boundary_unsat
end Papers.RationalityTen.FacetSatInitials.Tests.EmptyEdge

/- A one-class totalizer root is the class proposition itself. -/
namespace Papers.RationalityTen.FacetSatInitials.Tests.GroupedSingleton
def data : FacetSat.Data := Papers.RationalityTen.FacetSatInitials.Tests.Exact.data
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (j : Nat) : Nat := if j = 0 then 1 else 0
def grouping0 : FacetSat.Grouping data.count where
  count := 1
  members := fun _ => [facetIndex 0, facetIndex 1]
  color := fun _ => 0
def groupKind0 : List Nat := List.range grouping0.count
def first : List Nat := [0]
def second : List Nat := [1]
theorem grouping0_checked : grouping0.check data.toData.kind data.toData.relation 0 = true := by decide
def model (S : List (Fin data.count)) (i : Nat) : Prop :=
  if i = 1 then facetIndex 0 ∈ S else if i = 2 then facetIndex 1 ∈ S else
  if i = 3 then grouping0.selected S 0 else if i = 4 then grouping0.selected S 1 else
    SequentialCounter.reached (grouping0.selected S) groupKind0 1
theorem atom00001_eq (S : List (Fin data.count)) : model S 1 = (facetIndex 0 ∈ S) := rfl
theorem atom00002_eq (S : List (Fin data.count)) : model S 2 = (facetIndex 1 ∈ S) := rfl
theorem atom00003_eq (S : List (Fin data.count)) : model S 3 = grouping0.selected S 0 := rfl
theorem atom00004_eq (S : List (Fin data.count)) : model S 4 = grouping0.selected S 1 := rfl
theorem atom00005_eq (S : List (Fin data.count)) : model S 5 = SequentialCounter.reached (grouping0.selected S) groupKind0 1 := rfl
def leafCount : Nat := 2
def leaf0000 : List (Fin data.count) := [facetIndex 0]
def leaf0001 : List (Fin data.count) := [facetIndex 1]
def leaves (j : Fin leafCount) : List (Fin data.count) := if j.val = 0 then leaf0000 else leaf0001
theorem leaf0000_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true := by decide
theorem leaf0001_checked : FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true := by decide
facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.GroupedSingleton" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.GroupedSingleton\",\"lower_only\":false,\"coverage\":true,\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"group\",\"kind\":0,\"index\":0}],\"clauses\":[[-1],[-2],[-3,1,2],[-1,3],[-2,3],[3]],\"rules\":[{\"tag\":\"block\",\"leaf\":0,\"vertices\":[0]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[1]},{\"tag\":\"group_or\",\"kind\":0,\"index\":0,\"members\":[0,1]},{\"tag\":\"group_take\",\"kind\":0,\"index\":0,\"member\":0},{\"tag\":\"group_take\",\"kind\":0,\"index\":0,\"member\":1},{\"tag\":\"quota_lower\",\"kind\":0,\"quota\":1,\"grouped\":true}]}" "p cnf 3 6\n-1 0\n-2 0\n-3 1 2 0\n-1 3 0\n-2 3 0\n3 0\n" "7 0 1 2 6 3 0\n"
#print axioms boundary_unsat
end Papers.RationalityTen.FacetSatInitials.Tests.GroupedSingleton

namespace Papers.RationalityTen.FacetSatInitials.Tests.SingletonUpper
def data : FacetSat.Data where
  count := 2
  embedding := ⟨1, 2⟩
  vertices := ⟨2, 15⟩
  faces := ⟨4, 0⟩
  kinds := ⟨1, 2⟩
  cellCodes := ⟨1, 0⟩
  ridgeMatrix := 0
def facetIndex (i : Nat) : Fin data.count := ⟨i % 2, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 := ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def requirements (_ : Nat) : Nat := 0
def kind0 : List (Fin data.count) := [facetIndex 0]
theorem kind0_checked : FacetSat.Boundary.kindListCheck data.toData.kind 0 kind0 = true := by decide
def edgeCount : Nat := 1
def requiredEdges : Nat := 1
def edgeRows (_ : Fin edgeCount) : Nat := 1
def edgeIndex (_ : Nat) : Fin edgeCount := ⟨0, by decide⟩
def edgeOwners_0 : List (Fin data.count) := [facetIndex 0]
theorem edge_0_required : requiredEdges.testBit (edgeIndex 0).val = true := by decide
theorem edge_0_owners_checked : FacetSat.EdgeCover.ownersCheck (edgeRows (edgeIndex 0)) edgeOwners_0 = true := by decide
def model (S : List (Fin data.count)) (_ : Nat) : Prop := facetIndex 0 ∈ S
facet_refute% "Papers.RationalityTen.FacetSatInitials.Tests.SingletonUpper" "{\"namespace\":\"Papers.RationalityTen.FacetSatInitials.Tests.SingletonUpper\",\"lower_only\":false,\"coverage\":false,\"edge_cover\":true,\"atoms\":[{\"tag\":\"facet\",\"index\":0}],\"clauses\":[[1],[-1]],\"rules\":[{\"tag\":\"edge\",\"edge\":0,\"owners\":[0]},{\"tag\":\"quota_upper\",\"kind\":0,\"quota\":0}]}" "p cnf 1 2\n1 0\n-1 0\n" "3 0 1 2 0\n"
#print axioms boundary_unsat
end Papers.RationalityTen.FacetSatInitials.Tests.SingletonUpper
