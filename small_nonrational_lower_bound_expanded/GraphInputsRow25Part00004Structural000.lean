module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow25Part00004Data
public import GraphInputsRow25Part00004Frames
public import GraphInputsRow25Part00004Leaves
public import GraphInputsRow25Part00004Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 4), (certNat% 14), 7494552729897926656, (certNat% 15), (certNat% 16), (certNat% 17)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 11544872091648, 1154047404513689600, (certNat% 19), (certNat% 20), (certNat% 4)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), 1297036692682702848]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 12644383719424, (certNat% 27), (certNat% 28), 1297036692682702848]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), 1297046588287352832, (certNat% 31), (certNat% 32), (certNat% 33), 549755813888]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 2594354860342116352, (certNat% 4), (certNat% 36), (certNat% 3)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41), (certNat% 42), (certNat% 17)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 4), 5044042577771233280, (certNat% 45), 1729382256910270464, (certNat% 46)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), 8503921996382339072, (certNat% 49), (certNat% 50), 576465702253232128, (certNat% 51), (certNat% 52)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c4
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record031_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338cd32cc723c4f2aaa68da8e966399564d8ce2b85e0fbc1e85e1d46d1cc729c6699366394e725594e5c56354d70d3362d4b4ad8751d1743da8d6338e9354cd38cd33a2ccb8ae1b26c5b0ed4731d2729c6745c3723c4faa1542a8560b81ec86a1c4551a26292a61951525454550b41d30ca314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da6db69b4934d349269a4d34da4924934d26d2492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 80)]))
 (.branch 2
 (.leaf ([(facetIndex 61), (facetIndex 66)]))
 (.leaf ([(facetIndex 84), (facetIndex 87)]))))
 (.branch 4
 (.leaf ([(facetIndex 50), (facetIndex 71), (facetIndex 76)]))
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 52)]))
 (.leaf ([(facetIndex 85), (facetIndex 88)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 90), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 62), (facetIndex 64), (facetIndex 69)]))
 (.leaf ([(facetIndex 93), (facetIndex 94), (facetIndex 95)]))))
 (.branch 10
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 98)]))
 (.branch 11
 (.leaf ([(facetIndex 47)]))
 (.leaf ([(facetIndex 89)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "999888066b52052000000030000307001070710000000040300a4z2e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0013 : List Nat := [7]
def grouped3_0014 : List Nat := [7, 8]
def grouped3_0015 : List Nat := [8]
def grouped3_0016 : List Nat := [9]
def grouped3_0017 : List Nat := [9, 10, 11]
def grouped3_0018 : List Nat := [10, 11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013" "{\"ridges\":[[9,194],[21,769],[21,784],[23,769],[23,800],[37,193],[44,194],[48,194],[51,194],[62,780],[64,564],[65,784],[68,800],[69,312],[73,784],[74,800],[75,784],[75,800],[76,720],[77,769],[77,784],[78,480],[79,769],[79,800],[80,960],[90,216],[95,780],[96,780],[97,564],[98,312]],\"owners\":[[37,193,[71,76,78,80],[9,44,48,51,61,66]],[9,194,[84,87,90],[37,44,48,51]],[44,194,[87],[9,37,48,51,84,90]],[48,194,[84,87],[9,37,44,51,90]],[51,194,[84,90],[9,37,44,48,87]],[21,769,[23,62,68,74,79,80],[65,73,77]],[23,769,[21,62,65,73,77,80],[68,74,79]],[77,769,[23,62,68,74,79],[21,65,73,80]],[79,769,[21,62,65,73,77],[23,68,74,80]],[21,784,[95,97,98],[65,73,75,77]],[65,784,[98],[21,73,75,77,95,97]],[73,784,[97],[21,65,75,77,95,98]],[75,784,[95],[21,65,73,77,97,98]],[77,784,[95,97,98],[21,65,73,75]],[23,800,[96,97,98],[68,74,75,79]],[68,800,[98],[23,74,75,79,96,97]],[74,800,[97],[23,68,75,79,96,98]],[75,800,[96],[23,68,74,79,97,98]],[79,800,[96,97,98],[23,68,74,75]],[62,780,[95,96],[]],[95,780,[62,96],[]],[96,780,[62,95],[]],[64,564,[94,97],[]],[97,564,[64,94],[]],[69,312,[93,98],[]],[98,312,[69,93],[]],[90,216,[71],[]],[76,720,[],[]],[78,480,[],[]],[80,960,[],[]]],\"edges\":[[39,[9,37,44,48,51,61,66,71,76,78,80,84,87,90]],[44,[21,23,62,65,68,73,74,75,77,79,80,95,96,97,98]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,15,19,21,23],[-1,24,25,26],[-5,25],[-6,24,25],[-7,24,26],[-2,3,9,13,17,22,23],[-3,2,9,11,16,20,23],[-20,3,9,13,17,22],[-22,2,9,11,16,20],[-2,29,31,32],[-11,32],[-16,31],[-18,29],[-20,29,31,32],[-3,30,31,32],[-13,32],[-17,31],[-18,30],[-22,30,31,32],[-9,29,30],[-29,9,30],[-30,9,29],[-10,28,31],[-31,10,28],[-14,27,32],[-32,14,27],[-26,15],[-19],[-21],[-23],[-8,33],[-12,33],[-24,34],[-25,34],[-15,35],[-36,9,10,14],[-9,36],[-10,36],[-14,36],[-27,37],[-28,37],[-29,37],[-30,38],[-31,38],[-32,38],[-34,39],[-33,39],[-39,40],[-35,41],[-41,42],[-40,42],[-43,36,37],[-37,43],[-36,43],[-36,-37,44],[-43,45],[-44,46],[-38,47],[-45,-47,48],[-46,48],[-42,-48,49],[-49],[1,4,5,6,7,8,12,15,19,21,23,24,25,26],[2,3,9,11,13,16,17,18,20,22,23,29,30,31,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":193,\"a\":37,\"owners\":[71,76,78,80]},{\"tag\":\"mate\",\"ridge\":194,\"a\":9,\"owners\":[84,87,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":194,\"a\":51,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":769,\"a\":21,\"owners\":[23,62,68,74,79,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":23,\"owners\":[21,62,65,73,77,80]},{\"tag\":\"mate\",\"ridge\":769,\"a\":77,\"owners\":[23,62,68,74,79]},{\"tag\":\"mate\",\"ridge\":769,\"a\":79,\"owners\":[21,62,65,73,77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":21,\"owners\":[95,97,98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":65,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":784,\"a\":73,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":784,\"a\":75,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":784,\"a\":77,\"owners\":[95,97,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":23,\"owners\":[96,97,98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":68,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":800,\"a\":74,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":800,\"a\":75,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":79,\"owners\":[96,97,98]},{\"tag\":\"mate\",\"ridge\":780,\"a\":62,\"owners\":[95,96]},{\"tag\":\"mate\",\"ridge\":780,\"a\":95,\"owners\":[62,96]},{\"tag\":\"mate\",\"ridge\":780,\"a\":96,\"owners\":[62,95]},{\"tag\":\"mate\",\"ridge\":564,\"a\":64,\"owners\":[94,97]},{\"tag\":\"mate\",\"ridge\":564,\"a\":97,\"owners\":[64,94]},{\"tag\":\"mate\",\"ridge\":312,\"a\":69,\"owners\":[93,98]},{\"tag\":\"mate\",\"ridge\":312,\"a\":98,\"owners\":[69,93]},{\"tag\":\"mate\",\"ridge\":216,\"a\":90,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":720,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":80,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-8,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-12,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-24,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-25,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-15,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[62,64,69],\"full_literals\":[-36,9,10,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":62,\"full_literals\":[-9,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":64,\"full_literals\":[-10,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-14,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":93,\"full_literals\":[-27,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-28,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":95,\"full_literals\":[-29,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-30,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":97,\"full_literals\":[-31,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-32,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0012\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[9,37,44,48,51,61,66,71,76,78,80,84,87,90]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[21,23,62,65,68,73,74,75,77,79,80,95,96,97,98]}]}"
  "65 1 4 5 6 7 8 12 15 24 25 26 0 28 29 30 63 0\n66 2 3 9 11 13 16 17 18 20 22 29 30 31 32 0 30 64 0\n67 42 0 30 29 28 50 51 49 48 35 46 47 1 27 33 34 31 32 5 2 3 4 65 0\n68 -48 0 67 62 61 0\n69 -46 0 68 60 0\n70 -44 0 69 57 0\n71 43 0 30 53 54 40 41 42 37 38 39 26 24 10 13 22 11 16 12 17 14 7 9 66 0\n72 45 0 71 56 0\n73 -47 0 72 68 59 0\n74 -38 0 73 58 0\n75 -30 0 74 43 0\n76 -31 0 74 44 0\n77 -32 0 74 45 0\n78 -3 0 75 76 77 15 0\n79 -18 0 75 18 0\n80 -22 0 75 76 77 19 0\n81 -16 0 76 12 0\n82 -17 0 76 17 0\n83 -11 0 77 11 0\n84 -13 0 77 16 0\n85 37 0 71 77 76 75 40 41 42 52 25 23 20 36 0\n86 -36 0 85 70 55 0\n87 -9 0 86 37 0\n88 -29 0 87 75 21 0\n89 -2 0 87 78 84 82 80 30 6 0\n90 20 0 87 89 78 84 81 82 79 83 80 88 75 76 77 66 0\n91 0 90 87 78 84 82 80 8 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b931ca71d2ca96aa98e6558d6c3a8e53a2e1b91e2783ef0761b8791747295a719a6745b16a5994e5c5695554d5c368d5346d8751d2743de0dc3c8ea358ce364d5334f0ba2d4b8ad2b1ac9b0ef07a1d4789ca745c570de0f43c8f13e2c468c6198960b81ec26294668531625194958342d0754330c6344c9342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6da69b69249b6da69b49269a49a49269b49249a4924d2492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 71), (facetIndex 77), (facetIndex 82)]))
 (.leaf ([(facetIndex 57), (facetIndex 79), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 81), (facetIndex 85)]))
 (.branch 4
 (.leaf ([(facetIndex 56), (facetIndex 83)]))
 (.leaf ([(facetIndex 65), (facetIndex 98)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 69), (facetIndex 100)]))
 (.leaf ([(facetIndex 49), (facetIndex 101)])))
 (.branch 8
 (.leaf ([(facetIndex 97), (facetIndex 103)]))
 (.branch 9
 (.leaf ([(facetIndex 42), (facetIndex 92), (facetIndex 99)]))
 (.leaf ([(facetIndex 76), (facetIndex 91), (facetIndex 93), (facetIndex 95), (facetIndex 102)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "79658470909890000021302010090000005000400000201300000060000008z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9]
def grouped3_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024" "{\"ridges\":[[20,641],[20,644],[23,769],[23,776],[41,641],[41,644],[50,769],[50,776],[56,674],[57,802],[59,898],[66,641],[66,644],[67,769],[67,776],[70,641],[71,788],[74,641],[74,644],[75,641],[75,644],[76,836],[77,664],[78,769],[78,776],[80,776],[82,912],[83,736],[84,864],[85,960],[92,650],[97,674],[99,802],[101,664],[102,788],[103,736]],\"owners\":[[20,641,[49,56,59,77,82,83,85],[41,66,70,74,75]],[41,641,[77,82,83,85],[20,49,56,59,66,70,74,75]],[66,641,[56,59,82,83,85],[20,41,49,70,74,75,77]],[70,641,[49,56,59,83,85],[20,41,66,74,75,77,82]],[74,641,[49,59,77,82,85],[20,41,56,66,70,75,83]],[75,641,[49,56,59,77,82],[20,41,66,70,74,83,85]],[20,644,[92,97,101,103],[41,66,70,74,75]],[41,644,[101,103],[20,66,70,74,75,92,97]],[66,644,[97,103],[20,41,70,74,75,92,101]],[74,644,[92,101],[20,41,66,70,75,97,103]],[75,644,[92,97,101],[20,41,66,70,74,103]],[23,769,[42,57,59,71,76,82,84,85],[50,67,78,80]],[50,769,[71,76,82,84,85],[23,42,57,59,67,78,80]],[67,769,[57,59,82,84,85],[23,42,50,71,76,78,80]],[78,769,[42,57,59,76,84,85],[23,50,67,71,80,82]],[23,776,[93,99,102],[50,67,78,80]],[50,776,[102],[23,67,78,80,93,99]],[67,776,[99],[23,50,78,80,93,102]],[78,776,[93,99],[23,50,67,80,102]],[80,776,[93,102],[23,50,67,78,99]],[92,650,[49],[]],[56,674,[97],[]],[97,674,[56],[]],[57,802,[99],[]],[99,802,[57],[]],[59,898,[],[]],[71,788,[102],[]],[102,788,[71],[]],[76,836,[],[]],[77,664,[101],[]],[101,664,[77],[]],[82,912,[],[]],[83,736,[103],[]],[103,736,[83],[]],[84,864,[],[]],[85,960,[],[]]],\"edges\":[[43,[20,41,49,56,59,66,70,74,75,77,82,83,85,92,97,101,103]],[44,[23,42,50,57,59,67,71,76,78,80,82,84,85,93,99,102]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,-4],[-19,-5],[-25,-5],[-1,5,7,9,17,20,21,23],[-3,17,20,21,23],[-10,7,9,20,21,23],[-12,5,7,9,21,23],[-14,5,9,17,20,23],[-15,5,7,9,17,20],[-1,24,26,28,30],[-3,28,30],[-10,26,30],[-14,24,28],[-15,24,26,28],[-2,4,8,9,13,16,20,22,23],[-6,13,16,20,22,23],[-11,8,9,20,22,23],[-18,4,8,9,16,22,23],[-2,25,27,29],[-6,29],[-11,27],[-18,25,27],[-19,25,29],[-24,5],[-7,26],[-26,7],[-8,27],[-27,8],[-9],[-13,29],[-29,13],[-16],[-17,28],[-28,17],[-20],[-21,30],[-30,21],[-22],[-23],[-13,31],[-17,31],[-8,32],[-7,33],[-21,33],[-5,34],[-28,34],[-26,35],[-30,35],[-4,36],[-27,36],[-25,37],[-29,37],[-32,38],[-31,38],[-33,39],[-39,40],[-40,41],[-38,41],[-34,42],[-37,43],[-36,43],[-43,44],[-35,-43,45],[-45,46],[-42,-44,46],[-41,-46,47],[-47],[1,3,5,7,9,10,12,14,15,17,20,21,23,24,26,28,30],[2,4,6,8,9,11,13,16,18,19,20,22,23,25,27,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":49},{\"tag\":\"incompatible\",\"a\":93,\"b\":49},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[49,56,59,77,82,83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":41,\"owners\":[77,82,83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[56,59,82,83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[49,56,59,83,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":74,\"owners\":[49,59,77,82,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":75,\"owners\":[49,56,59,77,82]},{\"tag\":\"mate\",\"ridge\":644,\"a\":20,\"owners\":[92,97,101,103]},{\"tag\":\"mate\",\"ridge\":644,\"a\":41,\"owners\":[101,103]},{\"tag\":\"mate\",\"ridge\":644,\"a\":66,\"owners\":[97,103]},{\"tag\":\"mate\",\"ridge\":644,\"a\":74,\"owners\":[92,101]},{\"tag\":\"mate\",\"ridge\":644,\"a\":75,\"owners\":[92,97,101]},{\"tag\":\"mate\",\"ridge\":769,\"a\":23,\"owners\":[42,57,59,71,76,82,84,85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":50,\"owners\":[71,76,82,84,85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":67,\"owners\":[57,59,82,84,85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":78,\"owners\":[42,57,59,76,84,85]},{\"tag\":\"mate\",\"ridge\":776,\"a\":23,\"owners\":[93,99,102]},{\"tag\":\"mate\",\"ridge\":776,\"a\":50,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":776,\"a\":67,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":776,\"a\":78,\"owners\":[93,99]},{\"tag\":\"mate\",\"ridge\":776,\"a\":80,\"owners\":[93,102]},{\"tag\":\"mate\",\"ridge\":650,\"a\":92,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":674,\"a\":56,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":674,\"a\":97,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":802,\"a\":57,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":802,\"a\":99,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":898,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":788,\"a\":71,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":788,\"a\":102,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":836,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":77,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":664,\"a\":101,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":912,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":83,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":736,\"a\":103,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":864,\"a\":84,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":960,\"a\":85,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":71,\"full_literals\":[-13,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":77,\"full_literals\":[-17,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-8,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-7,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-21,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":49,\"full_literals\":[-5,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-28,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":97,\"full_literals\":[-26,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":103,\"full_literals\":[-30,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":42,\"full_literals\":[-4,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":99,\"full_literals\":[-27,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":102,\"full_literals\":[-29,37]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-41,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,41,49,56,59,66,70,74,75,77,82,83,85,92,97,101,103]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[23,42,50,57,59,67,71,76,78,80,82,84,85,93,99,102]}]}"
  "70 1 3 5 7 10 12 14 15 17 21 24 26 28 30 0 29 35 39 68 0\n71 2 4 6 8 11 13 18 19 25 27 29 0 29 32 35 38 39 69 0\n72 5 41 0 39 35 29 57 56 55 44 37 43 26 6 58 54 41 34 5 24 8 4 7 9 70 0\n73 41 0 35 39 38 32 29 58 53 54 42 40 17 28 16 31 72 1 2 3 15 18 71 0\n74 -46 0 73 67 66 0\n75 -45 0 74 64 0\n76 43 0 60 61 51 52 49 50 19 22 23 20 30 21 27 71 0\n77 44 0 76 62 0\n78 -35 0 76 75 63 0\n79 -42 0 77 74 65 0\n80 -26 0 78 47 0\n81 -30 0 78 48 0\n82 -34 0 79 59 0\n83 -10 0 80 81 12 0\n84 -7 0 80 25 0\n85 -21 0 81 36 0\n86 -5 0 82 45 0\n87 -28 0 82 46 0\n88 -24 0 86 24 0\n89 -12 0 86 84 29 85 39 7 0\n90 -3 0 87 81 11 0\n91 -17 0 87 33 0\n92 -14 0 87 88 13 0\n93 -1 0 87 80 88 81 10 0\n94 -15 0 87 80 88 14 0\n95 0 89 92 93 90 86 83 84 94 91 85 88 80 87 81 70 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record024_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce3c4e5334ad32cc723c4f2b2c695a36a3ad1ac6a9b16a5a362db0e538ce8b86e8791e2783ee45d1cc6b1564d94e78571725a9715a55958d5352d4cd4b46d4749d0f6a3c4e9354cd38ccb352ccb1ad1b26c5bc1e8751e2729c6785d1725c3743c8f07d4ca4a320ea8631a261382e525190e5453150d1342d30c930cc4b0ac1b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6da6da69349b4926da6db4d34db6db6924d369a49249269249b492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 56), (facetIndex 58), (facetIndex 67)]))
 (.leaf ([(facetIndex 28), (facetIndex 38), (facetIndex 82), (facetIndex 90)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 76), (facetIndex 81), (facetIndex 86), (facetIndex 92)]))
 (.branch 4
 (.leaf ([(facetIndex 55), (facetIndex 57), (facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 29), (facetIndex 42), (facetIndex 45), (facetIndex 83)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 50), (facetIndex 96)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 44), (facetIndex 48)])))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 53), (facetIndex 87)]))
 (.branch 9
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 89)]))
 (.leaf ([(facetIndex 43), (facetIndex 80)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5000201807200412900020000303000000000003030700506554694660108800072417z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 70), (facetIndex 74)]))
 (.leaf ([(facetIndex 93), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 91), (facetIndex 104)]))
 (.branch 4
 (.leaf ([(facetIndex 79), (facetIndex 84), (facetIndex 100)]))
 (.leaf ([(facetIndex 95), (facetIndex 98), (facetIndex 105)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 33), (facetIndex 39), (facetIndex 52), (facetIndex 66), (facetIndex 68)]))
 (.branch 7
 (.leaf ([(facetIndex 51), (facetIndex 61), (facetIndex 65), (facetIndex 73), (facetIndex 75)]))
 (.leaf ([(facetIndex 59), (facetIndex 63), (facetIndex 72)]))))
 (.branch 9
 (.leaf ([(facetIndex 32), (facetIndex 54), (facetIndex 60), (facetIndex 62), (facetIndex 64), (facetIndex 85), (facetIndex 99)]))
 (.branch 10
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 97), (facetIndex 101), (facetIndex 103)]))
 (.leaf ([(facetIndex 88), (facetIndex 102)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "429a9384904110200a00830000399060670005056878687000080560000000000050000058z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0002 : List Nat := [5, 6]
def grouped2_0003 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0004 : List Nat := [7]
def grouped2_0005 : List Nat := [7, 8, 9]
def grouped2_0006 : List Nat := [8]
def grouped2_0007 : List Nat := [8, 9]
def grouped2_0008 : List Nat := [9]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6, 7]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [6, 7]
def grouped3_0024 : List Nat := [7]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9, 10]
def grouped3_0027 : List Nat := [9]
def grouped3_0028 : List Nat := [9, 10]
def grouped3_0029 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0005\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026" 77

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026" "{\"ridges\":[[22,644],[25,656],[31,145],[38,644],[39,771],[39,772],[50,656],[51,771],[51,784],[64,784],[66,772],[68,897],[73,784],[74,464],[75,784],[75,897],[84,778],[87,644],[87,656],[88,278],[88,772],[89,644],[90,644],[91,834],[95,778],[96,656],[99,540],[100,808],[101,180],[102,772],[103,404],[103,772],[104,960],[105,808]],\"owners\":[[31,145,[70,72,74,75],[8,41,46,48,50,54,59,62,63]],[22,644,[63,65,68,101,103,104],[38,87,89,90]],[38,644,[101,103,104],[22,63,65,68,87,89,90]],[87,644,[65,68,104],[22,38,63,89,90,101,103]],[89,644,[63,68,103,104],[22,38,65,87,90,101]],[90,644,[63,65,68,101,103],[22,38,87,89,104]],[25,656,[63,72,75,101,103],[50,87,96]],[50,656,[101,103],[25,63,72,75,87,96]],[87,656,[72,75],[25,50,63,96,101,103]],[96,656,[63,75,103],[25,50,72,87,101]],[88,278,[32,78],[]],[39,771,[51],[]],[51,771,[39],[]],[39,772,[99,100,102,103,104],[64,66,68,84,88,91]],[66,772,[84,88,91,99,103,104],[39,64,68,100,102]],[88,772,[66,68,100,104],[39,64,84,91,99,102,103]],[102,772,[39,68,84,91,104],[64,66,88,99,100,103]],[103,772,[39,66,84,91,100],[64,68,88,99,102,104]],[51,784,[99,102,103,105],[64,73,75,88,95]],[64,784,[95,105],[51,73,75,88,99,102,103]],[73,784,[88,95,99,103],[51,64,75,102,105]],[75,784,[88,95,99,102,105],[51,64,73,103]],[101,180,[59,85],[]],[103,404,[62],[]],[68,897,[75],[]],[75,897,[68],[]],[74,464,[],[]],[99,540,[79,98],[]],[84,778,[95],[]],[95,778,[84],[]],[91,834,[],[]],[100,808,[105],[]],[105,808,[100],[]],[104,960,[],[]]],\"edges\":[[43,[22,25,38,50,52,63,65,68,72,75,87,89,90,96,101,103,104]],[44,[39,51,64,66,68,73,75,84,88,91,95,99,100,102,103,104,105]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-6],[-11,-7],[-16,-11],[-18,-11],[-22,-11],[-41,-3],[-41,-13],[-4,21,22,24,25],[-1,16,18,20,40,42,43],[-8,40,42,43],[-30,18,20,43],[-32,16,20,42,43],[-33,16,18,20,40,42],[-2,16,22,25,40,42],[-10,40,42],[-30,22,25],[-36,16,25,42],[-31,5,26],[-9,11],[-11,9],[-9,38,39,41,42,43],[-19,28,31,34,38,42,43],[-31,19,20,39,43],[-41,9,20,28,34,43],[-42,9,19,28,34,39],[-11,38,41,42,44],[-17,35,44],[-23,31,35,38,42],[-25,31,35,38,41,44],[-40,14,29],[-42,15],[-20,25],[-25,20],[-24],[-38,27,37],[-28,35],[-35,28],[-34],[-39,44],[-44,39],[-43],[-45,3,4,13,30],[-46,6,7,32],[-47,46],[-48,45,47],[-49,48],[-50,49],[50],[-21,51],[-27,52],[-28,52],[-39,52],[-35,53],[-37,53],[-44,53],[-9,54],[-12,54],[-19,54],[-20,54],[-11,55],[-18,55],[-23,55],[-25,55],[-14,56],[-16,56],[-22,56],[-5,57],[-15,57],[-17,57],[-29,57],[-38,57],[-26,58],[-40,58],[-42,58],[-31,59],[-41,59],[-51,60],[-53,61],[-52,61],[-52,-53,62],[-61,63],[-62,64],[-63,65],[-64,66],[-60,65],[-56,67],[-55,67],[-67,68],[-54,68],[-54,-67,69],[-59,70],[-58,70],[-58,-59,71],[-70,72],[-71,73],[-57,72],[-57,-70,73],[-73,75],[-68,74],[-68,-72,75],[-68,-73,76],[-69,-72,76],[-76,77],[-65,-75,77],[-66,-74,77],[-77],[1,2,8,10,12,16,18,20,22,25,30,32,33,36,40,42,43],[9,11,17,19,20,23,25,28,31,34,35,38,39,41,42,43,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":51,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":51},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":72,\"b\":51},{\"tag\":\"incompatible\",\"a\":102,\"b\":27},{\"tag\":\"incompatible\",\"a\":102,\"b\":53},{\"tag\":\"mate\",\"ridge\":145,\"a\":31,\"owners\":[70,72,74,75]},{\"tag\":\"mate\",\"ridge\":644,\"a\":22,\"owners\":[63,65,68,101,103,104]},{\"tag\":\"mate\",\"ridge\":644,\"a\":38,\"owners\":[101,103,104]},{\"tag\":\"mate\",\"ridge\":644,\"a\":87,\"owners\":[65,68,104]},{\"tag\":\"mate\",\"ridge\":644,\"a\":89,\"owners\":[63,68,103,104]},{\"tag\":\"mate\",\"ridge\":644,\"a\":90,\"owners\":[63,65,68,101,103]},{\"tag\":\"mate\",\"ridge\":656,\"a\":25,\"owners\":[63,72,75,101,103]},{\"tag\":\"mate\",\"ridge\":656,\"a\":50,\"owners\":[101,103]},{\"tag\":\"mate\",\"ridge\":656,\"a\":87,\"owners\":[72,75]},{\"tag\":\"mate\",\"ridge\":656,\"a\":96,\"owners\":[63,75,103]},{\"tag\":\"mate\",\"ridge\":278,\"a\":88,\"owners\":[32,78]},{\"tag\":\"mate\",\"ridge\":771,\"a\":39,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":771,\"a\":51,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":772,\"a\":39,\"owners\":[99,100,102,103,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":66,\"owners\":[84,88,91,99,103,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":88,\"owners\":[66,68,100,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":102,\"owners\":[39,68,84,91,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":103,\"owners\":[39,66,84,91,100]},{\"tag\":\"mate\",\"ridge\":784,\"a\":51,\"owners\":[99,102,103,105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":64,\"owners\":[95,105]},{\"tag\":\"mate\",\"ridge\":784,\"a\":73,\"owners\":[88,95,99,103]},{\"tag\":\"mate\",\"ridge\":784,\"a\":75,\"owners\":[88,95,99,102,105]},{\"tag\":\"mate\",\"ridge\":180,\"a\":101,\"owners\":[59,85]},{\"tag\":\"mate\",\"ridge\":404,\"a\":103,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":897,\"a\":68,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":897,\"a\":75,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":464,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":540,\"a\":99,\"owners\":[79,98]},{\"tag\":\"mate\",\"ridge\":778,\"a\":84,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":778,\"a\":95,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":834,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":100,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":808,\"a\":105,\"owners\":[100]},{\"tag\":\"mate\",\"ridge\":960,\"a\":104,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[27,31,53,87],\"full_literals\":[-45,3,4,13,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[35,36,89],\"full_literals\":[-46,6,7,32]},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0004\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0005\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,45,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0003\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-50,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":9,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-21,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-27,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":84,\"full_literals\":[-28,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-39,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":95,\"full_literals\":[-35,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":98,\"full_literals\":[-37,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":105,\"full_literals\":[-44,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-9,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-12,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-19,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":68,\"full_literals\":[-20,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":51,\"full_literals\":[-11,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-18,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-25,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-14,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":63,\"full_literals\":[-16,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-22,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":32,\"full_literals\":[-5,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":62,\"full_literals\":[-15,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":64,\"full_literals\":[-17,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-29,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":99,\"full_literals\":[-38,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":78,\"full_literals\":[-26,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":101,\"full_literals\":[-40,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":103,\"full_literals\":[-42,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":88,\"full_literals\":[-31,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":102,\"full_literals\":[-41,59]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-70,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-72,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-73,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-72,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,25,38,50,52,63,65,68,72,75,87,89,90,96,101,103,104]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[39,51,64,66,68,73,75,84,88,91,95,99,100,102,103,104,105]}]}"
  "109 49 0 48 47 0\n110 48 0 109 46 0\n111 -76 0 106 103 0\n112 1 2 8 10 12 16 18 20 22 25 30 32 33 36 40 42 0 41 107 0\n113 9 11 17 19 20 23 25 28 31 35 38 39 41 42 44 0 38 41 108 0\n114 19 9 44 17 20 23 25 28 31 35 38 39 11 42 0 38 41 113 24 0\n115 68 61 0 41 38 78 53 55 27 79 50 54 35 52 51 88 89 87 56 58 59 60 62 63 23 25 114 0\n116 11 25 31 42 61 0 38 41 32 79 50 78 54 35 51 22 53 28 55 27 52 19 114 0\n117 25 31 42 65 0 41 34 110 83 81 79 50 78 54 35 55 85 77 49 32 116 2 3 4 5 20 26 12 11 8 1 6 7 43 42 44 45 0\n118 -25 31 35 38 44 0 111 29 33 63 76 59 87 91 90 94 102 0\n119 31 42 65 0 83 81 79 50 78 54 35 55 53 117 118 0\n120 -31 73 0 95 75 91 93 97 72 67 18 0\n121 65 0 111 83 81 115 101 120 119 31 74 68 92 97 0\n122 -75 0 121 106 104 0\n123 -73 0 122 98 0\n124 -31 0 123 120 0\n125 -42 0 123 31 74 68 92 97 0\n126 -70 0 123 122 41 125 94 97 100 70 88 89 86 87 57 59 64 65 66 61 63 30 12 17 16 14 10 15 9 13 112 0\n127 -59 0 126 91 0\n128 -58 0 126 92 0\n129 -41 0 127 76 0\n130 -40 0 128 73 0\n131 -8 0 130 125 41 10 0\n132 -10 0 130 125 15 0\n133 68 0 41 125 130 132 131 88 89 86 87 57 59 65 66 61 63 9 13 12 17 16 14 112 0\n134 74 0 133 99 0\n135 -72 0 133 122 100 0\n136 -66 0 134 106 105 0\n137 -57 0 135 96 0\n138 -64 0 136 84 0\n139 -17 0 137 69 0\n140 -38 0 137 71 0\n141 -62 0 138 82 0\n142 35 25 44 0 129 41 38 125 140 124 139 32 39 21 26 36 28 22 114 0\n143 -35 0 141 37 53 51 80 0\n144 44 0 124 140 143 118 142 0\n145 39 0 144 40 0\n146 53 0 144 55 0\n147 52 0 145 52 0\n148 0 147 146 141 80 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "16c373c2d2acaca96aa68dae19c6598d64d8b6c3a8e538ce4b86e2785ef0749b27295a6993678571565355352d70da354d3352d1b49d17783d0ec370f2358e9334d332cf0ba2e4b52ccb8ad2b1ae1b26c5bc1e8761ca719d1715e0f43c8f0f03a518c6498960d84e0b81e0e54531525254351342d07703a0d4330d2324c3382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6da4926d24926db6db4924da492492492492492492492492492249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 80), (facetIndex 87)]))
 (.leaf ([(facetIndex 73), (facetIndex 81), (facetIndex 82), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 83), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 101), (facetIndex 108)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 94), (facetIndex 102), (facetIndex 103), (facetIndex 106)]))
 (.leaf ([(facetIndex 95), (facetIndex 104), (facetIndex 105), (facetIndex 107)])))
 (.branch 7
 (.leaf ([(facetIndex 109)]))
 (.leaf ([(facetIndex 110)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1f3b2d918000b0000008a448000088z36;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045" 44

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045" "{\"ridges\":[[9,522],[15,641],[16,769],[38,522],[44,641],[45,769],[48,522],[51,522],[54,522],[55,522],[55,641],[56,522],[56,770],[60,641],[62,769],[64,641],[65,769],[66,641],[66,769],[73,652],[74,780],[80,900],[82,664],[84,808],[85,712],[86,840],[87,960],[94,652],[95,780],[101,900],[103,664],[105,808],[106,712],[107,840],[108,960]],\"owners\":[[9,522,[94,95,103,105,106,107],[38,48,51,54,55,56]],[38,522,[103,105,106,107],[9,48,51,54,55,56,94,95]],[48,522,[94,95,105,106,107],[9,38,51,54,55,56,103]],[51,522,[94,95,103,106,107],[9,38,48,54,55,56,105]],[54,522,[94,95,103,105],[9,38,48,51,55,56,106,107]],[55,522,[95,105,107],[9,38,48,51,54,56,94,103,106]],[56,522,[94,103,106],[9,38,48,51,54,55,95,105,107]],[15,641,[73,80,82,85,87],[44,55,60,64,66]],[44,641,[82,85,87],[15,55,60,64,66,73,80]],[55,641,[80,87],[15,44,60,64,66,73,82,85]],[60,641,[73,80,85,87],[15,44,55,64,66,82]],[64,641,[73,80,82],[15,44,55,60,66,85,87]],[66,641,[73,82,85],[15,44,55,60,64,80,87]],[16,769,[74,80,84,86,87],[45,56,62,65,66]],[45,769,[84,86,87],[16,56,62,65,66,74,80]],[62,769,[74,80,86,87],[16,45,56,65,66,84]],[65,769,[74,80,84],[16,45,56,62,66,86,87]],[66,769,[74,84,86],[16,45,56,62,65,80,87]],[56,770,[101,108],[16,45,62,65,66,95,105,107]],[73,652,[94],[]],[94,652,[73],[]],[74,780,[95],[]],[95,780,[74],[]],[80,900,[101],[]],[101,900,[80],[]],[82,664,[103],[]],[103,664,[82],[]],[84,808,[105],[]],[105,808,[84],[]],[85,712,[106],[]],[106,712,[85],[]],[86,840,[107],[]],[107,840,[86],[]],[87,960,[108],[]],[108,960,[87],[]]],\"edges\":[[29,[9,38,48,51,54,55,56,73,74,82,84,85,86,94,95,103,105,106,107]],[43,[15,44,55,60,64,66,73,80,82,85,87,94,101,103,106,108]],[44,[16,45,56,62,65,66,74,80,84,86,87,95,101,105,107,108]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,25,26,28,29,30,31],[-4,28,29,30,31],[-7,25,26,29,30,31],[-8,25,26,28,30,31],[-9,25,26,28,29],[-10,26,29,31],[-11,25,28,30],[-2,17,19,20,22,24],[-5,20,22,24],[-10,19,24],[-12,17,19,22,24],[-14,17,19,20],[-16,17,20,22],[-3,18,19,21,23,24],[-6,21,23,24],[-13,18,19,23,24],[-15,18,19,21],[-16,18,21,23],[-11,27,32],[-17,25],[-25,17],[-18,26],[-26,18],[-19,27],[-27,19],[-20,28],[-28,20],[-21,29],[-29,21],[-22,30],[-30,22],[-23,31],[-31,23],[-24,32],[-32,24],[-19,33],[-24,33],[-17,34],[-20,34],[-22,34],[-18,35],[-21,35],[-23,35],[-27,36],[-32,36],[-25,37],[-28,37],[-30,37],[-26,38],[-29,38],[-31,38],[-34,39],[-33,39],[-36,40],[-35,40],[-39,-40,41],[-38,42],[-37,42],[-42,43],[-41,-43,44],[-44],[1,4,7,8,9,10,11,17,18,20,21,22,23,25,26,28,29,30,31],[2,5,10,12,14,16,17,19,20,22,24,25,27,28,30,32],[3,6,11,13,15,16,18,19,21,23,24,26,27,29,31,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":522,\"a\":9,\"owners\":[94,95,103,105,106,107]},{\"tag\":\"mate\",\"ridge\":522,\"a\":38,\"owners\":[103,105,106,107]},{\"tag\":\"mate\",\"ridge\":522,\"a\":48,\"owners\":[94,95,105,106,107]},{\"tag\":\"mate\",\"ridge\":522,\"a\":51,\"owners\":[94,95,103,106,107]},{\"tag\":\"mate\",\"ridge\":522,\"a\":54,\"owners\":[94,95,103,105]},{\"tag\":\"mate\",\"ridge\":522,\"a\":55,\"owners\":[95,105,107]},{\"tag\":\"mate\",\"ridge\":522,\"a\":56,\"owners\":[94,103,106]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[73,80,82,85,87]},{\"tag\":\"mate\",\"ridge\":641,\"a\":44,\"owners\":[82,85,87]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[80,87]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[73,80,85,87]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[73,80,82]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[73,82,85]},{\"tag\":\"mate\",\"ridge\":769,\"a\":16,\"owners\":[74,80,84,86,87]},{\"tag\":\"mate\",\"ridge\":769,\"a\":45,\"owners\":[84,86,87]},{\"tag\":\"mate\",\"ridge\":769,\"a\":62,\"owners\":[74,80,86,87]},{\"tag\":\"mate\",\"ridge\":769,\"a\":65,\"owners\":[74,80,84]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[74,84,86]},{\"tag\":\"mate\",\"ridge\":770,\"a\":56,\"owners\":[101,108]},{\"tag\":\"mate\",\"ridge\":652,\"a\":73,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":652,\"a\":94,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":780,\"a\":74,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":780,\"a\":95,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":900,\"a\":80,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":900,\"a\":101,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":664,\"a\":82,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":664,\"a\":103,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":808,\"a\":84,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":808,\"a\":105,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":712,\"a\":85,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":712,\"a\":106,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":840,\"a\":86,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":840,\"a\":107,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":960,\"a\":87,\"owners\":[108]},{\"tag\":\"mate\",\"ridge\":960,\"a\":108,\"owners\":[87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":80,\"full_literals\":[-19,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":87,\"full_literals\":[-24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-17,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-20,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-22,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-18,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-21,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-23,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":101,\"full_literals\":[-27,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":108,\"full_literals\":[-32,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":94,\"full_literals\":[-25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":103,\"full_literals\":[-28,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":106,\"full_literals\":[-30,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":105,\"full_literals\":[-29,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":107,\"full_literals\":[-31,38]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[9,38,48,51,54,55,56,73,74,82,84,85,86,94,95,103,105,106,107]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,44,55,60,64,66,73,80,82,85,87,94,101,103,106,108]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,45,56,62,65,66,74,80,84,86,87,95,101,105,107,108]}]}"
  "65 42 0 57 58 49 50 51 46 47 48 6 22 28 32 1 3 4 5 7 20 2 26 30 62 0\n66 43 0 65 59 0\n67 -41 0 66 61 60 0\n68 40 0 54 55 44 45 41 42 43 19 24 34 18 23 29 33 17 14 16 15 64 0\n69 -39 0 68 67 56 0\n70 -34 0 69 52 0\n71 -33 0 69 53 0\n72 -17 0 70 38 0\n73 -20 0 70 39 0\n74 -22 0 70 40 0\n75 -19 0 71 36 0\n76 -24 0 71 37 0\n77 -16 0 72 73 74 13 0\n78 -25 0 72 21 0\n79 -12 0 72 75 74 76 11 0\n80 -2 0 72 75 73 74 76 8 0\n81 -14 0 72 75 73 12 0\n82 -5 0 73 74 76 9 0\n83 -28 0 73 27 0\n84 -30 0 74 31 0\n85 -10 0 75 76 10 0\n86 -27 0 75 25 0\n87 -32 0 76 35 0\n88 0 81 86 82 79 80 85 72 77 75 74 76 78 73 83 84 87 63 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045 Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00004.record045_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00004.record045
