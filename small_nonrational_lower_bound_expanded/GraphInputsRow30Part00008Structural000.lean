module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow30Part00008Data
public import GraphInputsRow30Part00008Frames
public import GraphInputsRow30Part00008Leaves
public import GraphInputsRow30Part00008Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨120, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 905969664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 4), (certNat% 11), (certNat% 12), (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 15), (certNat% 20), (certNat% 17), (certNat% 18)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 11), (certNat% 27), (certNat% 28), (certNat% 29)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), (certNat% 25), (certNat% 36)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), (certNat% 45), (certNat% 28), (certNat% 46)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a8ad2744f07ce8b52ccab2e2b4ab2b2aaa9aa5693ab1aa6a5a568d9362d8ce4b8ae4785e0fba1d4731ac6716a5594e4794d4b51d4cd4b46d4745d0f783d0ec3c8ea368f13a4e5354e334ccb362d4b32d2b2ad1b16c3b31d2729d1725c3743c2f07f302b312948562384e4c5292a4a5154352344d0b51314d0b22c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da4db6db6db69b69a69b69b4d349249a4db6da6934d24924d3492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 85), (facetIndex 100)]))
 (.leaf ([(facetIndex 89), (facetIndex 91), (facetIndex 92), (facetIndex 93)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 57), (facetIndex 64), (facetIndex 66)]))
 (.branch 4
 (.leaf ([(facetIndex 73), (facetIndex 75), (facetIndex 87), (facetIndex 98)]))
 (.leaf ([(facetIndex 32), (facetIndex 86), (facetIndex 99)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 68)]))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 69), (facetIndex 101)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 77), (facetIndex 79), (facetIndex 84), (facetIndex 90)]))))
 (.branch 9
 (.leaf ([(facetIndex 51), (facetIndex 80), (facetIndex 88), (facetIndex 94)]))
 (.branch 10
 (.leaf ([(facetIndex 72), (facetIndex 97), (facetIndex 102)]))
 (.leaf ([(facetIndex 71)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "9604390081117183407000870703039a065020200000020055587705005060000000204z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2, 3, 4]
def grouped3_0006 : List Nat := [5]
def grouped3_0007 : List Nat := [5, 6, 7]
def grouped3_0008 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0009 : List Nat := [6]
def grouped3_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [7]
def grouped3_0012 : List Nat := [8]
def grouped3_0013 : List Nat := [8, 9, 10]
def grouped3_0014 : List Nat := [9]
def grouped3_0015 : List Nat := [9, 10]
def grouped3_0016 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005" 54

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005" "{\"ridges\":[[21,592],[24,800],[46,578],[50,642],[52,705],[53,833],[68,609],[71,833],[82,592],[83,660],[84,550],[84,672],[85,708],[89,672],[91,712],[92,840],[93,904],[94,642],[96,578],[97,642],[97,672],[100,612],[101,560],[101,660],[102,672],[102,904]],\"owners\":[[46,578,[85,91,92],[21,52,53,82,96]],[96,578,[52,85,91],[21,46,53,82,92]],[21,592,[68,71,100],[46,82,96]],[82,592,[68,71],[21,46,96,100]],[101,560,[24,44,68,70,95],[69,81,94,100]],[24,800,[51,72,90,97,102],[70,95]],[50,642,[83,85,91,93],[47,52,54,84,89,94,97]],[94,642,[52,54,85,91,93],[47,50,83,84,89,97]],[97,642,[47,52,83,85,91],[50,54,84,89,93,94]],[84,672,[69,72,102],[50,89,94,97,101]],[89,672,[69,72,101],[50,84,94,97,102]],[97,672,[69,101],[50,72,84,89,94,102]],[102,672,[50,69,84,94,101],[72,89,97]],[52,705,[],[]],[53,833,[71],[]],[71,833,[53],[]],[68,609,[],[]],[84,550,[81],[]],[83,660,[101],[]],[101,660,[83],[]],[85,708,[],[]],[91,712,[],[]],[92,840,[],[]],[93,904,[102],[]],[102,904,[93],[]],[100,612,[],[]]],\"edges\":[[41,[21,46,52,53,68,71,82,85,91,92,96,100]],[43,[47,50,52,54,69,72,83,84,85,89,91,93,94,97,101,102]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-3],[-14,-5],[-14,-6],[-14,-7],[-14,-10],[-14,-12],[-14,-13],[-15,-14],[-27,-14],[-4,20,23,24],[-28,8,20,23],[-1,11,14,30],[-17,11,14],[-31,2,3,11,13,27],[-2,7,15,22,29,32],[-6,18,20,23,25],[-26,8,10,20,23,25],[-29,5,8,18,20,23],[-19,12,15,32],[-21,12,15,31],[-29,12,31],[-32,6,12,19,26,31],[-8],[-9,14],[-14,9],[-11],[-19,16],[-18,31],[-31,18],[-20],[-23],[-24],[-25,32],[-32,25],[-30],[-16,33],[-18,33],[-21,34],[-25,34],[-9,35],[-31,36],[-19,37],[-22,37],[-26,38],[-29,39],[-32,39],[-14,40],[-34,41],[-33,41],[-41,42],[-37,43],[-36,43],[-36,-37,44],[-35,45],[-35,-43,46],[-35,-44,47],[-40,48],[-39,-40,49],[-48,50],[-49,51],[-38,-49,52],[-45,-52,53],[-46,-51,53],[-47,-50,53],[-42,-53,54],[-54],[1,4,8,9,11,14,17,20,23,24,28,30],[5,6,8,10,12,15,18,19,20,21,23,25,26,29,31,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":50},{\"tag\":\"incompatible\",\"a\":71,\"b\":51},{\"tag\":\"incompatible\",\"a\":71,\"b\":54},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":95,\"b\":71},{\"tag\":\"mate\",\"ridge\":578,\"a\":46,\"owners\":[85,91,92]},{\"tag\":\"mate\",\"ridge\":578,\"a\":96,\"owners\":[52,85,91]},{\"tag\":\"mate\",\"ridge\":592,\"a\":21,\"owners\":[68,71,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":82,\"owners\":[68,71]},{\"tag\":\"mate\",\"ridge\":560,\"a\":101,\"owners\":[24,44,68,70,95]},{\"tag\":\"mate\",\"ridge\":800,\"a\":24,\"owners\":[51,72,90,97,102]},{\"tag\":\"mate\",\"ridge\":642,\"a\":50,\"owners\":[83,85,91,93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":94,\"owners\":[52,54,85,91,93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":97,\"owners\":[47,52,83,85,91]},{\"tag\":\"mate\",\"ridge\":672,\"a\":84,\"owners\":[69,72,102]},{\"tag\":\"mate\",\"ridge\":672,\"a\":89,\"owners\":[69,72,101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":97,\"owners\":[69,101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":102,\"owners\":[50,69,84,94,101]},{\"tag\":\"mate\",\"ridge\":705,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":833,\"a\":53,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":833,\"a\":71,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":609,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":550,\"a\":84,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":660,\"a\":83,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":660,\"a\":101,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":708,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":712,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":840,\"a\":92,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":904,\"a\":93,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":904,\"a\":102,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":612,\"a\":100,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":81,\"full_literals\":[-16,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":83,\"full_literals\":[-18,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-21,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":93,\"full_literals\":[-25,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":53,\"full_literals\":[-9,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":101,\"full_literals\":[-31,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-19,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":94,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":97,\"full_literals\":[-29,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":102,\"full_literals\":[-32,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":71,\"full_literals\":[-14,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-43,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-44,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-49,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-38,-49,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-45,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0008\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-42,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[21,46,52,53,68,71,82,85,91,92,96,100]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[47,50,52,54,69,72,83,84,85,89,91,93,94,97,101,102]}]}"
  "69 -28 0 31 23 30 11 0\n70 -4 0 32 30 31 10 0\n71 1 9 14 17 0 70 23 26 30 31 32 69 35 67 0\n72 5 6 10 12 15 18 19 21 25 26 29 31 32 0 23 30 31 68 0\n73 5 12 6 32 15 18 19 21 25 10 29 31 0 23 30 31 72 17 0\n74 -14 41 0 31 30 23 49 37 29 48 39 16 36 27 34 38 2 5 6 8 18 73 0\n75 14 0 35 26 24 12 13 71 0\n76 -3 0 75 1 0\n77 -5 0 75 2 0\n78 -6 0 75 3 0\n79 -7 0 75 4 0\n80 -10 0 75 5 0\n81 -12 0 75 6 0\n82 -13 0 75 7 0\n83 -15 0 75 8 0\n84 -27 0 75 9 0\n85 9 0 75 25 0\n86 40 0 75 47 0\n87 41 0 75 74 0\n88 35 0 85 40 0\n89 48 0 86 57 0\n90 42 0 87 50 0\n91 45 0 88 54 0\n92 50 0 89 59 0\n93 -53 0 90 66 65 0\n94 -52 0 91 93 62 0\n95 -47 0 92 93 64 0\n96 -44 0 95 88 56 0\n97 31 32 0 77 80 83 81 78 19 33 28 20 21 73 0\n98 32 0 84 82 26 76 96 88 93 79 83 86 97 14 41 52 53 55 43 63 15 60 45 58 0\n99 39 0 98 46 0\n100 49 0 99 86 58 0\n101 51 0 100 60 0\n102 -38 0 100 94 61 0\n103 -46 0 101 93 63 0\n104 -26 0 102 44 0\n105 -43 0 103 88 55 0\n106 -37 0 105 51 0\n107 -36 0 105 52 0\n108 -19 0 106 42 0\n109 -31 0 107 41 0\n110 0 108 109 81 78 98 104 22 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005
