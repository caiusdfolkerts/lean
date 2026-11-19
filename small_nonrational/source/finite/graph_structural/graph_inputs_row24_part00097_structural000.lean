module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00097Data
public import GraphInputsRow24Part00097Frames
public import GraphInputsRow24Part00097Leaves
public import GraphInputsRow24Part00097Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record028
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028
def vertexColumn : Fields := ⟨10, hexnat% "2f0ad0f46b0ec372e2b4ab29c8f25a8eaa68daa98e6a58d68d8b61d8ce4b8ae1b91e2785eb86d1ac6713c5693a699366a539695356352d4753352d2b46d4749d1772398d6394e331cd4b4ac6b86d1b89c6785d1715c3713c2f3609c169264381e165254341d88d2318e1314d0b12c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db6db69b6db6d36926db6db4db6db69b492492492492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨55, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨78, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8040010080020000000000", hexnat% "200000400204400000", hexnat% "600000c0000000000", 330712481792, 208490463232, 1650072748032, 1082130432]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record028_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record028

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record033
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033
def vertexColumn : Fields := ⟨10, hexnat% "f4ab13c2f07cb8b2aaaa9aa98e6a3a2e4b8ae1b91e2785eb85713c7294e479a94e5355352d4758b52d1b51d1743db0f23a8e6358ce3a4d5334f0b8ad2b1ae1b16e8731e2749ca719d1725e0f43c4f0bce4350d2468c62585607a294a519194550b41d44c5382d0b06c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6da6db6926da4da4da49249b6db69249a4d36d2492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "700000000018000000", 6631429505024, hexnat% "4010001800000200000000", hexnat% "180c0004000000000", 1718095970304, 83316593660002304, 5629499534213120]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record033_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record033

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b92b43b29c3716a3a8da8d9364b86e4785eb8731ac5b16a5693a699664d9b16a5994e5a54d58d5352d68d3352d2b46d8751d2745d58ce334e334ccb352ccb4acab1ac9b16e2749e1745c570dd0f0bd1a1984e07aa1386913251926625196151341d48c6344d0b12c1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6da4934db4926924d36d36924926d3493492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 60), (facetIndex 61), (facetIndex 73)]))
 (.leaf ([(facetIndex 26), (facetIndex 33), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 35), (facetIndex 37), (facetIndex 50), (facetIndex 67), (facetIndex 76)]))
 (.leaf ([(facetIndex 34), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 65), (facetIndex 66)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 41), (facetIndex 45)]))
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 62), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 30), (facetIndex 32)]))
 (.branch 8
 (.leaf ([(facetIndex 38), (facetIndex 46), (facetIndex 53), (facetIndex 64)]))
 (.leaf ([(facetIndex 29), (facetIndex 31)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2110050002337050050500070023337400040472023168686612z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 40), (facetIndex 43)]))
 (.leaf ([(facetIndex 58), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 55), (facetIndex 56), (facetIndex 70), (facetIndex 72)]))
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 68), (facetIndex 69), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 86)]))
 (.leaf ([(facetIndex 77), (facetIndex 82), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 54), (facetIndex 63), (facetIndex 83)]))
 (.leaf ([(facetIndex 84), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "f2fd5992800209b000c0004258360000008z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7, 8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009" 65

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009" "{\"ridges\":[[9,289],[9,290],[15,152],[17,200],[31,289],[31,290],[34,152],[37,289],[37,290],[38,200],[41,289],[41,290],[45,289],[45,290],[47,152],[51,172],[52,300],[53,137],[56,308],[57,532],[59,656],[62,672],[64,152],[65,152],[66,152],[67,224],[68,360],[69,424],[70,432],[71,656],[72,816],[77,300],[78,308],[81,170],[82,360]],\"owners\":[[9,289,[52,56,68,69,70,72],[31,37,41,45]],[31,289,[68,69,70,72],[9,37,41,45,52,56]],[37,289,[56,70,72],[9,31,41,45,52,68,69]],[41,289,[52,68,69],[9,31,37,45,56,70,72]],[45,289,[52,56,69,70,72],[9,31,37,41,68]],[9,290,[77,78,82],[31,37,41,45]],[31,290,[82],[9,37,41,45,77,78]],[37,290,[78],[9,31,41,45,77,82]],[41,290,[77,82],[9,31,37,45,78]],[45,290,[77,78],[9,31,37,41,82]],[57,532,[84],[12,30,49,59,79,86]],[53,137,[15,34,36,65,66,69],[17,38,47,51,54,67]],[15,152,[80,83,84],[34,47,64,65,66]],[34,152,[83,84],[15,47,64,65,66,80]],[47,152,[80],[15,34,64,65,66,83,84]],[64,152,[84],[15,34,47,65,66,80,83]],[65,152,[80,83,84],[15,34,47,64,66]],[66,152,[80,83],[15,34,47,64,65,84]],[17,200,[80,81,83,85],[38,53,64,67]],[38,200,[83,85],[17,53,64,67,80,81]],[59,656,[],[18,66,71,84,86]],[71,656,[84],[18,59,66,86]],[67,224,[87],[19,44,60,73,81,85]],[62,672,[],[20,71,73,86,87]],[81,170,[36],[]],[51,172,[85],[]],[52,300,[77],[]],[77,300,[52],[]],[56,308,[78],[]],[78,308,[56],[]],[68,360,[82],[]],[82,360,[68],[]],[69,424,[],[]],[70,432,[],[]],[72,816,[],[]]],\"edges\":[[27,[15,17,34,36,38,47,51,53,54,64,65,66,67,69,80,81,83,84,85]],[37,[9,31,37,41,45,52,56,68,69,70,72,77,78,82]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-40,-4],[-40,-7],[-40,-9],[-40,-14],[-40,-32],[-1,16,19,27,28,29,31],[-5,27,28,29,31],[-9,19,29,31],[-11,16,27,28],[-12,16,19,28,29,31],[-1,33,34,37],[-5,37],[-9,34],[-11,33,37],[-12,33,34],[-20,39],[-17,2,6,8,24,25,28],[-2,35,38,39],[-6,38,39],[-13,35],[-23,39],[-24,35,38,39],[-25,35,38],[-3,35,36,38,40],[-10,38,40],[-21],[-30,39],[-26,41],[-22],[-36,8],[-15,40],[-16,33],[-33,16],[-19,34],[-34,19],[-27,37],[-37,27],[-28],[-29],[-31],[-42,4,7,9,14,26,32],[-43,20,21,22,30],[-44,42],[-45,44],[-46,43],[-47,46],[-48,45,47],[48],[-8,49],[-35,50],[-19,51],[-16,52],[-27,52],[-34,53],[-33,54],[-37,54],[-18,55],[-38,55],[-39,56],[-41,56],[-50,57],[-49,57],[-52,58],[-51,58],[-58,59],[-57,-58,60],[-54,61],[-53,61],[-56,62],[-55,62],[-61,63],[-61,-62,64],[-59,-64,65],[-60,-63,65],[-65],[2,3,6,8,10,13,15,17,18,23,24,25,26,28,35,36,38,39,40],[1,5,9,11,12,16,19,27,28,29,31,33,34,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":85,\"b\":25},{\"tag\":\"incompatible\",\"a\":85,\"b\":35},{\"tag\":\"incompatible\",\"a\":85,\"b\":37},{\"tag\":\"incompatible\",\"a\":85,\"b\":50},{\"tag\":\"incompatible\",\"a\":85,\"b\":76},{\"tag\":\"mate\",\"ridge\":289,\"a\":9,\"owners\":[52,56,68,69,70,72]},{\"tag\":\"mate\",\"ridge\":289,\"a\":31,\"owners\":[68,69,70,72]},{\"tag\":\"mate\",\"ridge\":289,\"a\":37,\"owners\":[56,70,72]},{\"tag\":\"mate\",\"ridge\":289,\"a\":41,\"owners\":[52,68,69]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[52,56,69,70,72]},{\"tag\":\"mate\",\"ridge\":290,\"a\":9,\"owners\":[77,78,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":31,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":37,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":290,\"a\":41,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":45,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":137,\"a\":53,\"owners\":[15,34,36,65,66,69]},{\"tag\":\"mate\",\"ridge\":152,\"a\":15,\"owners\":[80,83,84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":34,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":47,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":152,\"a\":64,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":65,\"owners\":[80,83,84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":66,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":200,\"a\":17,\"owners\":[80,81,83,85]},{\"tag\":\"mate\",\"ridge\":200,\"a\":38,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":656,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":67,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":672,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":170,\"a\":81,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":172,\"a\":51,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":300,\"a\":52,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":300,\"a\":77,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":308,\"a\":56,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":308,\"a\":78,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":360,\"a\":68,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":360,\"a\":82,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":424,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":72,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[25,35,37,50,67,76],\"full_literals\":[-42,4,7,9,14,26,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[57,59,62,71],\"full_literals\":[-43,20,21,22,30]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-47,46,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-48,45,47],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":36,\"full_literals\":[-8,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-19,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":52,\"full_literals\":[-16,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-27,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-33,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-37,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":54,\"full_literals\":[-18,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-38,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-39,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-41,56]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-59,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[15,17,34,36,38,47,51,53,54,64,65,66,67,69,80,81,83,84,85]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[9,31,37,41,45,52,56,68,69,70,72,77,78,82]}]}"
  "p cnf 65 77\n-40 -4 0\n-40 -7 0\n-40 -9 0\n-40 -14 0\n-40 -32 0\n-1 16 19 27 28 29 31 0\n-5 27 28 29 31 0\n-9 19 29 31 0\n-11 16 27 28 0\n-12 16 19 28 29 31 0\n-1 33 34 37 0\n-5 37 0\n-9 34 0\n-11 33 37 0\n-12 33 34 0\n-20 39 0\n-17 2 6 8 24 25 28 0\n-2 35 38 39 0\n-6 38 39 0\n-13 35 0\n-23 39 0\n-24 35 38 39 0\n-25 35 38 0\n-3 35 36 38 40 0\n-10 38 40 0\n-21 0\n-30 39 0\n-26 41 0\n-22 0\n-36 8 0\n-15 40 0\n-16 33 0\n-33 16 0\n-19 34 0\n-34 19 0\n-27 37 0\n-37 27 0\n-28 0\n-29 0\n-31 0\n-42 4 7 9 14 26 32 0\n-43 20 21 22 30 0\n-44 42 0\n-45 44 0\n-46 43 0\n-47 46 0\n-48 45 47 0\n48 0\n-8 49 0\n-35 50 0\n-19 51 0\n-16 52 0\n-27 52 0\n-34 53 0\n-33 54 0\n-37 54 0\n-18 55 0\n-38 55 0\n-39 56 0\n-41 56 0\n-50 57 0\n-49 57 0\n-52 58 0\n-51 58 0\n-58 59 0\n-57 -58 60 0\n-54 61 0\n-53 61 0\n-56 62 0\n-55 62 0\n-61 63 0\n-61 -62 64 0\n-59 -64 65 0\n-60 -63 65 0\n-65 0\n2 3 6 8 10 13 15 17 18 23 24 25 26 28 35 36 38 39 40 0\n1 5 9 11 12 16 19 27 28 29 31 33 34 37 0\n"
  "78 -43 20 30 0 26 29 42 0\n79 2 3 6 8 10 13 15 17 18 23 24 25 26 35 36 38 39 40 0 38 76 0\n80 1 5 9 11 12 16 19 27 33 34 37 0 38 39 40 77 0\n81 58 0 40 39 38 63 64 52 53 51 33 7 37 9 6 8 35 10 80 0\n82 59 0 81 65 0\n83 -64 0 82 75 73 0\n84 61 0 67 68 55 56 54 32 12 36 14 11 13 34 15 80 0\n85 63 0 84 71 0\n86 -62 0 84 83 72 0\n87 -60 0 85 75 74 0\n88 -56 0 86 69 0\n89 -55 0 86 70 0\n90 -57 0 87 81 66 0\n91 -39 0 88 59 0\n92 -41 0 88 60 0\n93 -18 0 89 57 0\n94 -38 0 89 58 0\n95 -50 0 90 61 0\n96 -49 0 90 62 0\n97 -20 0 91 16 0\n98 -23 0 91 21 0\n99 -30 0 91 27 0\n100 -6 0 91 94 19 0\n101 -26 0 92 28 0\n102 -35 0 95 50 0\n103 -8 0 96 49 0\n104 -43 0 99 97 78 0\n105 -13 0 102 20 0\n106 -2 0 102 94 91 18 0\n107 -24 0 102 91 94 22 0\n108 -25 0 102 94 23 0\n109 -36 0 103 30 0\n110 -46 0 104 45 0\n111 -17 0 107 106 103 100 108 38 17 0\n112 -47 0 110 46 0\n113 45 0 112 48 47 0\n114 44 0 113 44 0\n115 42 0 114 43 0\n116 40 0 91 94 109 102 101 108 107 98 93 111 105 100 103 106 31 25 24 79 0\n117 -4 0 116 1 0\n118 -7 0 116 2 0\n119 -9 0 116 3 0\n120 -14 0 116 4 0\n121 -32 0 116 5 0\n122 0 121 117 115 118 120 119 101 41 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc2b4a72e2b4ab29c8f25a8eaa68dac9a361d92e1ba1e4785eac4f16a5693a6a5a56352d4754b4ad1b51d2745da8d6338e9334e332cc7352ccb4acab1ad1b26e2719e1745c570dc4f0bcd816a2649a164381e384d132499165254341d48c6314d0b12c1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6da49a69269b4db6d36926934da493492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 48), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 70), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 45), (facetIndex 72)]))
 (.leaf ([(facetIndex 25), (facetIndex 35), (facetIndex 37), (facetIndex 53), (facetIndex 59), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 62)]))
 (.leaf ([(facetIndex 30), (facetIndex 64), (facetIndex 65), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 46)]))
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 29), (facetIndex 31)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "224316d100600018000190404c98601f7f3d8z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 51), (facetIndex 52), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 67), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 55), (facetIndex 57), (facetIndex 81)]))
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 73), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 80)]))
 (.leaf ([(facetIndex 42), (facetIndex 54), (facetIndex 78), (facetIndex 82), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 56), (facetIndex 69)]))
 (.leaf ([(facetIndex 47), (facetIndex 58), (facetIndex 63)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b54764258030200e001d6540000e03158z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026" 50

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026" "{\"ridges\":[[44,656],[45,224],[47,643],[47,672],[52,172],[57,645],[58,645],[58,672],[61,424],[62,161],[63,656],[63,672],[72,74],[73,650],[78,656],[79,706],[80,706],[81,652],[82,656],[83,656],[83,672]],\"owners\":[[72,74,[5,26,35,39,67,75],[23,38,64,74]],[62,161,[36,47,52,58,61],[17,41,45,55,59,63]],[45,224,[83],[17,59,62,74,76,80]],[47,643,[44],[]],[44,656,[81,82,83],[57,63,73,78,79]],[63,656,[73,79,81],[44,57,78,82,83]],[78,656,[57,81],[44,63,73,79,82,83]],[82,656,[44,73,79],[57,63,78,81,83]],[83,656,[44,57,73,81],[63,78,79,82]],[47,672,[82,83],[58,63,78,80]],[58,672,[78,80,83],[47,63,82]],[63,672,[80],[47,58,78,82,83]],[83,672,[47,58],[63,78,80,82]],[52,172,[],[]],[57,645,[58],[]],[58,645,[57],[]],[61,424,[],[]],[73,650,[],[]],[79,706,[80],[]],[80,706,[79],[]],[81,652,[],[]]],\"edges\":[[43,[44,47,57,58,63,73,78,79,80,81,82,83]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-1],[-7,-2],[-7,-3],[-7,-5],[-7,-6],[-8,-7],[-19,1,2,3,6,18,21],[-16,4,11,12,14,15],[-10,27],[-11,9],[-9,25,26,27],[-17,20,23,25],[-22,13,25],[-26,9,20,23],[-27,9,13,20,25],[-11,26,27],[-14,22,24,27],[-17,24],[-27,11,14],[-12],[-13,14],[-14,13],[-15],[-20],[-23,24],[-24,23],[-25],[-28,5,8,10,19],[-29,7,16],[-30,28],[-31,30],[-32,29],[-33,32],[-34,31],[-34,33],[34],[-4,35],[-18,36],[-21,36],[-13,37],[-9,38],[-23,38],[-24,39],[-22,40],[-26,40],[-27,40],[-11,41],[-14,41],[-36,42],[-35,42],[-38,43],[-37,43],[-43,44],[-42,-43,45],[-40,46],[-39,46],[-41,47],[-46,48],[-46,-47,49],[-44,-49,50],[-45,-48,50],[-50],[9,11,13,14,17,20,22,23,24,25,26,27]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":5},{\"tag\":\"incompatible\",\"a\":40,\"b\":26},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"mate\",\"ridge\":74,\"a\":72,\"owners\":[5,26,35,39,67,75]},{\"tag\":\"mate\",\"ridge\":161,\"a\":62,\"owners\":[36,47,52,58,61]},{\"tag\":\"mate\",\"ridge\":224,\"a\":45,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":643,\"a\":47,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":656,\"a\":44,\"owners\":[81,82,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":63,\"owners\":[73,79,81]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[57,81]},{\"tag\":\"mate\",\"ridge\":656,\"a\":82,\"owners\":[44,73,79]},{\"tag\":\"mate\",\"ridge\":656,\"a\":83,\"owners\":[44,57,73,81]},{\"tag\":\"mate\",\"ridge\":672,\"a\":47,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":672,\"a\":58,\"owners\":[78,80,83]},{\"tag\":\"mate\",\"ridge\":672,\"a\":63,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":672,\"a\":83,\"owners\":[47,58]},{\"tag\":\"mate\",\"ridge\":172,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":645,\"a\":57,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":645,\"a\":58,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":424,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":79,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":706,\"a\":80,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":652,\"a\":81,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,43,45,72],\"full_literals\":[-28,5,8,10,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[40,62],\"full_literals\":[-29,7,16]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-34,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-34,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":36,\"full_literals\":[-4,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-18,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-21,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-13,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":44,\"full_literals\":[-9,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-24,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-22,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-26,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-27,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":47,\"full_literals\":[-11,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":58,\"full_literals\":[-14,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-48,50],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[44,47,57,58,63,73,78,79,80,81,82,83]}]}"
  "p cnf 50 63\n-7 -1 0\n-7 -2 0\n-7 -3 0\n-7 -5 0\n-7 -6 0\n-8 -7 0\n-19 1 2 3 6 18 21 0\n-16 4 11 12 14 15 0\n-10 27 0\n-11 9 0\n-9 25 26 27 0\n-17 20 23 25 0\n-22 13 25 0\n-26 9 20 23 0\n-27 9 13 20 25 0\n-11 26 27 0\n-14 22 24 27 0\n-17 24 0\n-27 11 14 0\n-12 0\n-13 14 0\n-14 13 0\n-15 0\n-20 0\n-23 24 0\n-24 23 0\n-25 0\n-28 5 8 10 19 0\n-29 7 16 0\n-30 28 0\n-31 30 0\n-32 29 0\n-33 32 0\n-34 31 0\n-34 33 0\n34 0\n-4 35 0\n-18 36 0\n-21 36 0\n-13 37 0\n-9 38 0\n-23 38 0\n-24 39 0\n-22 40 0\n-26 40 0\n-27 40 0\n-11 41 0\n-14 41 0\n-36 42 0\n-35 42 0\n-38 43 0\n-37 43 0\n-43 44 0\n-42 -43 45 0\n-40 46 0\n-39 46 0\n-41 47 0\n-46 48 0\n-46 -47 49 0\n-44 -49 50 0\n-45 -48 50 0\n-50 0\n9 11 13 14 17 20 22 23 24 25 26 27 0\n"
  "64 31 0 36 34 0\n65 33 0 36 35 0\n66 30 0 64 31 0\n67 32 0 65 33 0\n68 28 0 66 30 0\n69 29 0 67 32 0\n70 9 11 13 14 17 22 23 24 26 27 0 24 27 63 0\n71 43 0 24 27 51 52 41 42 40 10 14 15 12 26 13 22 70 0\n72 44 0 71 53 0\n73 -49 0 72 62 60 0\n74 46 0 27 55 56 44 45 46 43 17 16 11 18 25 21 70 0\n75 48 0 74 58 0\n76 -47 0 74 73 59 0\n77 -45 0 75 62 61 0\n78 -41 0 76 57 0\n79 -42 0 77 71 54 0\n80 -11 0 78 47 0\n81 -14 0 78 48 0\n82 -36 0 79 49 0\n83 -35 0 79 50 0\n84 -27 0 81 80 19 0\n85 -18 0 82 38 0\n86 -21 0 82 39 0\n87 -4 0 83 37 0\n88 -10 0 84 9 0\n89 -16 0 87 80 20 81 23 8 0\n90 7 0 89 69 29 0\n91 -1 0 90 1 0\n92 -2 0 90 2 0\n93 -3 0 90 3 0\n94 -5 0 90 4 0\n95 -6 0 90 5 0\n96 -8 0 90 6 0\n97 -19 0 91 92 93 95 85 86 7 0\n98 0 94 96 68 88 97 28 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record026_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc2b4a70f25a8ea36a361d92e1b91e17ae1b46b19c4f16a5693a699c96a5a56352d475a352d2b46d8751d2745d58ce334e332cc7352ccb4acab1ad1b26e2719e1745c570dc4f0bcd8169264381ea84e1a44d13249916625496154341d48c6314d0b12c1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d369a49269b49249b69b4924936924d2492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 60), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 35), (facetIndex 40), (facetIndex 45), (facetIndex 46), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 58), (facetIndex 61)]))
 (.branch 4
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 72), (facetIndex 74)]))
 (.leaf ([(facetIndex 49), (facetIndex 59), (facetIndex 62), (facetIndex 69)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 37), (facetIndex 41), (facetIndex 42), (facetIndex 47)]))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 48), (facetIndex 51)]))
 (.leaf ([(facetIndex 50), (facetIndex 54)]))))
 (.branch 9
 (.leaf ([(facetIndex 63), (facetIndex 66)]))
 (.branch 10
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 71)]))
 (.leaf ([(facetIndex 36), (facetIndex 39)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10030390400800842042000700674651100551a05a129636293z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 55), (facetIndex 57)]))
 (.branch 2
 (.leaf ([(facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 38), (facetIndex 52), (facetIndex 64), (facetIndex 65)]))))
 (.branch 4
 (.leaf ([(facetIndex 73), (facetIndex 78), (facetIndex 79)]))
 (.branch 5
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 56), (facetIndex 67)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 80), (facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "a4d6c5a1800081200000400200000480008z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6, 7]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [6, 7]
def grouped2_0013 : List Nat := [7]
def grouped2_0014 : List Nat := [8]
def grouped2_0015 : List Nat := [8, 9, 10]
def grouped2_0016 : List Nat := [9]
def grouped2_0017 : List Nat := [9, 10]
def grouped2_0018 : List Nat := [10]
def grouped3_0019 : List Nat := [0]
def grouped3_0020 : List Nat := [0, 1, 2]
def grouped3_0022 : List Nat := [1]
def grouped3_0023 : List Nat := [1, 2]
def grouped3_0024 : List Nat := [2]
def grouped3_0025 : List Nat := [3]
def grouped3_0026 : List Nat := [3, 4, 5]
def grouped3_0027 : List Nat := [4]
def grouped3_0028 : List Nat := [4, 5]
def grouped3_0029 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027" "{\"ridges\":[[1,21],[2,37],[12,21],[12,532],[14,37],[14,548],[19,656],[20,224],[21,672],[27,37],[30,21],[31,21],[32,532],[33,37],[34,548],[46,224],[51,532],[53,172],[55,652],[57,21],[57,37],[57,180],[58,548],[59,532],[59,656],[60,548],[61,548],[62,656],[63,224],[65,424],[66,161],[68,672],[69,656],[70,672],[72,22],[74,38],[76,562],[78,170],[81,652],[82,180],[82,532],[82,548],[83,624]],\"owners\":[[72,22,[1,29,30,32,75,76],[22,31,71]],[74,38,[2,29,33,34,75,76],[24,27,73]],[12,532,[76,81,82],[32,51,58,59]],[32,532,[81,82],[12,51,58,59,76]],[51,532,[76,82],[12,32,58,59,81]],[59,532,[76],[12,32,51,58,81,82]],[82,532,[12,32,51],[58,59,76,81]],[14,548,[76,82],[34,58,60,61]],[34,548,[82],[14,58,60,61,76]],[58,548,[],[14,34,60,61,76,82]],[60,548,[76],[14,34,58,61,82]],[61,548,[76,82],[14,34,58,60]],[82,548,[14,34,61],[58,60,76]],[19,656,[81,82,83],[59,62,68,69]],[59,656,[83],[19,62,68,69,81,82]],[62,656,[82,83],[19,59,68,69,81]],[69,656,[81,82],[19,59,62,68,83]],[66,161,[21,38,53,60,65],[20,43,46,57,63,68]],[20,224,[78,80,83],[46,63,66,70]],[46,224,[83],[20,63,66,70,78,80]],[63,224,[80,83],[20,46,66,70,78]],[21,672,[82,83],[60,68,70]],[68,672,[],[21,60,70,82,83]],[70,672,[82],[21,60,68,83]],[78,170,[38],[]],[76,562,[44],[]],[53,172,[],[]],[55,652,[81],[]],[81,652,[55],[]],[57,180,[82],[]],[82,180,[57],[]],[65,424,[],[]],[83,624,[67],[]]],\"edges\":[[23,[12,14,32,34,51,55,58,59,60,61,76,81,82]],[36,[20,21,38,43,46,53,57,60,63,65,66,68,70,78,80,82,83]],[43,[19,21,55,59,60,62,68,69,70,81,82,83]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-15],[-27,-12],[-27,-14],[-27,-23],[-29,-23],[-30,-19],[-31,-27],[-32,-23],[-32,-27],[-33,-17],[-33,-25],[-38,-27],[-47,-9],[-47,-21],[-47,-35],[-47,-42],[-47,-43],[-48,-43],[-1,-3,-27],[-3,-10,-27],[-3,-11,-27],[-40,1,9,10,12,42,43],[-2,-4,-27],[-4,-8,-27],[-4,-13,-27],[-41,2,9,13,14,42,43],[-3,43,46,47],[-12,46,47],[-23,43,47],[-29,43],[-47,3,12,23],[-4,43,47],[-14,47],[-28],[-30,43],[-31,43,47],[-47,4,14,31],[-5,46,47,48],[-29,48],[-32,47,48],[-38,46,47],[-35,7,16,24,30,34],[-6,44,45,48],[-20,48],[-33,45,48],[-7,47,48],[-37],[-39,47],[-44,16],[-43,19],[-24],[-26,46],[-46,26],[-27,47],[-47,27],[-34],[-48,36],[-49,9,14,28,31],[-50,8,11,40,41],[-51,21,29,32,38],[-52,22,25],[-53,33,35],[-54,15,17],[-55,50,51],[-56,49,55],[-57,56],[-58,52],[-59,58],[-60,54],[-61,53],[-61,60],[-62,59],[-62,61],[-63,57,62],[63],[-26,64],[-46,65],[-47,65],[-16,66],[-18,67],[-36,67],[-45,68],[-48,68],[-65,69],[-65,-66,70],[-69,71],[-64,71],[-64,-69,72],[-64,-70,73],[-68,74],[-67,74],[-67,-68,75],[-74,76],[-75,77],[-71,-77,78],[-72,-76,78],[-73,78],[-78],[3,4,12,14,23,26,28,29,30,31,43,46,47],[6,7,16,18,20,24,27,30,33,34,35,37,39,44,45,47,48],[5,7,26,29,30,32,37,38,39,46,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":32},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":51},{\"tag\":\"incompatible\",\"a\":59,\"b\":51},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":51},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":82,\"b\":29},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":66},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":76},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[1,12,57]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[12,30,57]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[12,31,57]},{\"tag\":\"mate\",\"ridge\":22,\"a\":72,\"owners\":[1,29,30,32,75,76]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[2,14,57]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[14,27,57]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[14,33,57]},{\"tag\":\"mate\",\"ridge\":38,\"a\":74,\"owners\":[2,29,33,34,75,76]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[76,81,82]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":532,\"a\":51,\"owners\":[76,82]},{\"tag\":\"mate\",\"ridge\":532,\"a\":59,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":532,\"a\":82,\"owners\":[12,32,51]},{\"tag\":\"mate\",\"ridge\":548,\"a\":14,\"owners\":[76,82]},{\"tag\":\"mate\",\"ridge\":548,\"a\":34,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":548,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":548,\"a\":60,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":548,\"a\":61,\"owners\":[76,82]},{\"tag\":\"mate\",\"ridge\":548,\"a\":82,\"owners\":[14,34,61]},{\"tag\":\"mate\",\"ridge\":656,\"a\":19,\"owners\":[81,82,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":59,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":62,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":161,\"a\":66,\"owners\":[21,38,53,60,65]},{\"tag\":\"mate\",\"ridge\":224,\"a\":20,\"owners\":[78,80,83]},{\"tag\":\"mate\",\"ridge\":224,\"a\":46,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":224,\"a\":63,\"owners\":[80,83]},{\"tag\":\"mate\",\"ridge\":672,\"a\":21,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":672,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":672,\"a\":70,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":170,\"a\":78,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":562,\"a\":76,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":172,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":55,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":652,\"a\":81,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":180,\"a\":57,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":180,\"a\":82,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":424,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":83,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[29,34,58,61],\"full_literals\":[-49,9,14,28,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[27,31,72,74],\"full_literals\":[-50,8,11,40,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[49,59,62,69],\"full_literals\":[-51,21,29,32,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[50,54],\"full_literals\":[-52,22,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[63,66],\"full_literals\":[-53,33,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[36,39],\"full_literals\":[-54,15,17]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,50,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,49,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0010\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-63,57,62],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":55,\"full_literals\":[-26,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-46,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-47,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":38,\"full_literals\":[-16,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":43,\"full_literals\":[-18,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-36,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-45,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-48,68]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-64,-70,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-68,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-71,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[12,14,32,34,51,55,58,59,60,61,76,81,82]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[20,21,38,43,46,53,57,60,63,65,66,68,70,78,80,82,83]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[19,21,55,59,60,62,68,69,70,81,82,83]}]}"
  "p cnf 78 101\n-22 -15 0\n-27 -12 0\n-27 -14 0\n-27 -23 0\n-29 -23 0\n-30 -19 0\n-31 -27 0\n-32 -23 0\n-32 -27 0\n-33 -17 0\n-33 -25 0\n-38 -27 0\n-47 -9 0\n-47 -21 0\n-47 -35 0\n-47 -42 0\n-47 -43 0\n-48 -43 0\n-1 -3 -27 0\n-3 -10 -27 0\n-3 -11 -27 0\n-40 1 9 10 12 42 43 0\n-2 -4 -27 0\n-4 -8 -27 0\n-4 -13 -27 0\n-41 2 9 13 14 42 43 0\n-3 43 46 47 0\n-12 46 47 0\n-23 43 47 0\n-29 43 0\n-47 3 12 23 0\n-4 43 47 0\n-14 47 0\n-28 0\n-30 43 0\n-31 43 47 0\n-47 4 14 31 0\n-5 46 47 48 0\n-29 48 0\n-32 47 48 0\n-38 46 47 0\n-35 7 16 24 30 34 0\n-6 44 45 48 0\n-20 48 0\n-33 45 48 0\n-7 47 48 0\n-37 0\n-39 47 0\n-44 16 0\n-43 19 0\n-24 0\n-26 46 0\n-46 26 0\n-27 47 0\n-47 27 0\n-34 0\n-48 36 0\n-49 9 14 28 31 0\n-50 8 11 40 41 0\n-51 21 29 32 38 0\n-52 22 25 0\n-53 33 35 0\n-54 15 17 0\n-55 50 51 0\n-56 49 55 0\n-57 56 0\n-58 52 0\n-59 58 0\n-60 54 0\n-61 53 0\n-61 60 0\n-62 59 0\n-62 61 0\n-63 57 62 0\n63 0\n-26 64 0\n-46 65 0\n-47 65 0\n-16 66 0\n-18 67 0\n-36 67 0\n-45 68 0\n-48 68 0\n-65 69 0\n-65 -66 70 0\n-69 71 0\n-64 71 0\n-64 -69 72 0\n-64 -70 73 0\n-68 74 0\n-67 74 0\n-67 -68 75 0\n-74 76 0\n-75 77 0\n-71 -77 78 0\n-72 -76 78 0\n-73 78 0\n-78 0\n3 4 12 14 23 26 28 29 30 31 43 46 47 0\n6 7 16 18 20 24 27 30 33 34 35 37 39 44 45 47 48 0\n5 7 26 29 30 32 37 38 39 46 47 48 0\n"
  "102 -49 9 14 31 0 34 58 0\n103 -73 0 98 97 0\n104 3 4 12 14 23 26 29 30 31 43 46 47 0 34 99 0\n105 6 7 16 18 20 27 30 33 35 39 44 45 47 48 0 51 56 47 100 0\n106 5 7 26 29 30 32 38 39 46 47 48 0 47 101 0\n107 -62 35 0 72 73 68 70 71 67 62 69 10 11 63 61 1 0\n108 -30 0 6 35 50 0\n109 -23 71 0 108 86 84 78 48 77 41 87 76 5 8 29 18 38 46 106 0\n110 43 71 0 108 109 86 84 78 33 77 28 87 76 30 27 32 36 104 0\n111 71 0 108 86 87 84 76 77 78 41 48 110 18 39 38 40 46 106 0\n112 -77 0 111 98 95 0\n113 -75 0 112 94 0\n114 48 47 46 0 108 41 48 52 39 38 40 46 106 0\n115 -48 0 113 57 83 81 92 0\n116 -29 0 115 39 0\n117 -20 0 115 44 0\n118 -47 0 75 116 13 14 15 16 17 55 107 2 3 4 7 9 12 74 31 37 102 60 66 19 20 21 23 24 25 65 64 22 26 59 0\n119 -39 0 118 48 0\n120 -27 0 118 54 0\n121 46 0 118 115 114 0\n122 -7 0 118 115 46 0\n123 26 0 121 53 0\n124 65 0 121 77 0\n125 64 0 123 76 0\n126 69 0 124 84 0\n127 -70 0 125 103 89 0\n128 72 0 126 125 88 0\n129 -66 0 127 124 85 0\n130 -76 0 128 98 96 0\n131 -16 0 129 79 0\n132 -74 0 130 93 0\n133 -44 0 131 49 0\n134 -35 0 131 122 51 108 56 42 0\n135 -68 0 132 90 0\n136 -67 0 132 91 0\n137 -45 0 135 82 0\n138 -18 0 136 80 0\n139 -33 0 137 115 45 0\n140 6 0 137 131 122 138 120 108 117 134 119 133 139 118 115 105 0\n141 0 140 137 133 115 43 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc0f45b0ec372b23c9aa3aa9a368e635a362d8763392e2b86e4789e17ae1b46b19c4f15a4e9a64d9596351d54d4b46d47723a8ce3a4cd38ccb31ce8b32d2b2ac6b86d1b26c5b89c6785d1715c3713c2f3605ca8a92269264381e16525194554344d0762348e1342c1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db49b6936db69b4936db6da4d24924d34db69b492492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 56), (facetIndex 65), (facetIndex 77), (facetIndex 83)]))
 (.leaf ([(facetIndex 24), (facetIndex 28), (facetIndex 38), (facetIndex 51), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 78), (facetIndex 82)]))
 (.leaf ([(facetIndex 31), (facetIndex 43), (facetIndex 47), (facetIndex 48)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 25), (facetIndex 49), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 29), (facetIndex 35)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 53), (facetIndex 55)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 66), (facetIndex 67)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "80080000040fc0000000c34323610600040bf87a9b61z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 59), (facetIndex 69), (facetIndex 80)]))
 (.leaf ([(facetIndex 58), (facetIndex 68), (facetIndex 84), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 63)]))
 (.leaf ([(facetIndex 41), (facetIndex 54), (facetIndex 60), (facetIndex 61), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 57), (facetIndex 62), (facetIndex 64)]))
 (.leaf ([(facetIndex 72), (facetIndex 74), (facetIndex 86), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 71), (facetIndex 79), (facetIndex 81)]))
 (.branch 8
 (.leaf ([(facetIndex 75)]))
 (.leaf ([(facetIndex 76)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5511006060087535600100042433014003000000060402322z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5, 6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1]
def grouped3_0009 : List Nat := [0, 1, 2, 3]
def grouped3_0011 : List Nat := [1]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [2, 3]
def grouped3_0014 : List Nat := [3]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0018 : List Nat := [5]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7, 8]
def grouped3_0021 : List Nat := [7]
def grouped3_0022 : List Nat := [7, 8]
def grouped3_0023 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029" "{\"ridges\":[[20,642],[21,162],[21,672],[23,208],[40,649],[44,195],[45,656],[46,224],[47,545],[47,672],[56,208],[57,649],[58,224],[62,177],[63,705],[64,705],[76,224],[77,208],[78,642],[79,106],[80,424],[81,224],[82,162],[82,656],[82,672],[83,208],[84,224],[86,180],[87,224],[87,624]],\"owners\":[[47,545,[54,61],[8,31,43,48,62,64]],[20,642,[21,40,47],[45,78]],[78,642,[21,47],[20,40,45]],[45,656,[87],[20,57,62,63,78,82]],[82,656,[57,63],[20,45,62,78,87]],[21,162,[37,42,46,69,73,76,79,80,81],[47,82]],[82,162,[37,46,69,76,79,80],[21,42,47,73,81]],[21,672,[62,64,87],[47,82]],[47,672,[87],[21,62,64,82]],[82,672,[64],[21,47,62,87]],[23,208,[44,60,63,75,81,86,87],[56,77,83]],[56,208,[75,81,86,87],[23,44,60,63,77,83]],[77,208,[60,63,86,87],[23,44,56,75,81,83]],[83,208,[44,60,63,81,87],[23,56,75,77,86]],[79,106,[36,68],[]],[44,195,[39,46],[]],[40,649,[57],[]],[57,649,[40],[]],[62,177,[42,60],[]],[46,224,[84,86,87],[58,60,64,76,79,81]],[58,224,[76,81,86,87],[46,60,64,79,84]],[76,224,[58,60,64,87],[46,79,81,84,86]],[81,224,[58,64,84],[46,60,76,79,86,87]],[84,224,[46,60,64,81,87],[58,76,79,86]],[87,224,[46,58,76,79,84],[60,64,81,86]],[87,624,[61],[]],[63,705,[64],[]],[64,705,[63],[]],[86,180,[73],[]],[80,424,[],[]]],\"edges\":[[36,[21,37,42,46,47,58,60,62,64,69,73,76,79,80,81,82,84,86,87]],[39,[23,39,44,46,56,58,60,63,64,71,75,76,77,79,81,83,84,86,87]],[43,[20,21,40,45,47,57,62,63,64,78,82,87]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-29,-8],[-29,-25],[-12,13,18],[-1,2,7,12],[-29,2,12],[-10,37],[-33,15,20],[-2,5,8,11,23,25,27,30,31,32],[-33,5,11,23,27,30,31],[-2,19,21,37],[-12,37],[-33,21],[-3,9,17,20,26,32,36,37],[-14,26,32,36,37],[-28,17,20,36,37],[-34,9,17,20,32,37],[-30,4,22],[-9,6,11],[-7,15],[-15,7],[-19,8,17],[-11,35,36,37],[-16,27,32,36,37],[-27,16,17,21,37],[-32,16,21,35],[-35,11,17,21,32,37],[-37,11,16,27,30,35],[-37,18],[-20,21],[-21,20],[-36,25],[-31],[-38,10,29,33],[-39,38],[-40,39],[-41,40],[41],[-4,42],[-5,42],[-23,42],[-16,43],[-22,43],[-35,43],[-6,44],[-7,44],[-8,44],[-20,44],[-13,45],[-17,45],[-18,45],[-25,45],[-15,46],[-19,46],[-21,46],[-37,47],[-11,48],[-24,48],[-30,48],[-32,48],[-26,49],[-27,50],[-43,51],[-42,51],[-45,52],[-44,52],[-52,53],[-51,53],[-51,-52,54],[-47,55],[-46,55],[-50,56],[-49,56],[-56,57],[-48,57],[-55,58],[-55,-57,59],[-53,-59,60],[-54,-58,60],[-60],[2,5,8,11,12,16,17,19,21,23,25,27,30,31,32,33,35,36,37],[3,6,9,11,14,16,17,20,21,24,26,27,28,30,32,34,35,36,37],[1,2,7,10,12,15,19,20,21,29,33,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":78,\"b\":42},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[54,61]},{\"tag\":\"mate\",\"ridge\":642,\"a\":20,\"owners\":[21,40,47]},{\"tag\":\"mate\",\"ridge\":642,\"a\":78,\"owners\":[21,47]},{\"tag\":\"mate\",\"ridge\":656,\"a\":45,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":656,\"a\":82,\"owners\":[57,63]},{\"tag\":\"mate\",\"ridge\":162,\"a\":21,\"owners\":[37,42,46,69,73,76,79,80,81]},{\"tag\":\"mate\",\"ridge\":162,\"a\":82,\"owners\":[37,46,69,76,79,80]},{\"tag\":\"mate\",\"ridge\":672,\"a\":21,\"owners\":[62,64,87]},{\"tag\":\"mate\",\"ridge\":672,\"a\":47,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":672,\"a\":82,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":208,\"a\":23,\"owners\":[44,60,63,75,81,86,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":56,\"owners\":[75,81,86,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":77,\"owners\":[60,63,86,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":83,\"owners\":[44,60,63,81,87]},{\"tag\":\"mate\",\"ridge\":106,\"a\":79,\"owners\":[36,68]},{\"tag\":\"mate\",\"ridge\":195,\"a\":44,\"owners\":[39,46]},{\"tag\":\"mate\",\"ridge\":649,\"a\":40,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":649,\"a\":57,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":177,\"a\":62,\"owners\":[42,60]},{\"tag\":\"mate\",\"ridge\":224,\"a\":46,\"owners\":[84,86,87]},{\"tag\":\"mate\",\"ridge\":224,\"a\":58,\"owners\":[76,81,86,87]},{\"tag\":\"mate\",\"ridge\":224,\"a\":76,\"owners\":[58,60,64,87]},{\"tag\":\"mate\",\"ridge\":224,\"a\":81,\"owners\":[58,64,84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":84,\"owners\":[46,60,64,81,87]},{\"tag\":\"mate\",\"ridge\":224,\"a\":87,\"owners\":[46,58,76,79,84]},{\"tag\":\"mate\",\"ridge\":624,\"a\":87,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":705,\"a\":63,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":705,\"a\":64,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":180,\"a\":86,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":424,\"a\":80,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[45,78,82],\"full_literals\":[-38,10,29,33]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":36,\"full_literals\":[-4,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":37,\"full_literals\":[-5,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":58,\"full_literals\":[-16,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-22,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-35,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":39,\"full_literals\":[-6,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":40,\"full_literals\":[-7,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":42,\"full_literals\":[-8,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-20,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":54,\"full_literals\":[-13,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-17,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":61,\"full_literals\":[-18,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-25,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":57,\"full_literals\":[-15,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":62,\"full_literals\":[-19,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-21,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-37,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-11,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-24,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-30,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-32,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-26,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-27,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[21,37,42,46,47,58,60,62,64,69,73,76,79,80,81,82,84,86,87]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[23,39,44,46,56,58,60,63,64,71,75,76,77,79,81,83,84,86,87]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,21,40,45,47,57,62,63,64,78,82,87]}]}"
  "p cnf 60 82\n-29 -8 0\n-29 -25 0\n-12 13 18 0\n-1 2 7 12 0\n-29 2 12 0\n-10 37 0\n-33 15 20 0\n-2 5 8 11 23 25 27 30 31 32 0\n-33 5 11 23 27 30 31 0\n-2 19 21 37 0\n-12 37 0\n-33 21 0\n-3 9 17 20 26 32 36 37 0\n-14 26 32 36 37 0\n-28 17 20 36 37 0\n-34 9 17 20 32 37 0\n-30 4 22 0\n-9 6 11 0\n-7 15 0\n-15 7 0\n-19 8 17 0\n-11 35 36 37 0\n-16 27 32 36 37 0\n-27 16 17 21 37 0\n-32 16 21 35 0\n-35 11 17 21 32 37 0\n-37 11 16 27 30 35 0\n-37 18 0\n-20 21 0\n-21 20 0\n-36 25 0\n-31 0\n-38 10 29 33 0\n-39 38 0\n-40 39 0\n-41 40 0\n41 0\n-4 42 0\n-5 42 0\n-23 42 0\n-16 43 0\n-22 43 0\n-35 43 0\n-6 44 0\n-7 44 0\n-8 44 0\n-20 44 0\n-13 45 0\n-17 45 0\n-18 45 0\n-25 45 0\n-15 46 0\n-19 46 0\n-21 46 0\n-37 47 0\n-11 48 0\n-24 48 0\n-30 48 0\n-32 48 0\n-26 49 0\n-27 50 0\n-43 51 0\n-42 51 0\n-45 52 0\n-44 52 0\n-52 53 0\n-51 53 0\n-51 -52 54 0\n-47 55 0\n-46 55 0\n-50 56 0\n-49 56 0\n-56 57 0\n-48 57 0\n-55 58 0\n-55 -57 59 0\n-53 -59 60 0\n-54 -58 60 0\n-60 0\n2 5 8 11 12 16 17 19 21 23 25 27 30 31 32 33 35 36 37 0\n3 6 9 11 14 16 17 20 21 24 26 27 28 30 32 34 35 36 37 0\n1 2 7 10 12 15 19 20 21 29 33 37 0\n"
  "83 40 0 37 36 0\n84 39 0 83 35 0\n85 38 0 84 34 0\n86 2 5 8 11 12 16 17 19 21 23 25 27 30 32 33 35 36 37 0 32 80 0\n87 53 0 32 66 67 64 65 62 63 48 49 50 51 45 46 47 41 42 43 38 39 40 21 28 3 31 20 30 7 24 25 22 17 8 86 0\n88 -59 0 87 79 77 0\n89 55 0 69 70 55 52 53 54 6 11 19 10 12 29 4 5 82 0\n90 58 0 89 75 0\n91 -57 0 89 88 76 0\n92 -54 0 90 79 78 0\n93 -56 0 91 73 0\n94 -48 0 91 74 0\n95 -50 0 93 71 0\n96 -49 0 93 72 0\n97 -11 0 94 56 0\n98 -24 0 94 57 0\n99 -30 0 94 58 0\n100 -32 0 94 59 0\n101 -27 0 95 61 0\n102 -26 0 96 60 0\n103 52 0 100 99 101 102 98 97 64 65 49 50 51 44 47 28 31 18 30 23 14 15 13 16 26 81 0\n104 -51 0 103 92 68 0\n105 -43 0 104 62 0\n106 -42 0 104 63 0\n107 -16 0 105 41 0\n108 -35 0 105 43 0\n109 -5 0 106 39 0\n110 -23 0 106 40 0\n111 -37 0 107 97 101 99 108 27 0\n112 -33 0 109 97 110 101 99 32 9 0\n113 -10 0 111 6 0\n114 -12 0 111 11 0\n115 29 0 112 85 113 33 0\n116 -8 0 115 1 0\n117 -25 0 115 2 0\n118 2 0 115 114 5 0\n119 0 118 116 109 97 110 117 101 99 32 100 8 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record029

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b62b8ab332b2aaa96a3aa98e6559361da8e33a2e2b91e1783eac4f1aa699366392e5a5395554d4752b51d1743da8ce354e331ce8b32e2b2ae1b46c3b51cc729c6745c570dd0f23c2f07ccc8c9328685a4984e4c4c9164c5494a52344d48d1314c3312c1b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6d26da6d36d36db4da4d34d36d24d3692492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 50), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 60), (facetIndex 62), (facetIndex 83)]))
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 46), (facetIndex 70), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 47), (facetIndex 67), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 40), (facetIndex 68), (facetIndex 78), (facetIndex 82)])))
 (.branch 7
 (.leaf ([(facetIndex 58), (facetIndex 81)]))
 (.leaf ([(facetIndex 61), (facetIndex 63)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "5707409082c5841eba1900000008c00c56z1d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7]
def grouped3_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040" "{\"ridges\":[[21,536],[23,546],[38,536],[40,553],[42,643],[42,648],[47,643],[60,648],[60,657],[61,648],[61,672],[63,560],[63,657],[68,556],[70,646],[70,648],[75,646],[76,546],[76,560],[77,536],[78,648],[78,672],[79,706],[80,546],[81,556],[81,648],[82,648],[82,672],[83,720]],\"owners\":[[21,536,[58,60,82,83],[38,76,77]],[38,536,[82,83],[21,58,60,76,77]],[77,536,[58,60,82],[21,38,76,83]],[23,546,[40,47,68,75,78],[44,76,80]],[76,546,[47,75],[23,40,44,68,78,80]],[80,546,[40,47,68,75,78],[23,44,76]],[63,560,[23,76,80],[44,58,82]],[76,560,[63],[23,44,58,80,82]],[40,553,[58,61],[]],[42,643,[47],[]],[47,643,[42],[]],[42,648,[81,82,83],[60,61,70,78,79]],[60,648,[70,78,79,81],[42,61,82,83]],[61,648,[70,79,83],[42,60,78,81,82]],[70,648,[60,61,82,83],[42,78,79,81]],[78,648,[60,83],[42,61,70,79,81,82]],[81,648,[42,60,79,83],[61,70,78,82]],[82,648,[42,70,79],[60,61,78,81,83]],[61,672,[75],[47,63,78,81,82]],[78,672,[63],[47,61,75,81,82]],[82,672,[47,75],[61,63,78,81]],[60,657,[63],[]],[63,657,[60],[]],[68,556,[81],[]],[81,556,[68],[]],[70,646,[75],[]],[75,646,[70],[]],[79,706,[],[]],[83,720,[],[]]],\"edges\":[[29,[21,38,40,42,58,60,61,68,70,76,77,78,79,81,82,83]],[43,[42,47,60,61,63,70,75,78,79,81,82,83]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,7,8,20,21],[-3,20,21],[-15,7,8,20],[-2,4,6,11,13,16],[-14,6,13],[-18,4,6,11,13,16],[-10,2,14,18],[-14,10],[-4,7,9],[-5,6],[-6,5],[-5,19,20,21],[-8,12,16,17,19],[-9,12,17,21],[-12,8,9,20,21],[-16,8,21],[-19,5,8,17,21],[-20,5,12,17],[-9,13],[-16,10],[-20,6,13],[-8,10],[-10,8],[-11,19],[-19,11],[-12,13],[-13,12],[-17],[-21],[-8,22],[-5,23],[-12,23],[-6,24],[-13,24],[-4,25],[-11,25],[-16,25],[-20,25],[-7,26],[-19,26],[-9,27],[-10,27],[-23,28],[-22,28],[-28,29],[-25,30],[-24,30],[-24,-25,31],[-27,32],[-26,32],[-30,-32,33],[-31,33],[-29,-33,34],[-34],[1,3,4,5,7,8,9,11,12,14,15,16,17,19,20,21],[5,6,8,9,10,12,13,16,17,19,20,21]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":536,\"a\":21,\"owners\":[58,60,82,83]},{\"tag\":\"mate\",\"ridge\":536,\"a\":38,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":536,\"a\":77,\"owners\":[58,60,82]},{\"tag\":\"mate\",\"ridge\":546,\"a\":23,\"owners\":[40,47,68,75,78]},{\"tag\":\"mate\",\"ridge\":546,\"a\":76,\"owners\":[47,75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":80,\"owners\":[40,47,68,75,78]},{\"tag\":\"mate\",\"ridge\":560,\"a\":63,\"owners\":[23,76,80]},{\"tag\":\"mate\",\"ridge\":560,\"a\":76,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":553,\"a\":40,\"owners\":[58,61]},{\"tag\":\"mate\",\"ridge\":643,\"a\":42,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":643,\"a\":47,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":648,\"a\":42,\"owners\":[81,82,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":60,\"owners\":[70,78,79,81]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[70,79,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":70,\"owners\":[60,61,82,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":78,\"owners\":[60,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":81,\"owners\":[42,60,79,83]},{\"tag\":\"mate\",\"ridge\":648,\"a\":82,\"owners\":[42,70,79]},{\"tag\":\"mate\",\"ridge\":672,\"a\":61,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":672,\"a\":78,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":672,\"a\":82,\"owners\":[47,75]},{\"tag\":\"mate\",\"ridge\":657,\"a\":60,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":657,\"a\":63,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":556,\"a\":68,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":556,\"a\":81,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":646,\"a\":70,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":646,\"a\":75,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":706,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":720,\"a\":83,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":60,\"full_literals\":[-8,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":42,\"full_literals\":[-5,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-12,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":47,\"full_literals\":[-6,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-13,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-4,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":68,\"full_literals\":[-11,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-20,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":58,\"full_literals\":[-7,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":61,\"full_literals\":[-9,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":63,\"full_literals\":[-10,27]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-23,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-25,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[21,38,40,42,58,60,61,68,70,76,77,78,79,81,82,83]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[42,47,60,61,63,70,75,78,79,81,82,83]}]}"
  "p cnf 34 56\n-1 7 8 20 21 0\n-3 20 21 0\n-15 7 8 20 0\n-2 4 6 11 13 16 0\n-14 6 13 0\n-18 4 6 11 13 16 0\n-10 2 14 18 0\n-14 10 0\n-4 7 9 0\n-5 6 0\n-6 5 0\n-5 19 20 21 0\n-8 12 16 17 19 0\n-9 12 17 21 0\n-12 8 9 20 21 0\n-16 8 21 0\n-19 5 8 17 21 0\n-20 5 12 17 0\n-9 13 0\n-16 10 0\n-20 6 13 0\n-8 10 0\n-10 8 0\n-11 19 0\n-19 11 0\n-12 13 0\n-13 12 0\n-17 0\n-21 0\n-8 22 0\n-5 23 0\n-12 23 0\n-6 24 0\n-13 24 0\n-4 25 0\n-11 25 0\n-16 25 0\n-20 25 0\n-7 26 0\n-19 26 0\n-9 27 0\n-10 27 0\n-23 28 0\n-22 28 0\n-28 29 0\n-25 30 0\n-24 30 0\n-24 -25 31 0\n-27 32 0\n-26 32 0\n-30 -32 33 0\n-31 33 0\n-29 -33 34 0\n-34 0\n1 3 4 5 7 8 9 11 12 14 15 16 17 19 20 21 0\n5 6 8 9 10 12 13 16 17 19 20 21 0\n"
  "57 1 3 4 5 7 8 9 11 12 14 15 16 19 20 0 28 29 55 0\n58 5 6 8 9 10 12 13 16 19 20 0 28 29 56 0\n59 28 0 29 28 43 44 31 32 30 11 18 14 27 16 23 17 58 0\n60 29 0 59 45 0\n61 -33 0 60 54 53 0\n62 -31 0 61 52 0\n63 30 0 28 46 47 35 36 37 38 33 34 4 25 6 5 10 19 26 7 13 58 0\n64 -32 0 63 61 51 0\n65 -27 0 64 49 0\n66 -26 0 64 50 0\n67 -9 0 65 41 0\n68 -10 0 65 42 0\n69 -7 0 66 39 0\n70 -19 0 66 40 0\n71 -14 0 68 8 0\n72 -16 0 68 20 0\n73 -8 0 68 22 0\n74 -4 0 69 67 9 0\n75 -11 0 70 24 0\n76 20 0 29 70 72 71 75 67 73 69 74 2 1 12 15 3 57 0\n77 25 0 76 38 0\n78 -24 0 77 62 48 0\n79 -6 0 78 33 0\n80 -13 0 78 34 0\n81 0 79 80 76 21 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record040_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record040

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b62b8ab23a399564d876338ae4785e0fad1cc6b13c6c9aa699964d98e4b9a95a5395554d475a362d2b51d1743d38d538cc7332e2b2ae1b46c3b51cc729c6745c570dd0f23c2f07ccc4c85a4984ea86314c68932619164c5494a52344d48d1314c3312c1b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6d34da6d26924934934d34d36924da492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 49), (facetIndex 72), (facetIndex 75)]))
 (.leaf ([(facetIndex 35), (facetIndex 51), (facetIndex 57), (facetIndex 58), (facetIndex 59)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 61), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 55), (facetIndex 77)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 44), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 30), (facetIndex 34), (facetIndex 36), (facetIndex 37)]))
 (.leaf ([(facetIndex 53), (facetIndex 65)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1800001213c910248638200155005b7639b7b66z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041" "{\"atoms\":[{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041" 15

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041" "{\"ridges\":[[53,648],[65,672],[82,184]],\"owners\":[[53,648,[82,83],[18,64,65,66,81]],[65,672,[],[21,59,68,81,82]],[82,184,[60],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,-1],[-3,-1],[-5,-1],[-7,-1],[-9,-4],[-1,8,9],[-6],[-8,2],[-10,3,4,5,7],[-11,1,6],[-12,10],[-13,11],[-14,12],[-14,13],[-15,14],[15]],\"atoms\":[{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":64,\"b\":53},{\"tag\":\"incompatible\",\"a\":66,\"b\":53},{\"tag\":\"incompatible\",\"a\":83,\"b\":63},{\"tag\":\"mate\",\"ridge\":648,\"a\":53,\"owners\":[82,83]},{\"tag\":\"mate\",\"ridge\":672,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":184,\"a\":82,\"owners\":[60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[62,63,64,66],\"full_literals\":[-10,3,4,5,7]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[53,65],\"full_literals\":[-11,1,6]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-12,10,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-13,false,11],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-14,12,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-14,false,13],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-15,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 15 16\n-2 -1 0\n-3 -1 0\n-5 -1 0\n-7 -1 0\n-9 -4 0\n-1 8 9 0\n-6 0\n-8 2 0\n-10 3 4 5 7 0\n-11 1 6 0\n-12 10 0\n-13 11 0\n-14 12 0\n-14 13 0\n-15 14 0\n15 0\n"
  "17 -11 1 0 7 10 0\n18 14 0 16 15 0\n19 12 0 18 13 0\n20 13 0 18 14 0\n21 10 0 19 11 0\n22 11 0 20 12 0\n23 1 0 22 17 0\n24 -2 0 23 1 0\n25 -3 0 23 2 0\n26 -5 0 23 3 0\n27 -7 0 23 4 0\n28 -8 0 24 8 0\n29 4 0 25 21 26 27 9 0\n30 9 0 28 23 6 0\n31 0 30 29 5 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00097.record041_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00097.record041
