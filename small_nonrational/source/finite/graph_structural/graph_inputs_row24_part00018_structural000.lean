module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00018Data
public import GraphInputsRow24Part00018Frames
public import GraphInputsRow24Part00018Leaves
public import GraphInputsRow24Part00018Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record050
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050
def vertexColumn : Fields := ⟨10, hexnat% "dc6c8da2eb46c996635a4e33a2e1ba1e2785e0f9b1e2749727296a569364b9d1725594d5934cd8b46d8749d17783d0f2368d6364cd34ccb3a2e4b32e2b2ac6b86c9b16c3bc1e4751cc789d2719e1725c5783c8f13c2f07c3c70836704c9264390d60d1342d0770360d4330d2324c3381c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6d36d36d26db4924924924926d36da6924924924d2449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2204000200000000000", hexnat% "2000000001400b800000", hexnat% "100021000000000000", 133419138960850944, 13690942867206307840, 256892731392, 1125917623582720]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record050_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record050

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record058
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058
def vertexColumn : Fields := ⟨10, hexnat% "1e47531c671e2d48eac687a719a6598e6c59561db0e638ae8791e0fb51744e936479714e5c5595554d51d61d2743dd0dc338f1394d531cccb8acab1ac5b0ef0761d4731ca719e1745c570de0f23cacc4952869160b81e384a9864a52342d0746384c5382c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4d36db49b6924da6da6db6926d24934924db692492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180010af87f800000", 1688849860263936, hexnat% "40000200000000000", 1224979098644774912, hexnat% "80c00000140000000000", hexnat% "20020000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1970324895694848, 1225014558968512512, hexnat% "48000000000000000", 722091376640, hexnat% "a0c10000000000000000", 15462217809920, hexnat% "20000100008000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record058_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record058

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e60ec2f1e2748eac699a2eb165586e8783e78791747893a719a65992e74539715554d52d4cd8b4ad1b49d0f5c368d6338f1364d5334cb3c2d8b32cab1ae1b46c9b0ef0751e1745c570de0f13e1c1982e079c138711644a986499196158342d0754318d130ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6924934924d26db49249a4926db692493492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 59), (facetIndex 62)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 85)]))
 (.leaf ([(facetIndex 56), (facetIndex 57), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 43), (facetIndex 49)])))
 (.branch 7
 (.leaf ([(facetIndex 77), (facetIndex 80), (facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 75), (facetIndex 76)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "149b64b7e000010000000db000028000b49az1d;"⟩
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
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054" "{\"ridges\":[[8,322],[18,769],[19,224],[20,448],[31,322],[44,322],[46,784],[47,224],[48,322],[50,448],[56,204],[58,212],[59,340],[60,784],[61,224],[62,836],[66,769],[67,168],[69,448],[70,769],[71,224],[71,448],[76,774],[77,178],[80,202],[81,210],[82,418]],\"owners\":[[8,322,[75,81,82],[31,44,48,50]],[31,322,[81,82],[8,44,48,50,75]],[44,322,[82],[8,31,48,50,75,81]],[48,322,[75,81],[8,31,44,50,82]],[67,168,[77,83],[16,38,54,63,80,84]],[18,769,[32,41,62,68],[46,60,66,70]],[66,769,[32,62],[18,41,46,60,68,70]],[70,769,[32,41,62],[18,46,60,66,68]],[46,784,[85],[18,60,66,70,76,79]],[60,784,[79,85],[18,46,66,70,76]],[19,224,[80,82,84],[47,61,67,71]],[47,224,[84],[19,61,67,71,80,82]],[61,224,[80,82],[19,47,67,71,84]],[71,224,[80,84],[19,47,61,67,82]],[20,448,[81,82],[50,69,71]],[50,448,[],[20,69,71,81,82]],[69,448,[82],[20,50,71,81]],[71,448,[81],[20,50,69,82]],[76,774,[32],[]],[80,202,[39],[]],[77,178,[42],[]],[81,210,[43],[]],[82,418,[49],[]],[56,204,[84],[]],[58,212,[],[]],[59,340,[75],[]],[62,836,[],[]]],\"edges\":[[39,[19,20,39,43,47,50,56,58,61,67,69,71,80,81,82,84]],[40,[8,20,31,44,48,50,59,62,69,71,75,81,82]],[44,[18,32,41,46,60,62,66,68,70,76,79,85]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,29,34,35],[-5,34,35],[-11,35],[-14,29,34],[-24,31,36],[-2,6,8,22,25],[-23,6,22],[-27,6,8,22],[-12,38],[-20,32,38],[-3,33,35,37],[-13,37],[-21,33,35],[-28,33,37],[-4,34,35],[-16],[-26,35],[-28,34],[-30,6],[-33,7],[-31,9],[-34,10],[-35,15],[-17,37],[-18],[-19,29],[-22],[-6,39],[-8,40],[-25,40],[-32,41],[-38,41],[-36,42],[-37,42],[-7,43],[-9,43],[-10,43],[-15,43],[-34,44],[-35,44],[-29,45],[-40,46],[-39,46],[-41,47],[-47,48],[-46,48],[-43,49],[-42,49],[-45,50],[-44,50],[-49,-50,51],[-48,-51,52],[-52],[3,4,7,10,13,16,17,18,21,24,26,28,33,34,35,37],[1,4,5,11,14,16,19,22,26,28,29,34,35],[2,6,8,12,20,22,23,25,27,30,32,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":322,\"a\":8,\"owners\":[75,81,82]},{\"tag\":\"mate\",\"ridge\":322,\"a\":31,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":322,\"a\":44,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":322,\"a\":48,\"owners\":[75,81]},{\"tag\":\"mate\",\"ridge\":168,\"a\":67,\"owners\":[77,83]},{\"tag\":\"mate\",\"ridge\":769,\"a\":18,\"owners\":[32,41,62,68]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[32,62]},{\"tag\":\"mate\",\"ridge\":769,\"a\":70,\"owners\":[32,41,62]},{\"tag\":\"mate\",\"ridge\":784,\"a\":46,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":784,\"a\":60,\"owners\":[79,85]},{\"tag\":\"mate\",\"ridge\":224,\"a\":19,\"owners\":[80,82,84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":47,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":224,\"a\":61,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":224,\"a\":71,\"owners\":[80,84]},{\"tag\":\"mate\",\"ridge\":448,\"a\":20,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":448,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":448,\"a\":69,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":448,\"a\":71,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":774,\"a\":76,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":202,\"a\":80,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":178,\"a\":77,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":210,\"a\":81,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":418,\"a\":82,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":204,\"a\":56,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":212,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":59,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":836,\"a\":62,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-6,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":41,\"full_literals\":[-8,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":68,\"full_literals\":[-25,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-32,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-38,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-36,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-37,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":39,\"full_literals\":[-7,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":42,\"full_literals\":[-9,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":43,\"full_literals\":[-10,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":49,\"full_literals\":[-15,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-34,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-35,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-29,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-48,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[19,20,39,43,47,50,56,58,61,67,69,71,80,81,82,84]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[8,20,31,44,48,50,59,62,69,71,75,81,82]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[18,32,41,46,60,62,66,68,70,76,79,85]}]}"
  "p cnf 52 56\n-1 29 34 35 0\n-5 34 35 0\n-11 35 0\n-14 29 34 0\n-24 31 36 0\n-2 6 8 22 25 0\n-23 6 22 0\n-27 6 8 22 0\n-12 38 0\n-20 32 38 0\n-3 33 35 37 0\n-13 37 0\n-21 33 35 0\n-28 33 37 0\n-4 34 35 0\n-16 0\n-26 35 0\n-28 34 0\n-30 6 0\n-33 7 0\n-31 9 0\n-34 10 0\n-35 15 0\n-17 37 0\n-18 0\n-19 29 0\n-22 0\n-6 39 0\n-8 40 0\n-25 40 0\n-32 41 0\n-38 41 0\n-36 42 0\n-37 42 0\n-7 43 0\n-9 43 0\n-10 43 0\n-15 43 0\n-34 44 0\n-35 44 0\n-29 45 0\n-40 46 0\n-39 46 0\n-41 47 0\n-47 48 0\n-46 48 0\n-43 49 0\n-42 49 0\n-45 50 0\n-44 50 0\n-49 -50 51 0\n-48 -51 52 0\n-52 0\n3 4 7 10 13 16 17 18 21 24 26 28 33 34 35 37 0\n1 4 5 11 14 16 19 22 26 28 29 34 35 0\n2 6 8 12 20 22 23 25 27 30 32 38 0\n"
  "57 3 4 7 10 13 17 21 24 26 28 33 34 35 37 0 16 25 54 0\n58 1 4 5 11 14 19 26 28 29 34 35 0 16 27 55 0\n59 2 6 8 12 20 23 25 27 30 32 38 0 27 56 0\n60 48 0 27 45 46 44 42 43 31 32 29 30 28 9 10 8 6 7 19 59 0\n61 -51 0 60 53 52 0\n62 49 0 47 48 35 36 37 38 33 34 20 21 22 23 12 24 14 5 17 11 13 15 57 0\n63 -50 0 62 61 51 0\n64 -45 0 63 49 0\n65 -44 0 63 50 0\n66 -29 0 64 41 0\n67 -34 0 65 39 0\n68 -35 0 65 40 0\n69 -14 0 66 67 4 0\n70 -19 0 66 26 0\n71 -1 0 66 67 68 1 0\n72 -5 0 67 68 2 0\n73 -28 0 67 18 0\n74 -11 0 68 3 0\n75 -26 0 68 17 0\n76 -4 0 68 67 15 0\n77 0 74 76 71 72 69 70 75 73 66 67 68 58 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00018.record054_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00018.record054
