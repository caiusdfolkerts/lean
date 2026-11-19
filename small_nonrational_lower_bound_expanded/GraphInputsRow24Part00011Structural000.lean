module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00011Data
public import GraphInputsRow24Part00011Frames
public import GraphInputsRow24Part00011Leaves
public import GraphInputsRow24Part00011Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 261718127149056, 148619337459040256, (certNat% 3), (certNat% 4), 562949953421312]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 306596618382082048, (certNat% 6), 66039417143296, (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 144295542342549504, (certNat% 10), (certNat% 11), 79233556676608]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 414331165718085632, 148623185749737472, (certNat% 14), (certNat% 15), 114452288503808]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record060
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060
def vertexColumn : Fields := ⟨10, (certNat% 16)⟩
def kindColumn : Fields := ⟨3, (certNat% 17)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21), 5071497517334528, (certNat% 22), (certNat% 23)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record060_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record060

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f0b4ab2aaa3aa9a368ba398d62db0e5386e17bc1d26c9aa4e9a64d92e4e5354b5c354d1b45de0f43b0dc3a8ce3a4cd3c2e8b92d4b32e2b2ac6b86c9b16f0731d2729c6745c9715e0f43c3c2c83a518361382e078b10e5450d44d0b41dc0e8350cc328c930ce0b12c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db69b4d24db6db4da692492492492492492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 39), (facetIndex 64), (facetIndex 79)]))
 (.leaf ([(facetIndex 42), (facetIndex 45), (facetIndex 47), (facetIndex 50), (facetIndex 67), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 60), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 40), (facetIndex 58)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 59)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 48), (facetIndex 49), (facetIndex 51)]))
 (.leaf ([(facetIndex 33), (facetIndex 36)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4001b600000200092b2db6dc7638ec7410783e4z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 73)]))
 (.leaf ([(facetIndex 78), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 72), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 87), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 85), (facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "29bffe240400c3db609z31;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [4, 5]
def grouped3_0018 : List Nat := [4, 5, 6, 7]
def grouped3_0019 : List Nat := [6]
def grouped3_0020 : List Nat := [6, 7]
def grouped3_0021 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008" "{\"ridges\":[[14,641],[15,770],[40,770],[50,641],[51,769],[53,641],[55,641],[57,642],[58,770],[59,641],[59,770],[69,664],[71,680],[83,216],[84,664],[85,232],[86,680],[87,712],[89,960]],\"owners\":[[14,641,[69,71,72,74],[50,53,55,57,59]],[50,641,[74],[14,53,55,57,59,69,71,72]],[53,641,[71,72,74],[14,50,55,57,59,69]],[55,641,[69,72,74],[14,50,53,57,59,71]],[59,641,[69,71,72],[14,50,53,55,57,74]],[57,642,[84,86],[14,50,53,55,59,87,89]],[51,769,[74],[15,40,58,59,63,73]],[15,770,[78,88,89],[40,51,58,59]],[40,770,[88,89],[15,51,58,59,78]],[58,770,[78],[15,40,51,59,88,89]],[59,770,[78,88],[15,40,51,58,89]],[83,216,[68],[]],[69,664,[84],[]],[84,664,[69],[]],[85,232,[70],[]],[71,680,[86],[]],[86,680,[71],[]],[87,712,[72],[]],[89,960,[74],[]]],\"edges\":[[43,[14,50,53,55,57,59,69,71,72,74,84,86,87,89]],[44,[15,40,51,58,59,63,73,74,78,88,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-4,-3],[-5,-4],[-6,-3],[-6,-5],[-7,-3],[-7,-5],[-20,-13],[-22,-13],[-1,17,19,20,22],[-8,22],[-10,19,20,22],[-11,17,20,22],[-14,17,19,20],[-12,25,27],[-9,22],[-2,23,29,30],[-7,29,30],[-13,23],[-14,23,29],[-24,16],[-17,25],[-25,17],[-26,18],[-19,27],[-27,19],[-28,20],[-30,22],[-31,4,6,7,13],[-32,3,5],[-33,31],[-34,32],[-35,33],[-35,34],[-36,35],[36],[-15,37],[-21,37],[-23,38],[-29,38],[-39,20,22],[-20,39],[-22,39],[-16,40],[-17,40],[-18,40],[-19,40],[-41,24,25,26,27],[-25,41],[-27,41],[-38,42],[-37,42],[-39,43],[-43,44],[-42,44],[-40,-41,45],[-45,46],[-44,-46,47],[-47],[1,8,10,11,12,14,17,19,20,22,25,27,28,30],[2,7,9,13,14,15,21,22,23,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":33},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":72,\"b\":58},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"mate\",\"ridge\":641,\"a\":14,\"owners\":[69,71,72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":53,\"owners\":[71,72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[69,72,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[69,71,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[84,86]},{\"tag\":\"mate\",\"ridge\":769,\"a\":51,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":770,\"a\":15,\"owners\":[78,88,89]},{\"tag\":\"mate\",\"ridge\":770,\"a\":40,\"owners\":[88,89]},{\"tag\":\"mate\",\"ridge\":770,\"a\":58,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":770,\"a\":59,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":216,\"a\":83,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":664,\"a\":69,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":664,\"a\":84,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":232,\"a\":85,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":680,\"a\":71,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":680,\"a\":86,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":712,\"a\":87,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":960,\"a\":89,\"owners\":[74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,38,40,58],\"full_literals\":[-31,4,6,7,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[33,36],\"full_literals\":[-32,3,5]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-35,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-15,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-21,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-29,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[72,74],\"full_literals\":[-39,20,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-20,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-22,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-16,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-17,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-18,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-19,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[83,84,85,86],\"full_literals\":[-41,24,25,26,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-25,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-27,41]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-41,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,50,53,55,57,59,69,71,72,74,84,86,87,89]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[15,40,51,58,59,63,73,74,78,88,89]}]}"
  "61 35 0 35 34 0\n62 33 0 61 32 0\n63 34 0 61 33 0\n64 31 0 62 30 0\n65 32 0 63 31 0\n66 44 0 53 54 52 50 51 42 38 39 36 37 15 27 16 18 17 19 60 0\n67 -46 0 66 58 57 0\n68 -45 0 67 56 0\n69 -41 0 68 55 43 44 45 46 20 22 23 25 47 0\n70 -25 0 69 48 0\n71 -27 0 69 49 0\n72 -12 0 70 71 14 0\n73 -17 0 70 21 0\n74 -19 0 71 24 0\n75 39 0 71 70 74 73 72 41 42 26 9 12 13 11 10 27 59 0\n76 -4 0 65 1 2 29 0\n77 -6 0 65 3 4 29 0\n78 -7 0 65 5 6 29 0\n79 13 0 78 64 76 77 28 0\n80 -20 0 79 7 0\n81 -22 0 79 8 0\n82 0 80 81 75 40 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "178e315c3a95a1ea96558b6538ae4785e0fb51ac571e25693a5594e479e1695554b5c368d6354d2b51d1743d38e9354cb352ccb46c5b0ee8751ca785d1725c570dd0f13c2f07f141c8aa1a88ec45511c5492a469c1685855154348d28c6314c3322c4b0ac8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db4d36da6da69a49a49349249b4d249a49a492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 57), (facetIndex 62), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 28), (facetIndex 36), (facetIndex 42), (facetIndex 51), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 54), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 31), (facetIndex 39), (facetIndex 44), (facetIndex 47)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 77), (facetIndex 79)]))
 (.leaf ([(facetIndex 43), (facetIndex 60), (facetIndex 63), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 50), (facetIndex 52), (facetIndex 53), (facetIndex 55)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35)]))
 (.leaf ([(facetIndex 29), (facetIndex 40)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "40400001000000055005220062661600300351083201777736817z1b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65)]))
 (.leaf ([(facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 46), (facetIndex 56), (facetIndex 67)]))
 (.leaf ([(facetIndex 74), (facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 41), (facetIndex 49)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 75), (facetIndex 78), (facetIndex 80)]))
 (.branch 8
 (.leaf ([(facetIndex 48), (facetIndex 61)]))
 (.leaf ([(facetIndex 69), (facetIndex 82)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8160603635055802000007000020000004702000040004z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8]
def grouped2_0012 : List Nat := [8]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7, 8]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8]
def grouped3_0029 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058" 62

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058" "{\"ridges\":[[14,644],[18,328],[20,336],[37,326],[38,644],[43,328],[45,336],[48,60],[52,328],[54,644],[57,336],[58,644],[59,644],[61,312],[62,336],[64,328],[66,336],[67,688],[68,336],[69,60],[73,326],[75,326],[78,282],[80,92],[82,312]],\"owners\":[[14,644,[76,81],[38,54,58,59]],[38,644,[81],[14,54,58,59,76]],[54,644,[76],[14,38,58,59,81]],[58,644,[81],[14,38,54,59,76]],[59,644,[76],[14,38,54,58,81]],[18,328,[73,78,80,82],[43,52,62,64]],[43,328,[80,82],[18,52,62,64,73,78]],[52,328,[78,82],[18,43,62,64,73,80]],[64,328,[73,78,80],[18,43,52,62,82]],[20,336,[75,78,80,82],[45,57,62,66,68]],[45,336,[80,82],[20,57,62,66,68,75,78]],[57,336,[78,82],[20,45,62,66,68,75,80]],[62,336,[75],[20,45,57,66,68,78,80,82]],[66,336,[75,78,80],[20,45,57,62,68,82]],[68,336,[75,78,80,82],[20,45,57,62,66]],[37,326,[73,75],[]],[73,326,[37,75],[]],[75,326,[37,73],[]],[78,282,[41,71],[]],[48,60,[69],[]],[69,60,[48],[]],[80,92,[49,70],[]],[61,312,[82],[]],[82,312,[61],[]],[67,688,[],[]]],\"edges\":[[40,[18,20,37,43,45,52,57,62,64,66,68,73,75,78,80,82]],[43,[14,38,46,54,58,59,65,67,76,81]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-7,-5],[-29,-4],[-1,31,34],[-6,34],[-15,31],[-17,34],[-18,31],[-2,29,32,33,35],[-9,33,35],[-14,32,35],[-21,29,32,33],[-3,30,32,33,35],[-10,33,35],[-16,32,35],[-20,30],[-23,30,32,33],[-25,30,32,33,35],[-5,29,30],[-29,5,30],[-30,5,29],[-32,8,28],[-12,26],[-26,12],[-33,13,27],[-19,35],[-35,19],[-24],[-36,10,16,20,23,25],[-37,4,7],[-38,36],[-39,38],[-40,37],[-41,40],[-42,41],[-43,39,42],[43],[-22,44],[-34,45],[-11,46],[-31,47],[-5,48],[-8,48],[-13,48],[-27,49],[-28,49],[-29,49],[-50,30,32,33],[-30,50],[-32,50],[-33,50],[-51,12,19],[-12,51],[-19,51],[-52,26,35],[-26,52],[-35,52],[-45,53],[-44,53],[-47,54],[-46,54],[-54,55],[-53,55],[-49,56],[-48,56],[-57,51,52],[-51,-52,58],[-59,50,57],[-58,60],[-50,59],[-60,61],[-56,-59,61],[-55,-61,62],[-62],[2,3,5,9,10,14,16,20,21,23,25,29,30,32,33,35],[1,6,11,15,17,18,22,24,31,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":73,\"b\":29},{\"tag\":\"mate\",\"ridge\":644,\"a\":14,\"owners\":[76,81]},{\"tag\":\"mate\",\"ridge\":644,\"a\":38,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":644,\"a\":54,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":644,\"a\":58,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":328,\"a\":18,\"owners\":[73,78,80,82]},{\"tag\":\"mate\",\"ridge\":328,\"a\":43,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":328,\"a\":52,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":328,\"a\":64,\"owners\":[73,78,80]},{\"tag\":\"mate\",\"ridge\":336,\"a\":20,\"owners\":[75,78,80,82]},{\"tag\":\"mate\",\"ridge\":336,\"a\":45,\"owners\":[80,82]},{\"tag\":\"mate\",\"ridge\":336,\"a\":57,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":336,\"a\":62,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":336,\"a\":66,\"owners\":[75,78,80]},{\"tag\":\"mate\",\"ridge\":336,\"a\":68,\"owners\":[75,78,80,82]},{\"tag\":\"mate\",\"ridge\":326,\"a\":37,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":326,\"a\":73,\"owners\":[37,75]},{\"tag\":\"mate\",\"ridge\":326,\"a\":75,\"owners\":[37,73]},{\"tag\":\"mate\",\"ridge\":282,\"a\":78,\"owners\":[41,71]},{\"tag\":\"mate\",\"ridge\":60,\"a\":48,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":60,\"a\":69,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":92,\"a\":80,\"owners\":[49,70]},{\"tag\":\"mate\",\"ridge\":312,\"a\":61,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":312,\"a\":82,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":688,\"a\":67,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[45,57,62,66,68],\"full_literals\":[-36,10,16,20,23,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[29,40],\"full_literals\":[-37,4,7]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-43,39,42],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-22,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-34,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":46,\"full_literals\":[-11,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-31,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":37,\"full_literals\":[-5,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-8,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-13,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-27,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-28,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-29,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[75,78,80],\"full_literals\":[-50,30,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-30,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-32,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-33,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[48,61],\"full_literals\":[-51,12,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":48,\"full_literals\":[-12,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":61,\"full_literals\":[-19,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[69,82],\"full_literals\":[-52,26,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":69,\"full_literals\":[-26,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-35,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[18,20,37,43,45,52,57,62,64,66,68,73,75,78,80,82]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,38,46,54,58,59,65,67,76,81]}]}"
  "76 1 6 11 15 17 18 22 31 34 0 27 75 0\n77 55 0 61 62 59 60 57 58 40 39 38 37 5 7 4 6 3 76 0\n78 -61 0 77 73 72 0\n79 -60 0 78 70 0\n80 -58 0 79 68 0\n81 -52 0 80 66 52 53 23 26 54 0\n82 -26 0 81 55 0\n83 -35 0 81 56 0\n84 -12 0 82 22 0\n85 -19 0 83 25 0\n86 -51 0 84 85 51 0\n87 -57 0 86 81 65 0\n88 -59 0 78 87 71 67 63 64 44 45 46 41 42 43 21 20 24 47 0\n89 -50 0 88 69 0\n90 -30 0 89 48 0\n91 -32 0 89 49 0\n92 -33 0 89 50 0\n93 -20 0 90 15 0\n94 -23 0 90 91 92 16 0\n95 -3 0 90 91 92 83 12 0\n96 -25 0 90 91 92 83 17 0\n97 -14 0 91 83 10 0\n98 -16 0 91 83 14 0\n99 -9 0 92 83 9 0\n100 -10 0 92 83 13 0\n101 -36 0 96 100 93 94 98 28 0\n102 -38 0 101 30 0\n103 -39 0 102 31 0\n104 42 0 103 36 35 0\n105 41 0 104 34 0\n106 40 0 105 33 0\n107 37 0 106 32 0\n108 29 0 83 92 91 90 95 97 94 93 98 99 100 96 18 11 8 74 0\n109 -4 0 108 2 0\n110 5 0 108 90 19 0\n111 7 0 109 107 29 0\n112 0 111 110 1 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00011.record058_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00011.record058
