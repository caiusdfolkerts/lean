module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00034Data
public import GraphInputsRow24Part00034Frames
public import GraphInputsRow24Part00034Leaves
public import GraphInputsRow24Part00034Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016
def vertexColumn : Fields := ⟨10, hexnat% "f8370bc3c8ea368ba1eb16358b6c38ce2b89e1783e364b91e715a54d52d70d634cd2b49d1743d38f1394cd38ccb3c2d4b32d2b2ac9b16c3b31ca745c9715c3783c8f13c2f07cf03a0721ab068590e384d12c471324a91a705854954348dc0c6384c530cd0b12c2b81d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b49b49b4db6d249249249b49249249349b492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40803a246b4cff80000000", hexnat% "44000000000000000", hexnat% "48000000000000000000", 1729558178770714624, hexnat% "18014000000000000", hexnat% "c00000080000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40803804fbccbb80000000", 4035225283303833600, hexnat% "38000004000000000", hexnat% "48000000000000000000", hexnat% "c00000004200000000000", hexnat% "44000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c001f80bcacf480000000", hexnat% "4080200400000000000000", 914840918949888, hexnat% "40000040000000000000", 4035225266123964416, hexnat% "8004000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00187895ec4f80000000", hexnat% "4080200400000000000000", hexnat% "8000002008000000000", 29273603736338432, hexnat% "38000000000000000", hexnat% "40040000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c002f80bca8f480000000", hexnat% "4080100400040000000000", hexnat% "40000040000800000000", 4035225266123964416, hexnat% "8004002000000000000", 351856605790208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00287895e84f80000000", hexnat% "4080100400040000000000", hexnat% "8000002008000000000", hexnat% "38000000000000000", hexnat% "40040040000000000000", 11259205226856448]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c803804bdec7780000000", 4035225266123964416, hexnat% "38000000000000000", 18577932578455552, hexnat% "48000000000000000000", hexnat% "44000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c80399c94ac4480000000", 6917529062000820224, hexnat% "60000008000000000", hexnat% "48000000000000000000", 914806559211520, 29273603736338432]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48300014ac8880000000", 914806559211520, 29273603736338432, hexnat% "4c80080080000000000000", 4323455659455545344, hexnat% "44000000000000000", hexnat% "38000004000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c7
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c4
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c3
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c14 c2
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3d0ecc70f23ab1a668e6c58d62d876c38ce2b86e8791e278f13a719a659939715954d52d475c34cd8b4ad1b61d4749dc4d9354cb31cf0b62ccb4ac6b86d1b26f0731ca785d1725c3783d0f23c4f07ce2348aa198560b8e1c44d1c24a9196151560d0b4c328c6344c9314d0b22c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da4da69a6d26da49b4926934926d2492492693492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 56), (facetIndex 59), (facetIndex 61)]))
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 48), (facetIndex 53), (facetIndex 70)]))
 (.leaf ([(facetIndex 30), (facetIndex 38), (facetIndex 44), (facetIndex 46), (facetIndex 57), (facetIndex 71), (facetIndex 76), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 39), (facetIndex 49), (facetIndex 50), (facetIndex 62), (facetIndex 72), (facetIndex 80), (facetIndex 88)]))
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 32), (facetIndex 41), (facetIndex 45), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 58), (facetIndex 64), (facetIndex 67), (facetIndex 77), (facetIndex 82), (facetIndex 84)]))
 (.leaf ([(facetIndex 51), (facetIndex 52)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4606184033004680c4e100198017f22aeb0a88c9d05ae8z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 60), (facetIndex 63)]))
 (.leaf ([(facetIndex 73), (facetIndex 78), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 90), (facetIndex 91)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 55)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 79)]))
 (.leaf ([(facetIndex 83), (facetIndex 86), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4a8178a08840908036000000000600000000603z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007" "{\"ridges\":[[18,137],[20,145],[26,138],[27,146],[31,137],[52,259],[53,259],[56,524],[58,137],[69,664],[70,265],[70,776],[70,784],[71,137],[72,145],[77,168],[85,408],[87,138],[88,146]],\"owners\":[[18,137,[5,31,41,46,47,54,60,68,69],[58,71]],[31,137,[18,68,69,71],[5,41,46,47,54,58,60]],[58,137,[5,41,46,47,68,69],[18,31,54,60,71]],[71,137,[5,31,41,47,54,68,69],[18,46,58,60]],[26,138,[5,31,41,46,47,73,78,85],[77,87]],[87,138,[5,31,41,47,73,85],[26,46,77,78]],[52,259,[6,32,40,45,48],[9,36,47,51,53]],[53,259,[6,32,45,47],[9,36,40,48,51,52]],[70,265,[6,32,45,47],[19,42,55,61,68]],[20,145,[8,35,41,50,52,54,63,68,69],[64,72]],[72,145,[8,35,41,52,54,68,69],[20,50,63,64]],[27,146,[8,35,41,50,52,73,81,85],[82,88]],[88,146,[8,35,41,52,73,85],[27,50,81,82]],[56,524,[79],[14,33,59,61,75,89]],[77,168,[18,71],[26,58,87,90]],[70,776,[79],[19,48,61,86,89]],[70,784,[83],[21,53,66,86,89]],[85,408,[68],[]],[69,664,[],[]]],\"edges\":[[27,[5,18,26,31,41,46,47,54,58,60,68,69,71,73,77,78,85,87,90]],[32,[8,20,27,35,41,50,52,54,63,64,68,69,72,73,81,82,85,88,91]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-1],[-9,-2],[-10,-1],[-10,-9],[-11,-10],[-15,-9],[-16,-1],[-16,-9],[-18,-9],[-18,-15],[-19,-9],[-19,-16],[-19,-18],[-21,-3],[-21,-8],[-21,-12],[-21,-14],[-21,-15],[-21,-20],[-22,-8],[-22,-14],[-22,-15],[-22,-17],[-22,-18],[-23,-21],[-23,-22],[-27,-10],[-29,-10],[-31,-21],[-32,-15],[-32,-19],[-32,-23],[-34,-32],[-40,-10],[-42,-21],[-4,1,9,14,17,18,24,28,32,33],[-9,4,32,33,35],[-26,1,14,17,18,32,33],[-35,1,9,14,18,24,32,33],[-6,1,9,14,17,18,37,39,44],[-45,1,9,14,18,37,44],[-22,2,10,13,16,19],[-23,2,10,16,18],[-34,2,10,16,18],[-5,3,12,14,20,22,24,30,32,33],[-36,3,12,14,22,24,32,33],[-7,3,12,14,20,22,37,41,44],[-46,3,12,14,22,37,44],[-25,40],[-38,4,35],[-34,40],[-34,43],[-44,32],[-33],[-49,11,25,27,29],[-50,15,19,23,34],[-51,8,9,10,14,16,18],[-52,21,22],[-53,49],[-54,50],[-55,53],[-55,54],[-56,51],[-57,52],[-58,56],[-58,57],[-59,55],[-59,58],[59],[-24,60],[-28,60],[-30,60],[-37,61],[-39,61],[-41,61],[-47,62],[-48,62],[-13,63],[-40,64],[-43,65],[-61,66],[-60,66],[-63,67],[-62,67],[-67,68],[-66,68],[-64,-65,69],[-69,70],[-68,-70,71],[-71],[1,4,6,9,14,17,18,24,26,28,32,33,35,37,38,39,44,45,47],[3,5,7,12,14,20,22,24,30,31,32,33,36,37,41,42,44,46,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":31,\"b\":5},{\"tag\":\"incompatible\",\"a\":31,\"b\":6},{\"tag\":\"incompatible\",\"a\":32,\"b\":5},{\"tag\":\"incompatible\",\"a\":32,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":42,\"b\":31},{\"tag\":\"incompatible\",\"a\":45,\"b\":5},{\"tag\":\"incompatible\",\"a\":45,\"b\":31},{\"tag\":\"incompatible\",\"a\":47,\"b\":31},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":31},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":8},{\"tag\":\"incompatible\",\"a\":51,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":35},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":42},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":29},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":61,\"b\":32},{\"tag\":\"incompatible\",\"a\":64,\"b\":51},{\"tag\":\"incompatible\",\"a\":68,\"b\":42},{\"tag\":\"incompatible\",\"a\":68,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":53},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":32},{\"tag\":\"incompatible\",\"a\":82,\"b\":51},{\"tag\":\"mate\",\"ridge\":137,\"a\":18,\"owners\":[5,31,41,46,47,54,60,68,69]},{\"tag\":\"mate\",\"ridge\":137,\"a\":31,\"owners\":[18,68,69,71]},{\"tag\":\"mate\",\"ridge\":137,\"a\":58,\"owners\":[5,41,46,47,68,69]},{\"tag\":\"mate\",\"ridge\":137,\"a\":71,\"owners\":[5,31,41,47,54,68,69]},{\"tag\":\"mate\",\"ridge\":138,\"a\":26,\"owners\":[5,31,41,46,47,73,78,85]},{\"tag\":\"mate\",\"ridge\":138,\"a\":87,\"owners\":[5,31,41,47,73,85]},{\"tag\":\"mate\",\"ridge\":259,\"a\":52,\"owners\":[6,32,40,45,48]},{\"tag\":\"mate\",\"ridge\":259,\"a\":53,\"owners\":[6,32,45,47]},{\"tag\":\"mate\",\"ridge\":265,\"a\":70,\"owners\":[6,32,45,47]},{\"tag\":\"mate\",\"ridge\":145,\"a\":20,\"owners\":[8,35,41,50,52,54,63,68,69]},{\"tag\":\"mate\",\"ridge\":145,\"a\":72,\"owners\":[8,35,41,52,54,68,69]},{\"tag\":\"mate\",\"ridge\":146,\"a\":27,\"owners\":[8,35,41,50,52,73,81,85]},{\"tag\":\"mate\",\"ridge\":146,\"a\":88,\"owners\":[8,35,41,52,73,85]},{\"tag\":\"mate\",\"ridge\":524,\"a\":56,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":168,\"a\":77,\"owners\":[18,71]},{\"tag\":\"mate\",\"ridge\":776,\"a\":70,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":784,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":408,\"a\":85,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":664,\"a\":69,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[33,56,59,61],\"full_literals\":[-49,11,25,27,29]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[42,48,53,70],\"full_literals\":[-50,15,19,23,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[29,31,32,41,45,47],\"full_literals\":[-51,8,9,10,14,16,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[51,52],\"full_literals\":[-52,21,22]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-59,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":54,\"full_literals\":[-24,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-28,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-30,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-37,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-39,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":81,\"full_literals\":[-41,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-47,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-48,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-13,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-40,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-43,65]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-65,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[5,18,26,31,41,46,47,54,58,60,68,69,71,73,77,78,85,87,90]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[8,20,27,35,41,50,52,54,63,64,68,69,72,73,81,82,85,88,91]}]}"
  "p cnf 71 92\n-9 -1 0\n-9 -2 0\n-10 -1 0\n-10 -9 0\n-11 -10 0\n-15 -9 0\n-16 -1 0\n-16 -9 0\n-18 -9 0\n-18 -15 0\n-19 -9 0\n-19 -16 0\n-19 -18 0\n-21 -3 0\n-21 -8 0\n-21 -12 0\n-21 -14 0\n-21 -15 0\n-21 -20 0\n-22 -8 0\n-22 -14 0\n-22 -15 0\n-22 -17 0\n-22 -18 0\n-23 -21 0\n-23 -22 0\n-27 -10 0\n-29 -10 0\n-31 -21 0\n-32 -15 0\n-32 -19 0\n-32 -23 0\n-34 -32 0\n-40 -10 0\n-42 -21 0\n-4 1 9 14 17 18 24 28 32 33 0\n-9 4 32 33 35 0\n-26 1 14 17 18 32 33 0\n-35 1 9 14 18 24 32 33 0\n-6 1 9 14 17 18 37 39 44 0\n-45 1 9 14 18 37 44 0\n-22 2 10 13 16 19 0\n-23 2 10 16 18 0\n-34 2 10 16 18 0\n-5 3 12 14 20 22 24 30 32 33 0\n-36 3 12 14 22 24 32 33 0\n-7 3 12 14 20 22 37 41 44 0\n-46 3 12 14 22 37 44 0\n-25 40 0\n-38 4 35 0\n-34 40 0\n-34 43 0\n-44 32 0\n-33 0\n-49 11 25 27 29 0\n-50 15 19 23 34 0\n-51 8 9 10 14 16 18 0\n-52 21 22 0\n-53 49 0\n-54 50 0\n-55 53 0\n-55 54 0\n-56 51 0\n-57 52 0\n-58 56 0\n-58 57 0\n-59 55 0\n-59 58 0\n59 0\n-24 60 0\n-28 60 0\n-30 60 0\n-37 61 0\n-39 61 0\n-41 61 0\n-47 62 0\n-48 62 0\n-13 63 0\n-40 64 0\n-43 65 0\n-61 66 0\n-60 66 0\n-63 67 0\n-62 67 0\n-67 68 0\n-66 68 0\n-64 -65 69 0\n-69 70 0\n-68 -70 71 0\n-71 0\n1 4 6 9 14 17 18 24 26 28 32 33 35 37 38 39 44 45 47 0\n3 5 7 12 14 20 22 24 30 31 32 33 36 37 41 42 44 46 48 0\n"
  "93 55 0 69 67 0\n94 58 0 69 68 0\n95 53 0 93 61 0\n96 54 0 93 62 0\n97 56 0 94 65 0\n98 57 0 94 66 0\n99 49 0 95 59 0\n100 50 0 96 60 0\n101 51 0 97 63 0\n102 52 0 98 64 0\n103 1 4 6 9 14 17 18 24 26 28 32 35 37 38 39 44 45 47 0 54 91 0\n104 3 5 7 12 14 20 22 24 30 31 32 36 37 41 42 44 46 48 0 54 92 0\n105 -32 0 100 30 31 32 33 56 0\n106 -44 0 105 53 0\n107 -22 35 4 1 68 0 54 106 105 37 50 86 82 71 70 81 74 73 85 84 76 21 23 24 40 38 41 103 0\n108 22 31 3 68 0 102 54 106 105 86 82 72 70 81 75 73 85 84 77 58 16 17 19 35 45 46 48 47 104 0\n109 22 68 0 102 58 14 29 108 0\n110 35 4 68 0 54 105 101 109 24 21 20 37 107 3 7 57 0\n111 -1 -22 0 101 24 21 20 1 3 7 57 0\n112 9 68 0 54 105 109 111 24 23 21 86 82 71 70 39 36 110 0\n113 68 0 85 83 78 109 112 2 4 8 11 42 0\n114 -70 0 113 90 89 0\n115 -69 0 114 88 0\n116 -9 0 100 2 4 6 8 9 11 44 43 56 0\n117 -10 0 99 5 27 28 34 55 49 0\n118 -34 0 115 51 52 79 80 87 0\n119 -22 18 14 0 117 116 101 118 100 20 22 26 57 56 12 0\n120 18 14 0 100 118 101 116 117 102 119 58 15 18 25 57 56 12 0\n121 -18 0 118 100 102 10 13 24 56 58 25 0\n122 14 0 121 120 0\n123 -21 0 122 17 0\n124 -22 0 122 21 0\n125 0 123 124 102 58 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f4c723c3cb1a4e8e6c58d62d876c38ce8791e0f8f1c66394e4e5c5695356352d475c364d3362d8751d0f4e3c4d9334d332cc73c2d4b32d2b86d1b0ef0729e1745c5783d0f23c1f1b06a31866258361382ec47091a4c519615254358344d0b4c318d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a49a6d34da492492493492492492693492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 45), (facetIndex 59), (facetIndex 76)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 44), (facetIndex 46), (facetIndex 47)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 67)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 42), (facetIndex 55), (facetIndex 71), (facetIndex 73)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53)])))
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 54), (facetIndex 68), (facetIndex 79), (facetIndex 82)]))
 (.leaf ([(facetIndex 48), (facetIndex 51), (facetIndex 62), (facetIndex 65), (facetIndex 78), (facetIndex 80)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "187dc00208066fb7d20909adf6f241120cd8244z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 88)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 56)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 81), (facetIndex 84), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 83), (facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2bcde280209001b0000000003000000000603z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6, 7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7]
def grouped3_0027 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043" 83

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043" "{\"ridges\":[[7,265],[8,50],[9,146],[16,52],[17,148],[18,529],[22,776],[23,784],[26,22],[27,22],[34,266],[35,524],[38,532],[40,774],[41,50],[42,274],[44,266],[46,265],[47,776],[48,50],[49,50],[49,146],[50,50],[51,146],[52,146],[53,784],[55,52],[57,532],[61,776],[62,52],[63,52],[63,148],[64,52],[64,529],[65,148],[66,148],[66,529],[67,784],[71,776],[71,784],[73,22],[74,284],[75,538],[77,774],[78,22],[80,22],[81,22],[81,774]],\"owners\":[[7,265,[22,56,61,69,71],[34,42,44,46]],[46,265,[22,56,61,69,71],[7,34,42,44]],[34,266,[83,84],[7,42,44,46,47,74,77]],[44,266,[74,77,84],[7,34,42,46,47,83]],[8,50,[26,73,78,79,83,85],[41,48,49,50]],[41,50,[26,78,79,85],[8,48,49,50,73,83]],[48,50,[26,73,79,83],[8,41,49,50,78,85]],[49,50,[26,73,78,83],[8,41,48,50,79,85]],[50,50,[26,73,78,79,85],[8,41,48,49,83]],[9,146,[27,79,80,85],[49,51,52]],[49,146,[27,80],[9,51,52,79,85]],[51,146,[27,79],[9,49,52,80,85]],[52,146,[27,79,80,85],[9,49,51]],[42,274,[81],[10,37,50,52,53,74,83,84]],[35,524,[86,87],[15,57,58,60,61,75,77]],[16,52,[26,73,78,79,86,88],[55,62,63,64]],[55,52,[26,78,79,88],[16,62,63,64,73,86]],[62,52,[26,73,79,86],[16,55,63,64,78,88]],[63,52,[26,73,78,86],[16,55,62,64,79,88]],[64,52,[26,73,78,79,88],[16,55,62,63,86]],[17,148,[27,79,80,88],[63,65,66]],[63,148,[27,80],[17,65,66,79,88]],[65,148,[27,79],[17,63,66,80,88]],[66,148,[27,79,80,88],[17,63,65]],[18,529,[23,43,53,70,71],[38,57,64,66]],[64,529,[23,43,53,71],[18,38,57,66,70]],[66,529,[23,43,53,70,71],[18,38,57,64]],[38,532,[86,87],[18,57,64,66,67,75,81]],[57,532,[81],[18,38,64,66,67,75,86,87]],[22,776,[77,84,87],[47,61,71]],[47,776,[87],[22,61,71,77,84]],[61,776,[84],[22,47,71,77,87]],[71,776,[77],[22,47,61,84,87]],[23,784,[81,84,87],[53,67,71]],[53,784,[87],[23,67,71,81,84]],[67,784,[84],[23,53,71,81,87]],[71,784,[81],[23,53,67,84,87]],[40,774,[77,81],[]],[77,774,[40,81],[]],[81,774,[40,77],[]],[75,538,[43,84],[]],[74,284,[56,87],[]]],\"edges\":[[28,[7,22,34,42,44,46,47,56,61,69,71,74,77,83,84,87]],[30,[8,16,26,41,48,49,50,55,62,63,64,69,70,72,73,78,79,83,85,86,88]],[32,[9,17,27,49,51,52,63,65,66,72,79,80,85,88]],[34,[18,23,38,43,53,57,64,66,67,70,71,75,81,84,86,87]],[44,[22,23,40,47,53,61,67,71,77,81,84,87]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-19,-11],[-19,-16],[-19,-17],[-20,-11],[-20,-16],[-20,-17],[-30,-28],[-31,-28],[-32,-28],[-44,-18],[-46,-44],[-50,-22],[-50,-34],[-50,-48],[-51,-12],[-51,-13],[-51,-29],[-51,-45],[-51,-49],[-53,-11],[-53,-16],[-53,-17],[-53,-28],[-53,-42],[-53,-44],[-56,-11],[-56,-16],[-56,-17],[-56,-42],[-56,-44],[-9,-10,-51],[-9,-50,-51],[-10,-44,-51],[-10,-48,-51],[-44,-50,-51],[-1,7,29,33,40,42],[-20,7,29,33,40,42],[-12,52,53],[-19,45,47,53],[-2,9,44,48,49,52,54],[-16,9,48,49,54],[-22,9,44,49,52],[-23,9,44,48,52],[-24,9,44,48,49,54],[-3,10,49,50,54],[-23,10,50],[-25,10,49],[-26,10,49,50,54],[-17,51],[-13,55,56],[-4,9,44,48,49,55,57],[-28,9,48,49,57],[-34,9,44,49,55],[-35,9,44,48,55],[-36,9,44,48,49,57],[-5,10,49,50,57],[-35,10,50],[-37,10,49],[-38,10,49,50,57],[-6,8,18,27,41,42],[-36,8,18,27,42],[-38,8,18,27,41,42],[-14,55,56],[-30,51],[-7,47,53,56],[-21,56],[-33,53],[-42,47],[-8,51,53,56],[-27,56],[-39,53],[-42,51],[-15,47,51],[-47,15,51],[-51,15,47],[-46,18,53],[-45,29,56],[-58,12,13,19,20,21],[-59,30,31,32,33],[-60,11,16,17,28,42,44],[-61,58],[-62,59],[-63,61],[-63,62],[-64,60],[-65,64],[-66,63],[-66,65],[66],[-43,67],[-54,68],[-57,69],[-15,70],[-18,70],[-29,70],[-71,45,46,47],[-47,71],[-72,51,53,56],[-51,72],[-53,72],[-56,72],[-40,73],[-41,73],[-52,74],[-55,74],[-68,75],[-67,75],[-70,76],[-69,76],[-76,77],[-75,77],[-78,71,72],[-72,78],[-71,78],[-71,-72,79],[-74,80],[-73,80],[-78,-80,81],[-79,81],[-79,-80,82],[-82,83],[-77,-81,83],[-83],[1,7,12,17,19,20,21,29,33,40,42,45,47,52,53,56],[2,4,9,16,22,23,24,28,34,35,36,40,41,43,44,48,49,52,54,55,57],[3,5,10,23,25,26,35,37,38,43,49,50,54,57],[6,8,14,18,27,30,36,38,39,41,42,46,51,53,55,56],[7,8,15,21,27,33,39,42,47,51,53,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":32},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":32},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":73,\"b\":43},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":48},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":34},{\"tag\":\"incompatible\",\"a\":81,\"b\":35},{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":84,\"b\":32},{\"tag\":\"incompatible\",\"a\":84,\"b\":41},{\"tag\":\"incompatible\",\"a\":84,\"b\":42},{\"tag\":\"incompatible\",\"a\":84,\"b\":55},{\"tag\":\"incompatible\",\"a\":84,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":73},{\"tag\":\"incompatible\",\"a\":87,\"b\":32},{\"tag\":\"incompatible\",\"a\":87,\"b\":41},{\"tag\":\"incompatible\",\"a\":87,\"b\":42},{\"tag\":\"incompatible\",\"a\":87,\"b\":71},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[26,27,81]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[26,80,81]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[27,73,81]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[27,78,81]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[73,80,81]},{\"tag\":\"mate\",\"ridge\":265,\"a\":7,\"owners\":[22,56,61,69,71]},{\"tag\":\"mate\",\"ridge\":265,\"a\":46,\"owners\":[22,56,61,69,71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":34,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":266,\"a\":44,\"owners\":[74,77,84]},{\"tag\":\"mate\",\"ridge\":50,\"a\":8,\"owners\":[26,73,78,79,83,85]},{\"tag\":\"mate\",\"ridge\":50,\"a\":41,\"owners\":[26,78,79,85]},{\"tag\":\"mate\",\"ridge\":50,\"a\":48,\"owners\":[26,73,79,83]},{\"tag\":\"mate\",\"ridge\":50,\"a\":49,\"owners\":[26,73,78,83]},{\"tag\":\"mate\",\"ridge\":50,\"a\":50,\"owners\":[26,73,78,79,85]},{\"tag\":\"mate\",\"ridge\":146,\"a\":9,\"owners\":[27,79,80,85]},{\"tag\":\"mate\",\"ridge\":146,\"a\":49,\"owners\":[27,80]},{\"tag\":\"mate\",\"ridge\":146,\"a\":51,\"owners\":[27,79]},{\"tag\":\"mate\",\"ridge\":146,\"a\":52,\"owners\":[27,79,80,85]},{\"tag\":\"mate\",\"ridge\":274,\"a\":42,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":524,\"a\":35,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":52,\"a\":16,\"owners\":[26,73,78,79,86,88]},{\"tag\":\"mate\",\"ridge\":52,\"a\":55,\"owners\":[26,78,79,88]},{\"tag\":\"mate\",\"ridge\":52,\"a\":62,\"owners\":[26,73,79,86]},{\"tag\":\"mate\",\"ridge\":52,\"a\":63,\"owners\":[26,73,78,86]},{\"tag\":\"mate\",\"ridge\":52,\"a\":64,\"owners\":[26,73,78,79,88]},{\"tag\":\"mate\",\"ridge\":148,\"a\":17,\"owners\":[27,79,80,88]},{\"tag\":\"mate\",\"ridge\":148,\"a\":63,\"owners\":[27,80]},{\"tag\":\"mate\",\"ridge\":148,\"a\":65,\"owners\":[27,79]},{\"tag\":\"mate\",\"ridge\":148,\"a\":66,\"owners\":[27,79,80,88]},{\"tag\":\"mate\",\"ridge\":529,\"a\":18,\"owners\":[23,43,53,70,71]},{\"tag\":\"mate\",\"ridge\":529,\"a\":64,\"owners\":[23,43,53,71]},{\"tag\":\"mate\",\"ridge\":529,\"a\":66,\"owners\":[23,43,53,70,71]},{\"tag\":\"mate\",\"ridge\":532,\"a\":38,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":776,\"a\":22,\"owners\":[77,84,87]},{\"tag\":\"mate\",\"ridge\":776,\"a\":47,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":776,\"a\":61,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":71,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":784,\"a\":23,\"owners\":[81,84,87]},{\"tag\":\"mate\",\"ridge\":784,\"a\":53,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":784,\"a\":67,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":784,\"a\":71,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":774,\"a\":40,\"owners\":[77,81]},{\"tag\":\"mate\",\"ridge\":774,\"a\":77,\"owners\":[40,81]},{\"tag\":\"mate\",\"ridge\":774,\"a\":81,\"owners\":[40,77]},{\"tag\":\"mate\",\"ridge\":538,\"a\":75,\"owners\":[43,84]},{\"tag\":\"mate\",\"ridge\":284,\"a\":74,\"owners\":[56,87]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[34,35,44,46,47],\"full_literals\":[-58,12,13,19,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[57,58,60,61],\"full_literals\":[-59,30,31,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[32,41,42,55,71,73],\"full_literals\":[-60,11,16,17,28,42,44]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-66,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-43,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-54,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-57,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-15,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-18,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-29,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[74,75,77],\"full_literals\":[-71,45,46,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-47,71]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[81,84,87],\"full_literals\":[-72,51,53,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":81,\"full_literals\":[-51,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-53,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-56,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-40,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-41,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-52,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-55,74]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-79,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-82,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-77,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[7,22,34,42,44,46,47,56,61,69,71,74,77,83,84,87]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[8,16,26,41,48,49,50,55,62,63,64,69,70,72,73,78,79,83,85,86,88]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[9,17,27,49,51,52,63,65,66,72,79,80,85,88]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[18,23,38,43,53,57,64,66,67,70,71,75,81,84,86,87]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[22,23,40,47,53,61,67,71,77,81,84,87]}]}"
  "p cnf 83 128\n-19 -11 0\n-19 -16 0\n-19 -17 0\n-20 -11 0\n-20 -16 0\n-20 -17 0\n-30 -28 0\n-31 -28 0\n-32 -28 0\n-44 -18 0\n-46 -44 0\n-50 -22 0\n-50 -34 0\n-50 -48 0\n-51 -12 0\n-51 -13 0\n-51 -29 0\n-51 -45 0\n-51 -49 0\n-53 -11 0\n-53 -16 0\n-53 -17 0\n-53 -28 0\n-53 -42 0\n-53 -44 0\n-56 -11 0\n-56 -16 0\n-56 -17 0\n-56 -42 0\n-56 -44 0\n-9 -10 -51 0\n-9 -50 -51 0\n-10 -44 -51 0\n-10 -48 -51 0\n-44 -50 -51 0\n-1 7 29 33 40 42 0\n-20 7 29 33 40 42 0\n-12 52 53 0\n-19 45 47 53 0\n-2 9 44 48 49 52 54 0\n-16 9 48 49 54 0\n-22 9 44 49 52 0\n-23 9 44 48 52 0\n-24 9 44 48 49 54 0\n-3 10 49 50 54 0\n-23 10 50 0\n-25 10 49 0\n-26 10 49 50 54 0\n-17 51 0\n-13 55 56 0\n-4 9 44 48 49 55 57 0\n-28 9 48 49 57 0\n-34 9 44 49 55 0\n-35 9 44 48 55 0\n-36 9 44 48 49 57 0\n-5 10 49 50 57 0\n-35 10 50 0\n-37 10 49 0\n-38 10 49 50 57 0\n-6 8 18 27 41 42 0\n-36 8 18 27 42 0\n-38 8 18 27 41 42 0\n-14 55 56 0\n-30 51 0\n-7 47 53 56 0\n-21 56 0\n-33 53 0\n-42 47 0\n-8 51 53 56 0\n-27 56 0\n-39 53 0\n-42 51 0\n-15 47 51 0\n-47 15 51 0\n-51 15 47 0\n-46 18 53 0\n-45 29 56 0\n-58 12 13 19 20 21 0\n-59 30 31 32 33 0\n-60 11 16 17 28 42 44 0\n-61 58 0\n-62 59 0\n-63 61 0\n-63 62 0\n-64 60 0\n-65 64 0\n-66 63 0\n-66 65 0\n66 0\n-43 67 0\n-54 68 0\n-57 69 0\n-15 70 0\n-18 70 0\n-29 70 0\n-71 45 46 47 0\n-47 71 0\n-72 51 53 56 0\n-51 72 0\n-53 72 0\n-56 72 0\n-40 73 0\n-41 73 0\n-52 74 0\n-55 74 0\n-68 75 0\n-67 75 0\n-70 76 0\n-69 76 0\n-76 77 0\n-75 77 0\n-78 71 72 0\n-72 78 0\n-71 78 0\n-71 -72 79 0\n-74 80 0\n-73 80 0\n-78 -80 81 0\n-79 81 0\n-79 -80 82 0\n-82 83 0\n-77 -81 83 0\n-83 0\n1 7 12 17 19 20 21 29 33 40 42 45 47 52 53 56 0\n2 4 9 16 22 23 24 28 34 35 36 40 41 43 44 48 49 52 54 55 57 0\n3 5 10 23 25 26 35 37 38 43 49 50 54 57 0\n6 8 14 18 27 30 36 38 39 41 42 46 51 53 55 56 0\n7 8 15 21 27 33 39 42 47 51 53 56 0\n"
  "129 63 0 89 87 0\n130 65 0 89 88 0\n131 61 0 129 83 0\n132 62 0 129 84 0\n133 64 0 130 86 0\n134 58 0 131 81 0\n135 59 0 132 82 0\n136 60 0 133 85 0\n137 -82 0 123 121 0\n138 78 15 0 113 114 99 100 101 97 69 72 67 71 66 70 65 128 0\n139 72 70 0 93 138 95 94 99 100 101 112 74 76 77 96 0\n140 50 10 5 3 49 77 0 58 47 111 107 90 106 91 110 109 92 46 57 48 59 126 0\n141 -10 2 -51 80 77 0 19 117 103 102 116 105 104 111 107 90 106 91 110 109 92 31 33 34 51 42 53 54 44 55 43 41 52 125 0\n142 -17 12 13 21 0 134 3 6 78 0\n143 -11 12 13 21 0 134 1 4 78 0\n144 -16 12 13 21 0 134 2 5 78 0\n145 -44 -51 77 0 19 111 106 91 110 109 92 33 35 45 140 56 0\n146 -28 33 0 135 7 8 9 79 0\n147 50 3 10 49 77 0 110 109 92 140 56 0\n148 10 50 49 77 0 111 106 91 45 147 0\n149 -10 -51 80 77 0 145 19 116 104 111 106 91 31 34 141 40 0\n150 53 56 80 77 0 116 105 50 66 117 103 102 104 110 108 139 111 107 90 106 91 109 92 67 98 38 19 144 145 146 149 148 12 13 14 32 43 40 51 54 44 55 125 0\n151 -53 0 136 20 21 22 23 24 25 80 0\n152 -33 0 151 67 0\n153 -39 0 151 71 0\n154 -28 0 152 146 0\n155 -56 0 154 136 26 27 28 29 30 80 0\n156 -21 0 155 66 0\n157 -27 0 155 70 0\n158 77 0 151 155 137 110 108 93 139 150 98 120 75 115 97 0\n159 -81 0 158 123 122 0\n160 -79 0 159 119 0\n161 -51 0 160 159 155 151 156 152 15 16 17 18 99 142 113 115 118 97 116 117 65 68 39 104 102 36 37 124 0\n162 -17 0 161 49 0\n163 -30 0 161 64 0\n164 -8 0 161 151 155 69 0\n165 -42 0 161 72 0\n166 80 0 156 162 154 136 155 151 161 165 153 163 157 164 116 117 104 105 103 38 50 63 143 144 80 10 11 61 60 62 127 0\n167 -78 0 166 159 118 0\n168 -71 0 167 114 0\n169 15 0 167 138 0\n170 -47 0 168 97 0\n171 0 169 170 161 73 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00034.record043_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00034.record043
