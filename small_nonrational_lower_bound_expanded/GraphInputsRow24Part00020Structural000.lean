module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00020Data
public import GraphInputsRow24Part00020Frames
public import GraphInputsRow24Part00020Leaves
public import GraphInputsRow24Part00020Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 9223374236012249088]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 4), 1207959552, 504403226984972288, 9225626035691716608]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 4), 9223374235878031360, 436849232574414848]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 294985775592767488, 216172790703718400, 9223374236012249088, 69793218560]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 4503601237983232, 52776558133248, (certNat% 10), 2253998836940800]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), 52780853100544, 472877960873902080, 69793218560]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 52783000584192]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [555632789202927616, 61710090108928, (certNat% 18), (certNat% 19), 2199224582144, (certNat% 20)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9735660280448286720, (certNat% 21), 61583388573696, (certNat% 22), 45035996273704960, (certNat% 23)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 35197256990720, 2199627235328, 472877960873902080, 69793218560]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 19), (certNat% 27), 70330089472, 9007201469333504, 61585536057344, 4611688217450643456]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c19 c6
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e86e334cb13c6c8f26a8ea6693a2e8d68d8763389e0fb91cc5c9ca56966539c9665c54d58d5351d70d3362d4b46d4749d0f59334e334cc7362d2b1ad1b26c3b31e2719e1725c570dc8f0bc1fcc2341b0ca1a8660d84e0bb116458932615134c324c8b12c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db69b6d24d249b4db4d36d369b6936d34d34d2492489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 67), (facetIndex 74)]))
 (.leaf ([(facetIndex 42), (facetIndex 59), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 53), (facetIndex 55), (facetIndex 63), (facetIndex 80)]))
 (.leaf ([(facetIndex 24), (facetIndex 37), (facetIndex 49), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 25), (facetIndex 26), (facetIndex 27), (facetIndex 28)]))
 (.leaf ([(facetIndex 65), (facetIndex 68), (facetIndex 69)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 29), (facetIndex 46)]))
 (.leaf ([(facetIndex 31), (facetIndex 33), (facetIndex 41)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "200000002d0294c0200410018180078018038e34923dz11;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 54), (facetIndex 76)]))
 (.leaf ([(facetIndex 44), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 60), (facetIndex 82)]))
 (.branch 4
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 50)]))
 (.leaf ([(facetIndex 52), (facetIndex 78), (facetIndex 79)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 34), (facetIndex 71), (facetIndex 75)]))
 (.leaf ([(facetIndex 72), (facetIndex 77), (facetIndex 81)])))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 66), (facetIndex 73)]))
 (.branch 9
 (.leaf ([(facetIndex 30), (facetIndex 36), (facetIndex 43), (facetIndex 48), (facetIndex 51), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 58), (facetIndex 61)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "26044605076510007000092098800048308303180099008050708z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0, 1]
def grouped3_0012 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027" "{\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027" 38

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027" "{\"ridges\":[[50,780],[53,517],[55,769],[60,353],[63,769],[79,296],[80,800],[82,480]],\"owners\":[[53,517,[50],[8,28,30,48,55,56,57]],[55,769,[61],[12,50,57,63,64]],[63,769,[50],[12,55,57,61,64]],[80,800,[61],[21,57,63,79]],[79,296,[36,58,60,72,75,81,82],[47,61,78]],[50,780,[79],[]],[60,353,[],[]],[82,480,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-10,-1],[-10,-2],[-10,-4],[-6,5],[-7,10],[-11,5],[-15,10],[-14,3,8,9,12,13,16,17],[-5,14],[-9],[-17],[-18,6,7,11,15],[-19,1,2,4],[-20,18],[-21,20],[-22,19],[-23,22],[-24,21],[-24,23],[24],[-5,25],[-14,26],[-13,27],[-12,28],[-16,28],[-3,29],[-8,30],[-25,-26,31],[-31,32],[-32,33],[-28,34],[-27,34],[-30,35],[-29,35],[-35,36],[-36,37],[-34,37],[-33,-37,38],[-38]],\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":61,\"b\":23},{\"tag\":\"incompatible\",\"a\":61,\"b\":29},{\"tag\":\"incompatible\",\"a\":61,\"b\":46},{\"tag\":\"mate\",\"ridge\":517,\"a\":53,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":769,\"a\":55,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":769,\"a\":63,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":800,\"a\":80,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":296,\"a\":79,\"owners\":[36,58,60,72,75,81,82]},{\"tag\":\"mate\",\"ridge\":780,\"a\":50,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":353,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":82,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[53,55,63,80],\"full_literals\":[-18,6,7,11,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[23,29,46],\"full_literals\":[-19,1,2,4]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-20,18,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-22,19,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-23,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-24,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-5,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-14,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-13,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-12,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-16,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":36,\"full_literals\":[-3,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":58,\"full_literals\":[-8,30]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "40 21 0 20 18 0\n41 23 0 20 19 0\n42 20 0 40 15 0\n43 22 0 41 17 0\n44 18 0 42 14 0\n45 19 0 43 16 0\n46 5 10 0 44 7 5 4 6 12 0\n47 -5 0 39 11 10 9 21 22 28 29 30 38 36 37 35 31 32 33 34 24 25 23 27 26 8 0\n48 10 0 47 46 0\n49 -1 0 48 1 0\n50 -2 0 48 2 0\n51 -4 0 48 3 0\n52 0 50 51 45 49 13 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record027_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "763a43b19c371ca3a95ac99a639b161db0e638ce2b86e178e9664d9e16a539715654d51d70d634cd2b46d4749d1766338f131cf0b62ccb2ac6b46f0761cc729c6785d1715c3783d0f23c4f0bd8c4711a16b06899164381e384c9166252948d0762318c5312c1b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b69369a4db49a6936db4934924d369a49b492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 67), (facetIndex 78)]))
 (.leaf ([(facetIndex 38), (facetIndex 72), (facetIndex 74), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 53), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 34), (facetIndex 40), (facetIndex 45), (facetIndex 47), (facetIndex 48)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 28), (facetIndex 51), (facetIndex 55), (facetIndex 71), (facetIndex 82)]))
 (.leaf ([(facetIndex 42), (facetIndex 54), (facetIndex 64), (facetIndex 66)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 25), (facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 33)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1000080418001450900009509b36181430404ffffcdb8z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 84)]))
 (.leaf ([(facetIndex 58), (facetIndex 59), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 44), (facetIndex 46), (facetIndex 65)]))
 (.leaf ([(facetIndex 43), (facetIndex 56), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 52), (facetIndex 57), (facetIndex 81)]))
 (.leaf ([(facetIndex 68), (facetIndex 70), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 75), (facetIndex 76), (facetIndex 80)]))
 (.branch 8
 (.leaf ([(facetIndex 69), (facetIndex 83)]))
 (.leaf ([(facetIndex 79)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10704680066050057500200003114300040000020230600024z24;"⟩
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
def grouped3_0007 : List Nat := [0, 1]
def grouped3_0008 : List Nat := [0, 1, 2, 3]
def grouped3_0010 : List Nat := [2]
def grouped3_0011 : List Nat := [2, 3]
def grouped3_0012 : List Nat := [3]
def grouped3_0013 : List Nat := [4]
def grouped3_0014 : List Nat := [4, 5]
def grouped3_0015 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0016 : List Nat := [5]
def grouped3_0017 : List Nat := [6]
def grouped3_0018 : List Nat := [6, 7, 8]
def grouped3_0019 : List Nat := [7]
def grouped3_0020 : List Nat := [7, 8]
def grouped3_0021 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035" "{\"ridges\":[[20,772],[35,164],[38,770],[41,170],[53,164],[61,224],[62,164],[63,897],[69,170],[72,772],[74,772],[75,198],[76,418],[77,772],[79,170],[80,450],[83,108],[84,928]],\"owners\":[[35,164,[83,84],[11,53,61,62,69,75,76]],[53,164,[75,76,84],[11,35,61,62,69,83]],[62,164,[69,75,76,83],[11,35,53,61,84]],[61,224,[79],[15,47,66,75,83]],[38,770,[],[20,44,46,72,74,77]],[20,772,[56,60,63,84],[38,72,74,77]],[72,772,[60,63,84],[20,38,56,74,77]],[74,772,[56,63,84],[20,38,60,72,77]],[77,772,[56,60,63],[20,38,72,74,84]],[75,198,[36,70],[]],[41,170,[69,79],[]],[69,170,[41,79],[]],[79,170,[41,69],[]],[83,108,[52,68],[]],[63,897,[],[]],[76,418,[],[]],[80,450,[],[]],[84,928,[],[]]],\"edges\":[[44,[20,38,44,46,56,60,63,72,74,77,84]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,25,26],[-9,20,21,26],[-13,16,20,21,25],[-12,23],[-4],[-1,10,11,14,26],[-18,11,14,26],[-19,10,14,26],[-22,10,11,14],[-20,3,17],[-5,16,23],[-16,5,23],[-23,5,16],[-25,8,15],[-14],[-21],[-24],[-26],[-27,2,9,12,13],[-28,27],[-29,28],[-30,29],[30],[-6,31],[-7,31],[-10,32],[-11,32],[-3,33],[-8,33],[-15,34],[-17,34],[-35,5,20,21,24],[-5,35],[-20,35],[-36,16,25],[-16,36],[-25,36],[-37,23],[-23,37],[-32,38],[-31,38],[-38,39],[-34,40],[-33,40],[-41,36,37],[-37,41],[-36,41],[-36,-37,42],[-43,35,41],[-41,43],[-42,44],[-35,43],[-35,-41,44],[-44,45],[-40,-43,45],[-39,-45,46],[-46],[1,4,6,7,10,11,14,18,19,22,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":164,\"a\":35,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":164,\"a\":53,\"owners\":[75,76,84]},{\"tag\":\"mate\",\"ridge\":164,\"a\":62,\"owners\":[69,75,76,83]},{\"tag\":\"mate\",\"ridge\":224,\"a\":61,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":770,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":772,\"a\":20,\"owners\":[56,60,63,84]},{\"tag\":\"mate\",\"ridge\":772,\"a\":72,\"owners\":[60,63,84]},{\"tag\":\"mate\",\"ridge\":772,\"a\":74,\"owners\":[56,63,84]},{\"tag\":\"mate\",\"ridge\":772,\"a\":77,\"owners\":[56,60,63]},{\"tag\":\"mate\",\"ridge\":198,\"a\":75,\"owners\":[36,70]},{\"tag\":\"mate\",\"ridge\":170,\"a\":41,\"owners\":[69,79]},{\"tag\":\"mate\",\"ridge\":170,\"a\":69,\"owners\":[41,79]},{\"tag\":\"mate\",\"ridge\":170,\"a\":79,\"owners\":[41,69]},{\"tag\":\"mate\",\"ridge\":108,\"a\":83,\"owners\":[52,68]},{\"tag\":\"mate\",\"ridge\":897,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":418,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":450,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":928,\"a\":84,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[35,53,61,62],\"full_literals\":[-27,2,9,12,13]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-29,false,28],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":44,\"full_literals\":[-6,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":46,\"full_literals\":[-7,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":56,\"full_literals\":[-10,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-11,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":36,\"full_literals\":[-3,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-8,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":68,\"full_literals\":[-15,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-17,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[41,75,76,80],\"full_literals\":[-35,5,20,21,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":41,\"full_literals\":[-5,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-20,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[69,83],\"full_literals\":[-36,16,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-16,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-25,36]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[79],\"full_literals\":[-37,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-23,37]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,35,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-42,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-41,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[20,38,44,46,56,60,63,72,74,77,84]}]}"
  "59 29 0 23 22 0\n60 28 0 59 21 0\n61 27 0 60 20 0\n62 -35 5 20 0 16 17 32 0\n63 1 6 7 10 11 18 19 22 0 5 15 18 58 0\n64 38 0 18 15 40 41 26 27 24 25 6 8 9 7 63 0\n65 39 0 64 42 0\n66 -45 0 65 57 56 0\n67 -44 0 66 54 0\n68 -42 0 67 51 0\n69 -37 5 0 68 38 48 13 36 0\n70 -41 25 0 67 53 33 69 39 45 12 35 0\n71 -43 0 66 55 43 44 30 31 28 29 14 10 70 46 47 49 39 36 62 11 0\n72 -41 0 71 50 0\n73 -35 0 71 52 0\n74 -37 0 72 46 0\n75 -36 0 72 47 0\n76 -20 0 73 34 0\n77 -23 0 74 39 0\n78 -16 0 75 36 0\n79 -25 0 75 37 0\n80 -9 0 76 16 18 2 0\n81 -12 0 77 4 0\n82 -13 0 78 76 16 79 3 0\n83 -2 0 79 18 1 0\n84 0 81 82 61 83 80 19 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record035_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1e86b0ecc70dc789ca6a96a3ab1ac99a639b161db0e638ce4b8ae1ba1e4785e6a4e936785c95a5394d51d70d634cd4b4ad1b61d2745dc8da338e531cf0b62ccb4acab1ae1bc1d8731e2749ca719c570de0f43c8f13c2f6918c16b0649a164381e384c9164a58548d0746384c5312c1b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34db6db6d269a4d36926936936d269a49b49369b493692492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 82)]))
 (.leaf ([(facetIndex 58), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 53), (facetIndex 59), (facetIndex 60)]))
 (.branch 4
 (.leaf ([(facetIndex 71), (facetIndex 74), (facetIndex 77), (facetIndex 88)]))
 (.leaf ([(facetIndex 36), (facetIndex 41), (facetIndex 49), (facetIndex 64)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 43), (facetIndex 55), (facetIndex 63)]))
 (.leaf ([(facetIndex 40), (facetIndex 84), (facetIndex 86)])))
 (.branch 8
 (.leaf ([(facetIndex 72), (facetIndex 87), (facetIndex 92)]))
 (.branch 9
 (.leaf ([(facetIndex 79), (facetIndex 83), (facetIndex 90)]))
 (.leaf ([(facetIndex 48), (facetIndex 67), (facetIndex 85)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7081376968000803003073000900450022100502000490000504600042z23;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041" 66

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041" "{\"ridges\":[[12,164],[15,224],[20,770],[20,772],[23,416],[32,164],[37,772],[40,170],[47,224],[48,387],[49,801],[54,164],[61,224],[62,416],[63,801],[64,897],[66,224],[67,297],[72,170],[76,770],[76,772],[78,770],[78,772],[79,198],[80,416],[81,772],[83,170],[85,170],[87,450],[90,108],[91,416],[92,360]],\"owners\":[[12,164,[23,72,79,80,90,91],[32,54,61]],[32,164,[23,90,91],[12,54,61,72,79,80]],[54,164,[23,79,80],[12,32,61,72,90,91]],[15,224,[79,83,87,90,92],[47,61,66]],[47,224,[90,92],[15,61,66,79,83,87]],[61,224,[83,87,92],[15,47,66,79,90]],[66,224,[79,87],[15,47,61,83,90,92]],[20,770,[44,49,82],[37,76,78,81]],[76,770,[49],[20,37,44,78,81,82]],[78,770,[44,49],[20,37,76,81,82]],[20,772,[58,63,64,89],[37,76,78,81]],[37,772,[89],[20,58,63,64,76,78,81]],[76,772,[63,64],[20,37,58,78,81,89]],[78,772,[58,63,64],[20,37,76,81,89]],[81,772,[58,64,89],[20,37,63,76,78]],[23,416,[48,67,85,87,92],[62,80,91]],[62,416,[85,87,92],[23,48,67,80,91]],[80,416,[67,92],[23,48,62,85,87,91]],[91,416,[48,87],[23,62,67,80,85,92]],[79,198,[35,74],[]],[48,387,[36,43],[]],[40,170,[72,83,85],[]],[72,170,[40,83,85],[]],[83,170,[40,72,85],[]],[85,170,[40,72,83],[]],[67,297,[41,55],[]],[49,801,[63],[]],[63,801,[49],[]],[90,108,[53,71],[]],[64,897,[],[]],[92,360,[84],[]],[87,450,[86],[]]],\"edges\":[[36,[12,15,23,32,40,47,48,54,61,62,66,67,72,79,80,83,85,87,90,91,92]],[44,[20,37,44,49,58,63,64,76,78,81,82,89]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,4,27,31,32,41,42],[-5,4,41,42],[-17,4,31,32],[-2,31,35,39,41,43],[-13,41,43],[-20,35,39,43],[-24,31,39],[-3,12,15,34],[-29,15],[-30,12,15],[-3,19,22,23,40],[-8,40],[-29,22,23],[-30,19,22,23],[-33,19,23,40],[-4,14,25,37,39,43],[-21,37,39,43],[-32,25,43],[-42,14,39],[-31,6,28],[-14,7,11],[-9,27,35,37],[-27,9,35,37],[-35,9,27,37],[-37,9,27,35],[-25,10,18],[-15,22],[-22,15],[-41,16,26],[-23],[-43,36],[-39,38],[-12,44],[-34,44],[-19,45],[-40,45],[-6,46],[-16,46],[-26,47],[-28,47],[-7,48],[-10,48],[-15,48],[-11,49],[-18,49],[-22,49],[-9,50],[-36,50],[-38,50],[-51,27,39,43],[-27,51],[-39,51],[-43,51],[-52,31,35,41],[-31,52],[-35,52],[-41,52],[-53,14,25,37],[-14,53],[-25,53],[-37,53],[-45,54],[-44,54],[-48,55],[-47,55],[-55,56],[-46,56],[-56,57],[-54,57],[-54,-56,58],[-50,59],[-49,59],[-60,52,53],[-53,60],[-52,60],[-52,-53,61],[-62,51,60],[-60,62],[-61,63],[-51,62],[-51,-60,63],[-62,64],[-63,65],[-59,-62,65],[-57,-65,66],[-58,-64,66],[-66],[1,2,4,5,9,13,14,17,20,21,24,25,27,31,32,35,37,39,41,42,43],[3,8,12,15,19,22,23,29,30,33,34,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":164,\"a\":12,\"owners\":[23,72,79,80,90,91]},{\"tag\":\"mate\",\"ridge\":164,\"a\":32,\"owners\":[23,90,91]},{\"tag\":\"mate\",\"ridge\":164,\"a\":54,\"owners\":[23,79,80]},{\"tag\":\"mate\",\"ridge\":224,\"a\":15,\"owners\":[79,83,87,90,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":47,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":61,\"owners\":[83,87,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":66,\"owners\":[79,87]},{\"tag\":\"mate\",\"ridge\":770,\"a\":20,\"owners\":[44,49,82]},{\"tag\":\"mate\",\"ridge\":770,\"a\":76,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":770,\"a\":78,\"owners\":[44,49]},{\"tag\":\"mate\",\"ridge\":772,\"a\":20,\"owners\":[58,63,64,89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":37,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":772,\"a\":76,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":772,\"a\":78,\"owners\":[58,63,64]},{\"tag\":\"mate\",\"ridge\":772,\"a\":81,\"owners\":[58,64,89]},{\"tag\":\"mate\",\"ridge\":416,\"a\":23,\"owners\":[48,67,85,87,92]},{\"tag\":\"mate\",\"ridge\":416,\"a\":62,\"owners\":[85,87,92]},{\"tag\":\"mate\",\"ridge\":416,\"a\":80,\"owners\":[67,92]},{\"tag\":\"mate\",\"ridge\":416,\"a\":91,\"owners\":[48,87]},{\"tag\":\"mate\",\"ridge\":198,\"a\":79,\"owners\":[35,74]},{\"tag\":\"mate\",\"ridge\":387,\"a\":48,\"owners\":[36,43]},{\"tag\":\"mate\",\"ridge\":170,\"a\":40,\"owners\":[72,83,85]},{\"tag\":\"mate\",\"ridge\":170,\"a\":72,\"owners\":[40,83,85]},{\"tag\":\"mate\",\"ridge\":170,\"a\":83,\"owners\":[40,72,85]},{\"tag\":\"mate\",\"ridge\":170,\"a\":85,\"owners\":[40,72,83]},{\"tag\":\"mate\",\"ridge\":297,\"a\":67,\"owners\":[41,55]},{\"tag\":\"mate\",\"ridge\":801,\"a\":49,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":801,\"a\":63,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":108,\"a\":90,\"owners\":[53,71]},{\"tag\":\"mate\",\"ridge\":897,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":360,\"a\":92,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":450,\"a\":87,\"owners\":[86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-12,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":82,\"full_literals\":[-34,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":58,\"full_literals\":[-19,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-40,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":35,\"full_literals\":[-6,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-16,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-26,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":74,\"full_literals\":[-28,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":36,\"full_literals\":[-7,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-10,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-15,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":43,\"full_literals\":[-11,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":55,\"full_literals\":[-18,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":63,\"full_literals\":[-22,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":40,\"full_literals\":[-9,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-36,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-38,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[72,87,92],\"full_literals\":[-51,27,39,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":72,\"full_literals\":[-27,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-39,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":92,\"full_literals\":[-43,51]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[79,83,90],\"full_literals\":[-52,31,35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":79,\"full_literals\":[-31,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":83,\"full_literals\":[-35,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":90,\"full_literals\":[-41,52]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[48,67,85],\"full_literals\":[-53,14,25,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":48,\"full_literals\":[-14,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":67,\"full_literals\":[-25,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":85,\"full_literals\":[-37,53]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,51,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-60,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,15,23,32,40,47,48,54,61,62,66,67,72,79,80,83,85,87,90,91,92]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[20,37,44,49,58,63,64,76,78,81,82,89]}]}"
  "90 3 8 12 15 19 22 29 30 33 34 40 0 30 89 0\n91 57 0 30 68 69 66 62 63 64 35 36 33 34 43 12 15 9 28 8 10 90 0\n92 -65 0 91 87 85 0\n93 -63 0 92 83 0\n94 -61 0 93 79 0\n95 -53 25 14 27 9 0 94 58 76 25 56 0\n96 56 -60 59 0 93 81 51 72 45 44 71 47 66 67 64 65 37 38 41 42 39 40 21 26 29 20 95 61 73 24 54 0\n97 54 22 0 30 27 13 62 63 35 36 33 34 11 14 12 15 90 0\n98 -62 58 0 92 84 71 72 47 48 49 46 31 32 97 70 96 74 75 77 61 56 50 23 0\n99 62 0 78 80 74 75 51 52 53 59 60 61 55 56 57 22 19 18 17 16 7 6 4 5 1 2 3 88 0\n100 64 0 99 82 0\n101 58 0 99 98 0\n102 0 101 100 87 86 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record041_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record041

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7938ccb1ac6732a668da1e9c6c9966658d61db0e63a2e4ba1e4789e0fb89ca5a93a4d91e785c95a539475c368d6362d4b4ad8749d0f72334c73c2d8b32e2b4ac6b86c9b16c3bc1d8791cc789d2785c970de0f43c8f0bc1f3530a4ab0649866158d1264c5194951546314e0b0ac1b81c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db69b6d26926d36db6da6db49b6db69b4936924924d249249b489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 28), (facetIndex 38), (facetIndex 47), (facetIndex 50), (facetIndex 64)])))
 (.branch 3
 (.leaf ([(facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 30), (facetIndex 73), (facetIndex 80), (facetIndex 81)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 76), (facetIndex 86)]))
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 29), (facetIndex 31), (facetIndex 35)])))
 (.branch 7
 (.leaf ([(facetIndex 23), (facetIndex 36), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 22), (facetIndex 37), (facetIndex 46)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10001b0940180000010000000000403e01b6c7ea00ae9b40dcz10;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 49), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 82), (facetIndex 91)]))
 (.branch 4
 (.leaf ([(facetIndex 24), (facetIndex 34), (facetIndex 79), (facetIndex 84)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 85)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 25), (facetIndex 44), (facetIndex 48), (facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 53), (facetIndex 61), (facetIndex 66), (facetIndex 68)])))
 (.branch 8
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 67)]))
 (.branch 9
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 56), (facetIndex 57), (facetIndex 69), (facetIndex 74), (facetIndex 75), (facetIndex 87)]))
 (.leaf ([(facetIndex 72), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "29998043120030008809448676000565008877688015000500000000030000000053z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
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
def grouped3_0011 : List Nat := [0, 1]
def grouped3_0012 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049" "{\"atoms\":[{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049" "{\"ridges\":[[30,292],[34,387],[34,388],[44,387],[44,392],[45,776],[55,392],[60,388],[62,388],[66,392],[68,392],[72,540],[75,142],[75,392],[79,402],[82,450],[85,402],[87,284],[87,392],[88,172],[88,392],[89,556],[90,392],[90,652],[91,480]],\"owners\":[[30,292,[88,89,91],[17,53,60,61,73,80,81]],[45,776,[89,90],[20,57,67,68,76,86]],[75,142,[24,70],[]],[34,387,[44],[]],[44,387,[34],[]],[34,388,[87,88,90,91],[55,60,62,75,79,82]],[60,388,[75,79,82,87,90],[34,55,62,88,91]],[62,388,[75,79,82,87,88,91],[34,55,60,90]],[44,392,[87,88,90],[55,66,68,75,85]],[55,392,[85],[44,66,68,75,87,88,90]],[66,392,[75,85,87,90],[44,55,68,88]],[68,392,[75,85,87,88],[44,55,66,90]],[75,392,[66,68],[44,55,85,87,88,90]],[87,392,[44,66,68],[55,75,85,88,90]],[88,392,[44,68,85],[55,66,75,87,90]],[90,392,[44,66,85],[55,68,75,87,88]],[72,540,[51],[]],[88,172,[52],[]],[89,556,[54,74],[]],[90,652,[56],[]],[87,284,[71],[]],[79,402,[85],[]],[85,402,[79],[]],[82,450,[],[]],[91,480,[],[]]],\"edges\":[[42,[34,44,55,60,62,66,68,75,79,82,85,87,88,90,91]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-21,-18],[-25,-22],[-26,-24],[-28,-23],[-29,-28],[-2,31,32,34],[-5,32,33],[-20,1,15],[-3,4],[-4,3],[-3,30,31,33,34],[-11,20,24,27,30,33],[-12,20,24,27,30,31,34],[-4,30,31,33],[-9,28],[-13,20,28,30,33],[-14,20,28,30,31],[-20,13,14],[-30,4,13,14],[-31,4,14,28],[-33,4,13,28],[-17,6],[-31,7],[-32,8,19],[-33,10],[-30,16],[-24,28],[-28,24],[-27],[-34],[-35,22,23],[-36,2,18,25,26],[-37,5,21,29],[-38,35],[-38,36],[-39,38],[-40,37],[-41,40],[-42,39],[-42,41],[42],[-1,43],[-3,43],[-24,43],[-15,44],[-16,44],[-28,44],[-4,45],[-11,45],[-12,45],[-13,46],[-14,46],[-8,47],[-6,48],[-7,48],[-10,48],[-19,48],[-20,48],[-30,48],[-49,17,31,32,33],[-31,49],[-32,49],[-33,49],[-44,50],[-43,50],[-50,51],[-51,52],[-46,53],[-45,53],[-49,54],[-48,54],[-48,-49,55],[-54,56],[-55,57],[-47,-54,57],[-57,58],[-53,-56,58],[-53,-57,59],[-59,60],[-52,-58,60],[-60],[3,4,9,11,12,13,14,20,24,27,28,30,31,33,34]],\"atoms\":[{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":85,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"mate\",\"ridge\":292,\"a\":30,\"owners\":[88,89,91]},{\"tag\":\"mate\",\"ridge\":776,\"a\":45,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":142,\"a\":75,\"owners\":[24,70]},{\"tag\":\"mate\",\"ridge\":387,\"a\":34,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":387,\"a\":44,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":388,\"a\":34,\"owners\":[87,88,90,91]},{\"tag\":\"mate\",\"ridge\":388,\"a\":60,\"owners\":[75,79,82,87,90]},{\"tag\":\"mate\",\"ridge\":388,\"a\":62,\"owners\":[75,79,82,87,88,91]},{\"tag\":\"mate\",\"ridge\":392,\"a\":44,\"owners\":[87,88,90]},{\"tag\":\"mate\",\"ridge\":392,\"a\":55,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":392,\"a\":66,\"owners\":[75,85,87,90]},{\"tag\":\"mate\",\"ridge\":392,\"a\":68,\"owners\":[75,85,87,88]},{\"tag\":\"mate\",\"ridge\":392,\"a\":75,\"owners\":[66,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":87,\"owners\":[44,66,68]},{\"tag\":\"mate\",\"ridge\":392,\"a\":88,\"owners\":[44,68,85]},{\"tag\":\"mate\",\"ridge\":392,\"a\":90,\"owners\":[44,66,85]},{\"tag\":\"mate\",\"ridge\":540,\"a\":72,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":172,\"a\":88,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":556,\"a\":89,\"owners\":[54,74]},{\"tag\":\"mate\",\"ridge\":652,\"a\":90,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":284,\"a\":87,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":402,\"a\":79,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":402,\"a\":85,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":450,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":480,\"a\":91,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[77,78],\"full_literals\":[-35,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[30,73,80,81],\"full_literals\":[-36,2,18,25,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[45,76,86],\"full_literals\":[-37,5,21,29]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-41,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-42,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-42,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":24,\"full_literals\":[-1,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":34,\"full_literals\":[-3,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-24,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-15,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-16,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-28,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":44,\"full_literals\":[-4,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-11,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":62,\"full_literals\":[-12,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-13,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-14,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":54,\"full_literals\":[-8,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":51,\"full_literals\":[-6,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":52,\"full_literals\":[-7,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":56,\"full_literals\":[-10,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-19,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":75,\"full_literals\":[-20,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-30,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[72,88,89,90],\"full_literals\":[-49,17,31,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":88,\"full_literals\":[-31,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":89,\"full_literals\":[-32,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":90,\"full_literals\":[-33,49]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-49,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-52,-58,60],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[34,44,55,60,62,66,68,75,79,82,85,87,88,90,91]}]}"
  "83 39 0 41 39 0\n84 41 0 41 40 0\n85 38 0 83 36 0\n86 40 0 84 38 0\n87 35 0 85 34 0\n88 36 0 85 35 0\n89 37 0 86 37 0\n90 -59 0 81 79 0\n91 3 4 9 11 12 13 14 20 24 28 30 31 33 0 29 30 82 0\n92 53 50 0 65 43 10 64 47 15 46 26 42 45 8 44 68 69 51 52 49 50 21 20 91 0\n93 31 33 50 0 30 29 65 42 64 45 8 46 26 47 16 44 12 43 10 15 13 17 91 0\n94 -31 55 0 23 61 55 72 0\n95 50 0 90 92 78 74 94 93 25 63 56 72 0\n96 51 0 95 66 0\n97 52 0 96 67 0\n98 -58 0 97 81 80 0\n99 -57 0 98 76 0\n100 -55 0 99 74 0\n101 -31 0 100 94 0\n102 -33 0 100 25 63 56 72 0\n103 -49 0 100 99 102 101 70 72 75 54 57 53 22 24 60 0\n104 -32 0 103 62 0\n105 -5 0 104 102 7 0\n106 -2 0 104 101 30 6 0\n107 28 48 0 30 29 101 102 59 14 11 58 15 27 17 16 13 12 91 0\n108 -28 0 87 105 89 106 88 4 5 28 31 33 3 2 1 32 0\n109 -9 0 108 15 0\n110 -24 0 108 27 0\n111 48 0 108 107 0\n112 54 0 111 71 0\n113 56 0 112 73 0\n114 -53 0 113 98 77 0\n115 -46 0 114 68 0\n116 -45 0 114 69 0\n117 -13 0 115 51 0\n118 -14 0 115 52 0\n119 -4 0 116 48 0\n120 -11 0 116 49 0\n121 -12 0 116 50 0\n122 -20 0 117 118 18 0\n123 -3 0 119 9 0\n124 -30 0 119 117 118 19 0\n125 0 121 120 102 123 119 109 118 122 110 108 124 117 101 91 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00020.record049_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00020.record049
