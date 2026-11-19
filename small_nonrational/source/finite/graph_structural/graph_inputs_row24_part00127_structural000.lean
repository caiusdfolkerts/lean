module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00127Data
public import GraphInputsRow24Part00127Frames
public import GraphInputsRow24Part00127Leaves
public import GraphInputsRow24Part00127Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000
def vertexColumn : Fields := ⟨10, hexnat% "dc2745d26c3b25cd8b52cca725caaa9aa5a56a6659a5655a364d87693a2e2b86e8789e17a715c6693a65956565395554d475334ad1b49d68e6358e5354e334cc7392d4b8acab1ae1b46c9b16d4749c6745c9715c3713c2f9605c868a62381e58551164a5194552344d0752328d1322c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6db6da6db6db6d34934da4926924934d34db69a493492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efffffb6edbffffffffffff", 10133099161583616, 9295429630892703744, hexnat% "10000001000000000000000", hexnat% "40000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffd366fff7abdfffffff", hexnat% "200000004000000000", 9223380832947798016, hexnat% "10000001800000000000000", 72057594574798848, hexnat% "c0000001400000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffffffdcd77b7fbffffff", 8830519869440, 4503874505277440, 153122387330596864, 703687441776640]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd7fffd77a7ffffffff", hexnat% "200000004000000000", hexnat% "10100080000000000000000", 103079215104, 712483534798848]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdffdcd77a3e8ffffff", 712483534798848, 157625986974744576, hexnat% "200000004010000000", 120259084288, 100663296]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd1e7c3dfa9ffffffff", 16888498602639360, hexnat% "200000004000000000", 576495945265446912, hexnat% "c0000001400000000", hexnat% "10100021000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efefff56197dfedffffffff", 173388585653764096, hexnat% "1000a0000001200000000", 9511602413006487552, hexnat% "10000001800000000000000", 35184372088832]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffd3fd83ffa3deffffff", 120795955200, 173388585653764096, hexnat% "200010004001000000", hexnat% "c0000000000000000", 1125899906842624]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨8, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨12, by decide⟩ c12 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c11 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff7fdbfffffffffffff", hexnat% "80000000000000000", 162129586585337856]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffff7dbdffbfffffffff", 563224831328256, 162129586585337856, 9223372036854775808]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd775bfffffffffffff", 162129586585337856, hexnat% "200000000000000000", 9799832789158199296, hexnat% "10100080000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd7effdffa7ffffffff", hexnat% "200000004000000000", hexnat% "80000001800000000", 562949953421312, hexnat% "10100001000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efefff7e1bdd7e77fffffff", 571748193927168, 450359962737049600, hexnat% "100001000001000000000", 576495971035250688, hexnat% "10000080000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c11 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffff77ffdffbfffffffff", 9223372036854775808, hexnat% "80000000000000000", 563224831328256]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffd777fdffbfffffffff", 563224831328256, 9799832789158199296, hexnat% "10000080000000000000000", hexnat% "200000000000000000"]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdf79fdffbf7fffffff", 9511602413006487552, hexnat% "200000004000000000", 562952100904960, 144115188075855872]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efffff761fdf7ef7fffffff", hexnat% "80000001000000000", 432345566375051264, 571746046443520, hexnat% "10000001800000000000000", 9223372036854775808]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdfffcdf7bfffffffff", 571746046443520, 13510798882111488, hexnat% "200000004000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffdf7dcdf7bf7fffffff", 9223380832947798016, 157625986957967360, hexnat% "200000004000000000", 562952100904960]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffff69ddf7ff7fffffff", 153122387330596864, hexnat% "10000001000000000000000", 571748193927168, 9511602413006487552]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffffb79cdf7ab7fffffff", 157625986957967360, 9223380832947798016, hexnat% "40000001400000000", 563226978811904, 288230376151711744]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c43 c40
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffdd6187dfffffffffff", hexnat% "200018000000000000", 171136785840078848, hexnat% "10100021000000000000000", 9799867973530288128, 288230376151711744]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3efeffd16187d7e5dfffffff", 159877786771652608, 9529616811515969536, hexnat% "240000000000000000", hexnat% "10000001800000200000000", 44015361720320, hexnat% "1000a0000001000000000"]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c48 c37
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c49 c26
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c50 c10
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c51 c9
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c52 c8
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c53 c7
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c54 c2
  c55
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "25c8f25a8e93a599564d89e1783ed8751cc6a9966394e66559655556354d64d8b61d2745d0f5a398d6394e334ce4b8ad2b86d1b26c5b0ed4731d2719d1725c3713cac548aa298562382e07a51546292a619294552342d0754348ca344c5322c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da69269a49b6936d24926934d2492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 45), (facetIndex 53), (facetIndex 57), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 54), (facetIndex 61), (facetIndex 62), (facetIndex 67), (facetIndex 70)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 76)]))
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 50), (facetIndex 52)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 42)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4092040200048006c45148a05df10db6db4z17;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006" 18

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006" "{\"ridges\":[[52,289],[69,816],[71,864]],\"owners\":[[52,289,[59,63,65,69,71],[11,36,44,47,50]],[69,816,[],[]],[71,864,[],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-2,-1],[-3,-1],[-4,-1],[-8,-1],[-11,-6],[-11,-7],[-5,6,7,8,9,10],[-9],[-10],[-12,11],[-13,2,3,4,5],[-14,1],[-15,12],[-15,13],[-16,14],[-17,15],[-17,16],[-18,17],[18]],\"atoms\":[{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":42},{\"tag\":\"incompatible\",\"a\":76,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":63},{\"tag\":\"mate\",\"ridge\":289,\"a\":52,\"owners\":[59,63,65,69,71]},{\"tag\":\"mate\",\"ridge\":816,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":864,\"a\":71,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[76],\"full_literals\":[-12,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[44,47,50,52],\"full_literals\":[-13,2,3,4,5]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[42],\"full_literals\":[-14,1]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-15,12,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-15,false,13],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-16,false,14],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-17,15,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-17,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-18,false,17],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 18 19\n-2 -1 0\n-3 -1 0\n-4 -1 0\n-8 -1 0\n-11 -6 0\n-11 -7 0\n-5 6 7 8 9 10 0\n-9 0\n-10 0\n-12 11 0\n-13 2 3 4 5 0\n-14 1 0\n-15 12 0\n-15 13 0\n-16 14 0\n-17 15 0\n-17 16 0\n-18 17 0\n18 0\n"
  "20 17 0 19 18 0\n21 15 0 20 16 0\n22 16 0 20 17 0\n23 12 0 21 13 0\n24 13 0 21 14 0\n25 14 0 22 15 0\n26 11 0 23 10 0\n27 1 0 25 12 0\n28 -6 0 26 5 0\n29 -7 0 26 6 0\n30 -2 0 27 1 0\n31 -3 0 27 2 0\n32 -4 0 27 3 0\n33 -8 0 27 4 0\n34 -5 0 28 29 33 8 9 7 0\n35 0 30 31 24 32 34 11 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "25c2f1b24e8ba99966559362da4e8b8ae2785e0fb616c6a9965392e66559655555352d64d2b61d2745d0f5a398d6364cd34ccb392e2b4ad1b16c3b91d4789d2729c6745c970de0f23c4f8b1522a89a1582e079518a4a926645894558342d0754348ca344c9314c8b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da6d36d249369b49a4da49249a492692492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 47), (facetIndex 69)]))
 (.branch 2
 (.leaf ([(facetIndex 78), (facetIndex 88)]))
 (.leaf ([(facetIndex 53), (facetIndex 65), (facetIndex 72)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 68), (facetIndex 71)]))
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 85), (facetIndex 86)])))
 (.branch 6
 (.leaf ([(facetIndex 87)]))
 (.leaf ([(facetIndex 82), (facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b20d848400026030100d800001z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022" 40

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022" "{\"ridges\":[[11,289],[11,290],[18,577],[18,580],[38,290],[41,577],[41,580],[45,289],[45,290],[47,586],[49,289],[49,290],[52,290],[53,610],[54,289],[54,290],[60,577],[60,580],[64,577],[64,580],[65,356],[66,577],[66,580],[69,600],[72,864],[78,586],[83,610],[88,600]],\"owners\":[[11,289,[62,65,68,71,72],[38,45,49,52,54]],[45,289,[62,65,71,72],[11,38,49,52,54,68]],[49,289,[65,72],[11,38,45,52,54,62,68,71]],[54,289,[62,65,68,72],[11,38,45,49,52,71]],[11,290,[80,82,85,86],[38,45,49,52,54]],[38,290,[85,86],[11,45,49,52,54,80,82]],[45,290,[80,82,86],[11,38,49,52,54,85]],[49,290,[82],[11,38,45,52,54,80,85,86]],[52,290,[80,85,86],[11,38,45,49,54,82]],[54,290,[80,82,85],[11,38,45,49,52,86]],[18,577,[47,53,69,72],[41,60,64,66]],[41,577,[69,72],[18,47,53,60,64,66]],[60,577,[53,72],[18,41,47,64,66,69]],[64,577,[47,53,72],[18,41,60,66,69]],[66,577,[47,69],[18,41,53,60,64,72]],[18,580,[78,83,88],[41,60,64,66]],[41,580,[88],[18,60,64,66,78,83]],[60,580,[83],[18,41,64,66,78,88]],[64,580,[78,83],[18,41,60,66,88]],[66,580,[78,88],[18,41,60,64,83]],[47,586,[78],[]],[78,586,[47],[]],[53,610,[83],[]],[83,610,[53],[]],[65,356,[82],[]],[69,600,[88],[]],[88,600,[69],[]],[72,864,[],[]]],\"edges\":[[37,[11,38,45,49,52,54,62,65,68,71,72,80,82,85,86]],[41,[18,41,47,53,60,64,66,69,72,78,83,88]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-23,-14],[-23,-22],[-1,12,14,16,18,19],[-5,12,14,18,19],[-7,14,19],[-10,12,14,16,19],[-1,21,22,24,25],[-3,24,25],[-5,21,22,25],[-7,22],[-8,21,24,25],[-10,21,22,24],[-2,6,9,17,19],[-4,17,19],[-11,9,19],[-13,6,9,19],[-15,6,17],[-2,20,23,26],[-4,26],[-11,23],[-13,20,23],[-15,20,26],[-6,20],[-20,6],[-9,23],[-23,9],[-14,22],[-17,26],[-26,17],[-19],[-6,27],[-17,27],[-20,28],[-26,28],[-9,29],[-12,30],[-16,30],[-18,30],[-21,31],[-24,31],[-25,31],[-22,32],[-23,32],[-29,33],[-28,33],[-33,34],[-27,34],[-27,-33,35],[-31,36],[-30,36],[-32,37],[-37,38],[-36,38],[-36,-37,39],[-34,-39,40],[-35,-38,40],[-40],[1,3,5,7,8,10,12,14,16,18,19,21,22,24,25],[2,4,6,9,11,13,15,17,19,20,23,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"mate\",\"ridge\":289,\"a\":11,\"owners\":[62,65,68,71,72]},{\"tag\":\"mate\",\"ridge\":289,\"a\":45,\"owners\":[62,65,71,72]},{\"tag\":\"mate\",\"ridge\":289,\"a\":49,\"owners\":[65,72]},{\"tag\":\"mate\",\"ridge\":289,\"a\":54,\"owners\":[62,65,68,72]},{\"tag\":\"mate\",\"ridge\":290,\"a\":11,\"owners\":[80,82,85,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":38,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":45,\"owners\":[80,82,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":49,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":52,\"owners\":[80,85,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":54,\"owners\":[80,82,85]},{\"tag\":\"mate\",\"ridge\":577,\"a\":18,\"owners\":[47,53,69,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":41,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":60,\"owners\":[53,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":64,\"owners\":[47,53,72]},{\"tag\":\"mate\",\"ridge\":577,\"a\":66,\"owners\":[47,69]},{\"tag\":\"mate\",\"ridge\":580,\"a\":18,\"owners\":[78,83,88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":41,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":60,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":64,\"owners\":[78,83]},{\"tag\":\"mate\",\"ridge\":580,\"a\":66,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":586,\"a\":47,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":586,\"a\":78,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":610,\"a\":53,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":610,\"a\":83,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":356,\"a\":65,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":600,\"a\":69,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":600,\"a\":88,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":864,\"a\":72,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":47,\"full_literals\":[-6,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-17,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-26,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-9,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-12,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-16,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-18,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-24,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-25,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-22,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-23,32]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,38,45,49,52,54,62,65,68,71,72,80,82,85,86]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[18,41,47,53,60,64,66,69,72,78,83,88]}]}"
  "p cnf 40 59\n-23 -14 0\n-23 -22 0\n-1 12 14 16 18 19 0\n-5 12 14 18 19 0\n-7 14 19 0\n-10 12 14 16 19 0\n-1 21 22 24 25 0\n-3 24 25 0\n-5 21 22 25 0\n-7 22 0\n-8 21 24 25 0\n-10 21 22 24 0\n-2 6 9 17 19 0\n-4 17 19 0\n-11 9 19 0\n-13 6 9 19 0\n-15 6 17 0\n-2 20 23 26 0\n-4 26 0\n-11 23 0\n-13 20 23 0\n-15 20 26 0\n-6 20 0\n-20 6 0\n-9 23 0\n-23 9 0\n-14 22 0\n-17 26 0\n-26 17 0\n-19 0\n-6 27 0\n-17 27 0\n-20 28 0\n-26 28 0\n-9 29 0\n-12 30 0\n-16 30 0\n-18 30 0\n-21 31 0\n-24 31 0\n-25 31 0\n-22 32 0\n-23 32 0\n-29 33 0\n-28 33 0\n-33 34 0\n-27 34 0\n-27 -33 35 0\n-31 36 0\n-30 36 0\n-32 37 0\n-37 38 0\n-36 38 0\n-36 -37 39 0\n-34 -39 40 0\n-35 -38 40 0\n-40 0\n1 3 5 7 8 10 12 14 16 18 19 21 22 24 25 0\n2 4 6 9 11 13 15 17 19 20 23 26 0\n"
  "60 1 3 5 7 8 10 12 14 16 18 21 22 24 25 0 30 58 0\n61 2 4 6 9 11 13 15 17 20 23 26 0 30 59 0\n62 34 0 30 46 47 44 45 31 32 35 33 34 14 17 13 15 26 16 61 0\n63 -39 0 62 57 55 0\n64 11 15 2 9 4 6 17 26 20 23 0 61 21 0\n65 33 0 30 44 45 35 33 34 15 26 23 19 28 22 18 64 0\n66 23 27 0 30 31 32 17 29 14 24 20 25 18 64 0\n67 36 -23 0 30 1 5 2 49 50 39 40 41 36 37 38 11 8 3 4 6 60 0\n68 -23 0 63 67 43 54 51 0\n69 27 0 68 66 0\n70 35 0 69 65 48 0\n71 -38 0 70 57 56 0\n72 -37 0 71 52 0\n73 -36 0 71 53 0\n74 -32 0 72 51 0\n75 -31 0 73 49 0\n76 -30 0 73 50 0\n77 -22 0 74 42 0\n78 -21 0 75 39 0\n79 -24 0 75 40 0\n80 -25 0 75 41 0\n81 -12 0 76 36 0\n82 -16 0 76 37 0\n83 -18 0 76 38 0\n84 -7 0 77 10 0\n85 -14 0 77 27 0\n86 -8 0 78 79 80 11 0\n87 -10 0 78 77 79 12 0\n88 -1 0 78 77 79 80 7 0\n89 -5 0 78 77 80 9 0\n90 -3 0 80 79 8 0\n91 0 88 87 90 84 89 86 81 85 82 83 78 77 79 80 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9d26c3707c5c96a2e87a8d8765386e2785e0fb615c669364b91e665a54d58d4759354d3362d1b49d1743d58d538cd332cc7362d4b2ac6b26c5b0ed4789c6785c570dd0f13c2f07e705a2544a89623a61586518c471525291a645854951548d1352324c3342c8b0ac8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "136da6db6d36926d24924934934d24924934db492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 41), (facetIndex 53), (facetIndex 54), (facetIndex 65), (facetIndex 73)]))
 (.leaf ([(facetIndex 31), (facetIndex 34), (facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 51), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 55), (facetIndex 60), (facetIndex 61), (facetIndex 64), (facetIndex 85)]))
 (.leaf ([(facetIndex 32), (facetIndex 43), (facetIndex 45)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 59)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1000100000016d002912ff8400236c5964000085328z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025" "{\"atoms\":[{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025" 40

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025" "{\"ridges\":[[55,76],[57,76],[58,76],[59,76]],\"owners\":[[55,76,[72,75,83],[9,31,53,57,58,59,74,82,84]],[57,76,[72,74,75,82,84],[9,31,53,55,58,59,83]],[58,76,[72,74,82,83,84],[9,31,53,55,57,59,75]],[59,76,[72,74,75,82,83],[9,31,53,55,57,58,84]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-22,-3],[-22,-5],[-22,-8],[-22,-9],[-22,-10],[-22,-11],[-24,-2],[-24,-4],[-24,-18],[-24,-19],[-24,-20],[-25,-3],[-25,-5],[-25,-8],[-25,-9],[-25,-10],[-25,-11],[-26,-22],[-26,-25],[-27,-2],[-27,-4],[-27,-18],[-27,-19],[-27,-20],[-28,-1],[-28,-6],[-28,-7],[-28,-12],[-28,-13],[-28,-21],[-28,-23],[-29,-2],[-29,-4],[-29,-18],[-29,-19],[-29,-20],[-30,-24],[-30,-27],[-30,-29],[-14,22,25,28],[-15,22,24,25,27,29],[-16,22,24,27,28,29],[-17,22,24,25,27,28],[-31,1,6,7,12,13,21,23],[-32,3,5,8,9,10,11,26],[-33,2,4,14,18,19,20,30],[-34,15,16,17],[-35,31],[-35,32],[-36,33],[-37,35],[-37,36],[-38,34],[-39,38],[-40,37],[-40,39],[40]],\"atoms\":[{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":72,\"b\":31},{\"tag\":\"incompatible\",\"a\":72,\"b\":34},{\"tag\":\"incompatible\",\"a\":72,\"b\":42},{\"tag\":\"incompatible\",\"a\":72,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":46},{\"tag\":\"incompatible\",\"a\":72,\"b\":51},{\"tag\":\"incompatible\",\"a\":74,\"b\":30},{\"tag\":\"incompatible\",\"a\":74,\"b\":33},{\"tag\":\"incompatible\",\"a\":74,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":74,\"b\":64},{\"tag\":\"incompatible\",\"a\":75,\"b\":31},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":75,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":44},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":75,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":75},{\"tag\":\"incompatible\",\"a\":82,\"b\":30},{\"tag\":\"incompatible\",\"a\":82,\"b\":33},{\"tag\":\"incompatible\",\"a\":82,\"b\":60},{\"tag\":\"incompatible\",\"a\":82,\"b\":61},{\"tag\":\"incompatible\",\"a\":82,\"b\":64},{\"tag\":\"incompatible\",\"a\":83,\"b\":29},{\"tag\":\"incompatible\",\"a\":83,\"b\":39},{\"tag\":\"incompatible\",\"a\":83,\"b\":41},{\"tag\":\"incompatible\",\"a\":83,\"b\":53},{\"tag\":\"incompatible\",\"a\":83,\"b\":54},{\"tag\":\"incompatible\",\"a\":83,\"b\":65},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":84,\"b\":30},{\"tag\":\"incompatible\",\"a\":84,\"b\":33},{\"tag\":\"incompatible\",\"a\":84,\"b\":60},{\"tag\":\"incompatible\",\"a\":84,\"b\":61},{\"tag\":\"incompatible\",\"a\":84,\"b\":64},{\"tag\":\"incompatible\",\"a\":85,\"b\":74},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"mate\",\"ridge\":76,\"a\":55,\"owners\":[72,75,83]},{\"tag\":\"mate\",\"ridge\":76,\"a\":57,\"owners\":[72,74,75,82,84]},{\"tag\":\"mate\",\"ridge\":76,\"a\":58,\"owners\":[72,74,82,83,84]},{\"tag\":\"mate\",\"ridge\":76,\"a\":59,\"owners\":[72,74,75,82,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[29,39,41,53,54,65,73],\"full_literals\":[-31,1,6,7,12,13,21,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,34,42,44,46,51,80],\"full_literals\":[-32,3,5,8,9,10,11,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,33,55,60,61,64,85],\"full_literals\":[-33,2,4,14,18,19,20,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[57,58,59],\"full_literals\":[-34,15,16,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 40 57\n-22 -3 0\n-22 -5 0\n-22 -8 0\n-22 -9 0\n-22 -10 0\n-22 -11 0\n-24 -2 0\n-24 -4 0\n-24 -18 0\n-24 -19 0\n-24 -20 0\n-25 -3 0\n-25 -5 0\n-25 -8 0\n-25 -9 0\n-25 -10 0\n-25 -11 0\n-26 -22 0\n-26 -25 0\n-27 -2 0\n-27 -4 0\n-27 -18 0\n-27 -19 0\n-27 -20 0\n-28 -1 0\n-28 -6 0\n-28 -7 0\n-28 -12 0\n-28 -13 0\n-28 -21 0\n-28 -23 0\n-29 -2 0\n-29 -4 0\n-29 -18 0\n-29 -19 0\n-29 -20 0\n-30 -24 0\n-30 -27 0\n-30 -29 0\n-14 22 25 28 0\n-15 22 24 25 27 29 0\n-16 22 24 27 28 29 0\n-17 22 24 25 27 28 0\n-31 1 6 7 12 13 21 23 0\n-32 3 5 8 9 10 11 26 0\n-33 2 4 14 18 19 20 30 0\n-34 15 16 17 0\n-35 31 0\n-35 32 0\n-36 33 0\n-37 35 0\n-37 36 0\n-38 34 0\n-39 38 0\n-40 37 0\n-40 39 0\n40 0\n"
  "58 37 0 57 55 0\n59 39 0 57 56 0\n60 35 0 58 51 0\n61 36 0 58 52 0\n62 38 0 59 54 0\n63 31 0 60 48 0\n64 32 0 60 49 0\n65 33 0 61 50 0\n66 34 0 62 53 0\n67 -27 4 14 0 65 20 22 23 24 38 46 0\n68 28 27 22 29 24 25 0 66 41 43 42 47 0\n69 -28 12 6 0 63 25 27 29 30 31 44 0\n70 22 28 29 24 25 0 40 68 21 67 0\n71 -22 0 64 1 2 3 4 5 6 18 45 0\n72 -29 14 0 65 32 33 34 35 36 39 46 0\n73 25 28 0 65 71 40 72 70 7 8 9 10 11 37 46 0\n74 -25 0 64 12 13 14 15 16 17 19 45 0\n75 28 0 74 73 0\n76 -6 0 75 26 0\n77 -12 0 75 28 0\n78 0 75 77 76 69 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00127.record025_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00127.record025
