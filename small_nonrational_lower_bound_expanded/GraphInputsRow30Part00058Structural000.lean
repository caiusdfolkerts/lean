module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow30Part00058Data
public import GraphInputsRow30Part00058Frames
public import GraphInputsRow30Part00058Leaves
public import GraphInputsRow30Part00058Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 2), (certNat% 3), (certNat% 4)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record035_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3d0ec37332ac9b29c9723cb2aaa9aa9a96a3ab1aa699a9695a368e635a364d8b61d8ce8b92e2b86e8791e2785ecc6b16c6715c4f1ca6a96a6695a4e9c669966659564d9394d58d5352d4753362d4b4ad1b61d4749d17723a8da398d6338f13a4d9394d5334e334ccb31cf0ba2d8b92d4b32e2b4acab1ae1b46c9b16cc789d2785d170de0f43c2f07ca6198961588e138a5194951548d1362348ca318e1344c9314e0b42c8b12c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6db6db6da4da49b49b49b6db6db6db6db49b493693692492492492492492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 69), (facetIndex 70), (facetIndex 102), (facetIndex 103)]))
 (.branch 2
 (.leaf ([(facetIndex 30), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 73), (facetIndex 74), (facetIndex 106), (facetIndex 107)]))
 (.leaf ([(facetIndex 33), (facetIndex 38), (facetIndex 53), (facetIndex 54), (facetIndex 78), (facetIndex 79), (facetIndex 111), (facetIndex 112)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62)])))
 (.branch 6
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 77), (facetIndex 82), (facetIndex 83), (facetIndex 110), (facetIndex 115), (facetIndex 116)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6c0258024z10;d804b0048005b6db249248936db6492000ad91364z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [3, 4, 5, 6]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6]
def grouped2_0010 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":130},{\"tag\":\"facet\",\"index\":132},{\"tag\":\"facet\",\"index\":134},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016" "{\"ridges\":[[11,273],[34,273],[41,273],[42,529],[55,273],[58,273],[60,273],[62,273],[89,792],[101,816],[104,284],[113,308],[118,344],[120,408],[130,368],[132,432]],\"owners\":[[11,273,[71,80,85,87,89,97,99,101],[34,41,55,58,60,62]],[34,273,[85,87,89,97,99,101],[11,41,55,58,60,62,71,80]],[41,273,[80,97,99,101],[11,34,55,58,60,62,71,85,87,89]],[55,273,[71,85,87,89],[11,34,41,58,60,62,80,97,99,101]],[58,273,[71,80,87,89,99,101],[11,34,41,55,60,62,85,97]],[60,273,[71,80,85,89,97,101],[11,34,41,55,58,62,87,99]],[62,273,[71,80,85,87,97,99],[11,34,41,55,58,60,89,101]],[42,529,[81,98,100,101],[12,35,56,59,61,62,72,86,88,89]],[104,284,[71],[]],[113,308,[80],[]],[118,344,[85],[]],[120,408,[87],[]],[89,792,[122],[]],[130,368,[97],[]],[132,432,[99],[]],[101,816,[134],[]]],\"edges\":[[33,[11,34,41,55,58,60,62,71,80,85,87,89,97,99,101,104,113,118,120,122,130,132,134]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-18,-2],[-18,-6],[-18,-7],[-18,-16],[-18,-17],[-19,-5],[-22,-3],[-22,-10],[-22,-11],[-22,-20],[-22,-21],[-23,-3],[-23,-10],[-23,-11],[-23,-20],[-23,-21],[-24,-5],[-25,-5],[-26,-2],[-26,-6],[-26,-7],[-26,-16],[-26,-17],[-27,-2],[-27,-6],[-27,-7],[-27,-16],[-27,-17],[-29,-3],[-29,-10],[-29,-11],[-29,-20],[-29,-21],[-30,-3],[-30,-10],[-30,-11],[-30,-20],[-30,-21],[-31,-3],[-31,-10],[-31,-11],[-31,-20],[-31,-21],[-32,-3],[-32,-10],[-32,-11],[-32,-20],[-32,-21],[-34,-18],[-34,-26],[-34,-27],[-35,-18],[-35,-26],[-35,-27],[-37,-5],[-38,-22],[-38,-23],[-38,-29],[-38,-30],[-38,-31],[-38,-32],[-39,-22],[-39,-23],[-39,-29],[-39,-30],[-39,-31],[-39,-32],[-41,-5],[-42,-5],[-45,-2],[-45,-6],[-45,-7],[-45,-16],[-45,-17],[-45,-34],[-45,-35],[-48,-3],[-48,-10],[-48,-11],[-48,-20],[-48,-21],[-48,-38],[-48,-39],[-1,18,22,26,27,28,29,31,33],[-4,26,27,28,29,31,33],[-8,22,29,31,33],[-12,18,26,27,28],[-13,18,22,27,28,31,33],[-14,18,22,26,28,29,33],[-15,18,22,26,27,29,31],[-9,23,30,32,33],[-36,18],[-40,22],[-43,26],[-44,27],[-28,45],[-46,29],[-47,31],[-33,48],[-49,2,6,7,8,9,16,17,34,35],[-50,3,5,10,11,20,21,38,39],[-51,19,24,25,37,41,42],[-52,50],[-53,49],[-53,52],[-54,51],[-55,54],[-56,53],[-56,55],[56],[1,4,8,12,13,14,15,18,22,26,27,28,29,31,33,36,40,43,44,45,46,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":122},{\"tag\":\"facet\",\"index\":130},{\"tag\":\"facet\",\"index\":132},{\"tag\":\"facet\",\"index\":134},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":33},{\"tag\":\"incompatible\",\"a\":80,\"b\":53},{\"tag\":\"incompatible\",\"a\":80,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":81,\"b\":33},{\"tag\":\"incompatible\",\"a\":81,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":54},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":79},{\"tag\":\"incompatible\",\"a\":82,\"b\":38},{\"tag\":\"incompatible\",\"a\":83,\"b\":38},{\"tag\":\"incompatible\",\"a\":85,\"b\":29},{\"tag\":\"incompatible\",\"a\":85,\"b\":39},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":69},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":87,\"b\":29},{\"tag\":\"incompatible\",\"a\":87,\"b\":39},{\"tag\":\"incompatible\",\"a\":87,\"b\":40},{\"tag\":\"incompatible\",\"a\":87,\"b\":69},{\"tag\":\"incompatible\",\"a\":87,\"b\":70},{\"tag\":\"incompatible\",\"a\":97,\"b\":33},{\"tag\":\"incompatible\",\"a\":97,\"b\":53},{\"tag\":\"incompatible\",\"a\":97,\"b\":54},{\"tag\":\"incompatible\",\"a\":97,\"b\":78},{\"tag\":\"incompatible\",\"a\":97,\"b\":79},{\"tag\":\"incompatible\",\"a\":98,\"b\":33},{\"tag\":\"incompatible\",\"a\":98,\"b\":53},{\"tag\":\"incompatible\",\"a\":98,\"b\":54},{\"tag\":\"incompatible\",\"a\":98,\"b\":78},{\"tag\":\"incompatible\",\"a\":98,\"b\":79},{\"tag\":\"incompatible\",\"a\":99,\"b\":33},{\"tag\":\"incompatible\",\"a\":99,\"b\":53},{\"tag\":\"incompatible\",\"a\":99,\"b\":54},{\"tag\":\"incompatible\",\"a\":99,\"b\":78},{\"tag\":\"incompatible\",\"a\":99,\"b\":79},{\"tag\":\"incompatible\",\"a\":100,\"b\":33},{\"tag\":\"incompatible\",\"a\":100,\"b\":53},{\"tag\":\"incompatible\",\"a\":100,\"b\":54},{\"tag\":\"incompatible\",\"a\":100,\"b\":78},{\"tag\":\"incompatible\",\"a\":100,\"b\":79},{\"tag\":\"incompatible\",\"a\":102,\"b\":71},{\"tag\":\"incompatible\",\"a\":102,\"b\":85},{\"tag\":\"incompatible\",\"a\":102,\"b\":87},{\"tag\":\"incompatible\",\"a\":103,\"b\":71},{\"tag\":\"incompatible\",\"a\":103,\"b\":85},{\"tag\":\"incompatible\",\"a\":103,\"b\":87},{\"tag\":\"incompatible\",\"a\":110,\"b\":38},{\"tag\":\"incompatible\",\"a\":111,\"b\":80},{\"tag\":\"incompatible\",\"a\":111,\"b\":81},{\"tag\":\"incompatible\",\"a\":111,\"b\":97},{\"tag\":\"incompatible\",\"a\":111,\"b\":98},{\"tag\":\"incompatible\",\"a\":111,\"b\":99},{\"tag\":\"incompatible\",\"a\":111,\"b\":100},{\"tag\":\"incompatible\",\"a\":112,\"b\":80},{\"tag\":\"incompatible\",\"a\":112,\"b\":81},{\"tag\":\"incompatible\",\"a\":112,\"b\":97},{\"tag\":\"incompatible\",\"a\":112,\"b\":98},{\"tag\":\"incompatible\",\"a\":112,\"b\":99},{\"tag\":\"incompatible\",\"a\":112,\"b\":100},{\"tag\":\"incompatible\",\"a\":115,\"b\":38},{\"tag\":\"incompatible\",\"a\":116,\"b\":38},{\"tag\":\"incompatible\",\"a\":122,\"b\":29},{\"tag\":\"incompatible\",\"a\":122,\"b\":39},{\"tag\":\"incompatible\",\"a\":122,\"b\":40},{\"tag\":\"incompatible\",\"a\":122,\"b\":69},{\"tag\":\"incompatible\",\"a\":122,\"b\":70},{\"tag\":\"incompatible\",\"a\":122,\"b\":102},{\"tag\":\"incompatible\",\"a\":122,\"b\":103},{\"tag\":\"incompatible\",\"a\":134,\"b\":33},{\"tag\":\"incompatible\",\"a\":134,\"b\":53},{\"tag\":\"incompatible\",\"a\":134,\"b\":54},{\"tag\":\"incompatible\",\"a\":134,\"b\":78},{\"tag\":\"incompatible\",\"a\":134,\"b\":79},{\"tag\":\"incompatible\",\"a\":134,\"b\":111},{\"tag\":\"incompatible\",\"a\":134,\"b\":112},{\"tag\":\"mate\",\"ridge\":273,\"a\":11,\"owners\":[71,80,85,87,89,97,99,101]},{\"tag\":\"mate\",\"ridge\":273,\"a\":34,\"owners\":[85,87,89,97,99,101]},{\"tag\":\"mate\",\"ridge\":273,\"a\":41,\"owners\":[80,97,99,101]},{\"tag\":\"mate\",\"ridge\":273,\"a\":55,\"owners\":[71,85,87,89]},{\"tag\":\"mate\",\"ridge\":273,\"a\":58,\"owners\":[71,80,87,89,99,101]},{\"tag\":\"mate\",\"ridge\":273,\"a\":60,\"owners\":[71,80,85,89,97,101]},{\"tag\":\"mate\",\"ridge\":273,\"a\":62,\"owners\":[71,80,85,87,97,99]},{\"tag\":\"mate\",\"ridge\":529,\"a\":42,\"owners\":[81,98,100,101]},{\"tag\":\"mate\",\"ridge\":284,\"a\":104,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":308,\"a\":113,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":344,\"a\":118,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":408,\"a\":120,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":792,\"a\":89,\"owners\":[122]},{\"tag\":\"mate\",\"ridge\":368,\"a\":130,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":432,\"a\":132,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":816,\"a\":101,\"owners\":[134]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[29,39,40,41,42,69,70,102,103],\"full_literals\":[-49,2,6,7,8,9,16,17,34,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[33,38,53,54,78,79,111,112],\"full_literals\":[-50,3,5,10,11,20,21,38,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[77,82,83,110,115,116],\"full_literals\":[-51,19,24,25,37,41,42]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-56,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,34,41,55,58,60,62,71,80,85,87,89,97,99,101,104,113,118,120,122,130,132,134]}]}"
  "112 53 0 110 108 0\n113 55 0 110 109 0\n114 49 0 112 104 0\n115 52 0 112 105 0\n116 54 0 113 107 0\n117 50 0 115 103 0\n118 51 0 116 106 0\n119 -5 0 118 6 17 18 55 68 69 102 0\n120 -48 0 119 117 77 78 79 80 81 82 83 101 0\n121 -33 0 120 99 0\n122 -22 0 119 117 7 8 9 10 11 56 62 101 0\n123 -40 0 122 93 0\n124 -29 0 119 117 29 30 31 32 33 58 64 101 0\n125 -46 0 124 97 0\n126 -31 0 119 117 39 40 41 42 43 60 66 101 0\n127 -47 0 126 98 0\n128 -8 0 126 122 124 121 86 0\n129 -23 0 119 117 12 13 14 15 16 57 63 101 0\n130 -30 0 119 117 34 35 36 37 38 59 65 101 0\n131 -32 0 119 117 44 45 46 47 48 61 67 101 0\n132 -9 0 130 129 131 121 91 0\n133 18 26 27 15 45 0 120 122 123 121 126 124 128 125 127 96 85 94 95 87 92 84 88 89 111 0\n134 -18 0 132 128 114 1 2 3 4 5 49 52 100 0\n135 -26 0 132 128 114 19 20 21 22 23 50 53 100 0\n136 -27 0 132 128 114 24 25 26 27 28 51 54 100 0\n137 -15 0 136 122 134 135 124 126 90 0\n138 45 0 137 134 135 136 133 0\n139 -2 0 138 70 0\n140 -6 0 138 71 0\n141 -7 0 138 72 0\n142 -16 0 138 73 0\n143 -17 0 138 74 0\n144 -34 0 138 75 0\n145 -35 0 138 76 0\n146 0 144 145 114 139 140 141 128 132 142 143 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016 Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record016_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f83b0dc3a8dac9aa669a66598e6c5a9665a56558d633a2e4b8ae1ba1e4789e17b31ac5b19c5713c4e9366394e4b91e725a95a59956539715a559595555354cd8b52d8751d2745dc8ea368e6358ce3c4e9364e5354cd332e2b4acab1ae1b46f07a1d8791d4731e2749ca719e1745c9715e0f43c2f07cac1b09a1688e138a91a49916625494a51948d1342d84d1324c5322c4b06e0741c8711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d369b6db6db6d36936936db6936924924db6da49b49b6db492493692492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 72), (facetIndex 85), (facetIndex 86), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 29), (facetIndex 97), (facetIndex 98), (facetIndex 105), (facetIndex 118)])))
 (.branch 3
 (.leaf ([(facetIndex 30), (facetIndex 101), (facetIndex 102), (facetIndex 121)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 47), (facetIndex 48), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 70), (facetIndex 71), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 66)]))
 (.leaf ([(facetIndex 50), (facetIndex 67)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10040000000008090048000000004924800000900f800006db6c01f376db6c9236dda88z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

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

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021" "{\"ridges\":[[15,37],[17,37],[17,289],[18,37],[18,545],[39,292],[40,548],[65,289],[65,802],[70,289],[71,545],[80,289],[81,545],[82,289],[83,545],[84,289],[84,545],[87,312],[88,568],[92,368],[93,624],[94,432],[95,688],[96,816],[103,298],[113,354],[115,418],[117,292],[117,548],[117,802],[121,100]],\"owners\":[[121,100,[15,37,80,81,113,114],[27,79,101,112]],[17,289,[51,61,63,65,87,92,94,96],[39,70,80,82,84]],[65,289,[17,70,80,82,87,92,94],[39,51,61,63,84,96]],[70,289,[61,63,65,92,94,96],[17,39,51,80,82,84,87]],[80,289,[51,63,65,87,94,96],[17,39,61,70,82,84,92]],[82,289,[51,61,65,87,92,96],[17,39,63,70,80,84,94]],[84,289,[51,61,63,87,92,94],[17,39,65,70,80,82,96]],[39,292,[],[17,70,80,82,84,103,113,115,117]],[117,292,[17,70,80,82],[39,84,103,113,115]],[18,545,[52,62,64,65,88,93,95,96],[40,71,81,83,84]],[71,545,[62,64,65,93,95,96],[18,40,52,81,83,84,88]],[81,545,[52,64,65,88,95,96],[18,40,62,71,83,84,93]],[83,545,[52,62,65,88,93,96],[18,40,64,71,81,84,95]],[84,545,[52,62,64,88,93,95],[18,40,65,71,81,83,96]],[40,548,[],[18,71,81,83,84,104,114,116,117]],[117,548,[18,71,81,83],[40,84,104,114,116]],[103,298,[51],[]],[113,354,[61],[]],[115,418,[63],[]],[65,802,[117],[]],[117,802,[65],[]],[87,312,[],[]],[88,568,[],[]],[92,368,[],[]],[93,624,[],[]],[94,432,[],[]],[95,688,[],[]],[96,816,[],[]]],\"edges\":[[37,[17,39,51,61,63,65,70,80,82,84,87,92,94,96,103,113,115,117]],[38,[18,40,52,62,64,65,71,81,83,84,88,93,95,96,104,114,116,117]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-9],[-11,-10],[-12,-9],[-12,-11],[-13,-10],[-13,-12],[-14,-9],[-14,-11],[-14,-13],[-16,-3],[-17,-2],[-17,-16],[-18,-3],[-19,-3],[-19,-17],[-20,-2],[-20,-16],[-20,-19],[-21,-3],[-21,-17],[-21,-20],[-22,-2],[-22,-16],[-22,-19],[-22,-21],[-34,-9],[-34,-11],[-34,-13],[-36,-9],[-36,-11],[-36,-13],[-38,-9],[-38,-11],[-38,-13],[-39,-4],[-39,-5],[-39,-6],[-39,-23],[-39,-31],[-39,-32],[-39,-35],[-39,-36],[-1,-2,-3],[-40,1,5,19,20,35,36],[-2,9,11,13,15,24,26,28,30],[-15,2,16,19,21,24,26,28],[-16,11,13,15,26,28,30],[-19,9,13,15,24,28,30],[-21,9,11,15,24,26,30],[-23,9,11,13,24,26,28],[-7],[-39,2,16,19,21],[-3,10,12,14,15,25,27,29,30],[-17,12,14,15,27,29,30],[-20,10,14,15,25,29,30],[-22,10,12,15,25,27,30],[-23,10,12,14,25,27,29],[-8],[-39,3,17,20,22],[-33,9],[-35,11],[-37,13],[-15,39],[-39,15],[-24],[-25],[-26],[-27],[-28],[-29],[-30],[-41,4,31,32,40],[-42,5,6,7,8,16,17,18,19,20,21,22,23],[-43,41],[-44,43],[-45,42],[-46,45],[-47,44,46],[47],[2,7,9,11,13,15,16,19,21,23,24,26,28,30,33,35,37,39],[3,8,10,12,14,15,17,20,22,23,25,27,29,30,34,36,38,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":61,\"b\":52},{\"tag\":\"incompatible\",\"a\":62,\"b\":51},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":51},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":70,\"b\":18},{\"tag\":\"incompatible\",\"a\":71,\"b\":17},{\"tag\":\"incompatible\",\"a\":71,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":18},{\"tag\":\"incompatible\",\"a\":80,\"b\":18},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":81,\"b\":17},{\"tag\":\"incompatible\",\"a\":81,\"b\":70},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":18},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":17},{\"tag\":\"incompatible\",\"a\":83,\"b\":70},{\"tag\":\"incompatible\",\"a\":83,\"b\":80},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":104,\"b\":51},{\"tag\":\"incompatible\",\"a\":104,\"b\":61},{\"tag\":\"incompatible\",\"a\":104,\"b\":63},{\"tag\":\"incompatible\",\"a\":114,\"b\":51},{\"tag\":\"incompatible\",\"a\":114,\"b\":61},{\"tag\":\"incompatible\",\"a\":114,\"b\":63},{\"tag\":\"incompatible\",\"a\":116,\"b\":51},{\"tag\":\"incompatible\",\"a\":116,\"b\":61},{\"tag\":\"incompatible\",\"a\":116,\"b\":63},{\"tag\":\"incompatible\",\"a\":117,\"b\":30},{\"tag\":\"incompatible\",\"a\":117,\"b\":37},{\"tag\":\"incompatible\",\"a\":117,\"b\":38},{\"tag\":\"incompatible\",\"a\":117,\"b\":84},{\"tag\":\"incompatible\",\"a\":117,\"b\":101},{\"tag\":\"incompatible\",\"a\":117,\"b\":102},{\"tag\":\"incompatible\",\"a\":117,\"b\":113},{\"tag\":\"incompatible\",\"a\":117,\"b\":114},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[15,17,18]},{\"tag\":\"mate\",\"ridge\":100,\"a\":121,\"owners\":[15,37,80,81,113,114]},{\"tag\":\"mate\",\"ridge\":289,\"a\":17,\"owners\":[51,61,63,65,87,92,94,96]},{\"tag\":\"mate\",\"ridge\":289,\"a\":65,\"owners\":[17,70,80,82,87,92,94]},{\"tag\":\"mate\",\"ridge\":289,\"a\":70,\"owners\":[61,63,65,92,94,96]},{\"tag\":\"mate\",\"ridge\":289,\"a\":80,\"owners\":[51,63,65,87,94,96]},{\"tag\":\"mate\",\"ridge\":289,\"a\":82,\"owners\":[51,61,65,87,92,96]},{\"tag\":\"mate\",\"ridge\":289,\"a\":84,\"owners\":[51,61,63,87,92,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":292,\"a\":117,\"owners\":[17,70,80,82]},{\"tag\":\"mate\",\"ridge\":545,\"a\":18,\"owners\":[52,62,64,65,88,93,95,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":71,\"owners\":[62,64,65,93,95,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":81,\"owners\":[52,64,65,88,95,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":83,\"owners\":[52,62,65,88,93,96]},{\"tag\":\"mate\",\"ridge\":545,\"a\":84,\"owners\":[52,62,64,88,93,95]},{\"tag\":\"mate\",\"ridge\":548,\"a\":40,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":548,\"a\":117,\"owners\":[18,71,81,83]},{\"tag\":\"mate\",\"ridge\":298,\"a\":103,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":354,\"a\":113,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":418,\"a\":115,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":802,\"a\":65,\"owners\":[117]},{\"tag\":\"mate\",\"ridge\":802,\"a\":117,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":312,\"a\":87,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":568,\"a\":88,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":92,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":93,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":94,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":95,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":96,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[30,101,102,121],\"full_literals\":[-41,4,31,32,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,38,39,40,70,71,79,80,81,82,83,84],\"full_literals\":[-42,5,6,7,8,16,17,18,19,20,21,22,23]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-47,44,46],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[17,39,51,61,63,65,70,80,82,84,87,92,94,96,103,113,115,117]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[18,40,52,62,64,65,71,81,83,84,88,93,95,96,104,114,116,117]}]}"
  "82 -42 5 6 16 17 18 19 20 21 22 23 0 51 58 73 0\n83 2 9 11 13 15 16 19 21 23 33 35 37 39 0 51 65 67 69 71 80 0\n84 3 10 12 14 15 17 20 22 23 34 36 38 39 0 58 66 68 70 71 81 0\n85 9 15 11 13 0 65 69 71 67 45 60 47 61 49 50 62 48 64 83 0\n86 -9 39 0 68 71 70 66 63 1 3 7 26 29 32 53 54 56 57 55 84 0\n87 -11 39 0 68 71 70 66 63 2 4 8 27 30 33 53 54 56 57 55 84 0\n88 39 0 68 71 70 66 63 86 87 85 5 6 9 28 31 34 53 54 56 57 55 84 0\n89 -4 0 88 35 0\n90 -5 0 88 36 0\n91 -6 0 88 37 0\n92 -23 0 88 38 0\n93 -31 0 88 39 0\n94 -32 0 88 40 0\n95 -35 0 88 41 0\n96 -36 0 88 42 0\n97 15 0 88 64 0\n98 17 20 22 0 89 93 94 79 90 95 96 97 65 67 69 91 92 88 59 10 13 14 19 82 46 76 43 77 44 78 72 75 74 0\n99 -17 0 88 11 12 15 20 52 0\n100 -20 0 88 16 17 18 21 52 0\n101 22 0 100 99 98 0\n102 -2 0 101 22 0\n103 -16 0 101 23 0\n104 -19 0 101 24 0\n105 -21 0 101 25 0\n106 0 104 102 103 88 105 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021 Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00058.record021_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00058.record021
