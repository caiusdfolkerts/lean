module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00083Data
public import GraphInputsRow26Part00083Frames
public import GraphInputsRow26Part00083Leaves
public import GraphInputsRow26Part00083Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1729395451049803776, (certNat% 3), 989010709708800, (certNat% 4), (certNat% 5)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record019_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "332ac9b2caa6a5ab1a39a364d8b68b92e1ba1e4789e17b31ac5b1ca6695a719396354d4b58b52d1b61d4749d17723a8da398d6338f13a4d938cd332cf0b92d4b8ad2b1ac9b16cc789d2785d1715c3783d0f23c2f8691a298662584e07a19464a5194951341d88d2328c6384d1324e0b42c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69369b4924db6da4da6d2492492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 35), (facetIndex 40), (facetIndex 43), (facetIndex 65), (facetIndex 83)]))
 (.leaf ([(facetIndex 34), (facetIndex 68), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 86), (facetIndex 89)]))
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 90)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 41), (facetIndex 42), (facetIndex 46), (facetIndex 47), (facetIndex 48)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 44), (facetIndex 45), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1100801248000032010036dfffffb6db5b7f168ff606daz17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 69), (facetIndex 70), (facetIndex 76), (facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 84), (facetIndex 85), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 94), (facetIndex 95), (facetIndex 96)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "3fa83ca00150014z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [2, 3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012" "{\"ridges\":[[16,13],[17,69],[20,161],[23,22],[24,70],[25,22],[26,70],[27,134],[35,22],[35,69],[35,70],[45,545],[58,161],[59,161],[63,13],[64,13],[66,300],[67,556],[69,308],[70,564],[71,69],[71,100],[71,164],[76,161],[77,161],[81,22],[82,22],[84,300],[85,556],[89,164]],\"owners\":[[16,13,[0,17,30,31,32,33,65,66,67],[62,63,64]],[63,13,[0,17,30,31,33,65,67],[16,32,62,64,66]],[64,13,[0,17,30,31,32,65,66],[16,33,62,63,67]],[27,134,[4,25,31,40,80],[89]],[45,545,[70,77,78],[15,39,51,57,59,60,67,74,75]],[71,100,[26,83],[19,65,89]],[71,164,[27,86],[20,68,89]],[89,164,[20,68],[27,71,86]],[66,300,[84],[]],[84,300,[66],[]],[67,556,[85],[]],[85,556,[67],[]],[69,308,[87],[]],[70,564,[88],[]]],\"edges\":[[17,[0,16,17,23,24,30,31,32,33,61,62,63,64,65,66,67,79,80,81,82,83,84,85]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-1],[-16,-2],[-16,-12],[-16,-13],[-16,-14],[-16,-15],[-17,-16],[-18,-16],[-19,-11],[-20,-11],[-21,-15],[-22,-19],[-22,-20],[-23,-11],[-23,-22],[-24,-11],[-24,-22],[-28,-16],[-29,-16],[-30,-16],[-31,-11],[-31,-22],[-32,-11],[-32,-22],[-33,-11],[-33,-22],[-34,-11],[-34,-22],[-35,-11],[-35,-22],[-36,-11],[-36,-22],[-37,-16],[-38,-16],[-42,-41],[-43,-41],[-44,-21],[-44,-25],[-44,-26],[-44,-27],[-47,-21],[-47,-42],[-47,-43],[-48,-41],[-49,-41],[-50,-41],[-51,-25],[-51,-26],[-51,-27],[-51,-28],[-51,-34],[-51,-44],[-52,-25],[-52,-26],[-52,-27],[-52,-29],[-52,-35],[-52,-44],[-53,-25],[-53,-26],[-53,-27],[-53,-30],[-53,-44],[-54,-16],[-55,-16],[-58,-42],[-58,-43],[-58,-48],[-58,-49],[-58,-50],[-61,-45],[-61,-46],[-61,-51],[-61,-52],[-61,-53],[-64,-11],[-64,-15],[-64,-19],[-64,-20],[-64,-21],[-64,-31],[-64,-47],[-64,-58],[-64,-59],[-64,-60],[-64,-62],[-64,-63],[-3,1,4,11,12,13,14,41,42,43],[-39,1,4,11,12,14,41,43],[-40,1,4,11,12,13,41,42],[-6,-8,-16],[-8,-16,-56],[-8,-16,-57],[-4,-16,-47],[-7,-9,-16],[-10,2,8,12,21,55],[-5,-34,-52],[-5,-35,-51],[-24,46,52,53],[-47,9,58],[-47,10,61],[-64,5,44],[-42,59],[-59,42],[-43,60],[-60,43],[-45,62],[-46,63],[-65,11,16,21,22,41,58],[-66,15,44,47],[-67,61,64],[-68,17,18,25,26,27,28,29,30],[-69,19,20,23,24,31,32,33,34,35,36],[-70,65,66],[-71,65],[-71,66],[-72,67],[-73,70],[-73,71,72],[-74,71],[-74,72],[-75,68],[-75,69],[-76,75],[-77,73],[-77,74,76],[77],[-78,42,43,48,49,50],[-79,45,46,51,52,53],[-80,78],[-80,79],[-81,80],[81],[1,3,4,6,7,11,12,13,14,37,38,39,40,41,42,43,54,55,56,57,58,59,60]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":0},{\"tag\":\"incompatible\",\"a\":35,\"b\":4},{\"tag\":\"incompatible\",\"a\":35,\"b\":31},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":40,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":35},{\"tag\":\"incompatible\",\"a\":54,\"b\":35},{\"tag\":\"incompatible\",\"a\":55,\"b\":30},{\"tag\":\"incompatible\",\"a\":55,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":30},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":57,\"b\":30},{\"tag\":\"incompatible\",\"a\":57,\"b\":43},{\"tag\":\"incompatible\",\"a\":58,\"b\":30},{\"tag\":\"incompatible\",\"a\":58,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":30},{\"tag\":\"incompatible\",\"a\":59,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":30},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":61,\"b\":35},{\"tag\":\"incompatible\",\"a\":62,\"b\":35},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":40},{\"tag\":\"incompatible\",\"a\":68,\"b\":49},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":51},{\"tag\":\"incompatible\",\"a\":71,\"b\":40},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":76,\"b\":49},{\"tag\":\"incompatible\",\"a\":76,\"b\":50},{\"tag\":\"incompatible\",\"a\":76,\"b\":51},{\"tag\":\"incompatible\",\"a\":76,\"b\":52},{\"tag\":\"incompatible\",\"a\":76,\"b\":58},{\"tag\":\"incompatible\",\"a\":76,\"b\":68},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":77,\"b\":51},{\"tag\":\"incompatible\",\"a\":77,\"b\":53},{\"tag\":\"incompatible\",\"a\":77,\"b\":59},{\"tag\":\"incompatible\",\"a\":77,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":49},{\"tag\":\"incompatible\",\"a\":78,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":54},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":35},{\"tag\":\"incompatible\",\"a\":80,\"b\":35},{\"tag\":\"incompatible\",\"a\":83,\"b\":66},{\"tag\":\"incompatible\",\"a\":83,\"b\":67},{\"tag\":\"incompatible\",\"a\":83,\"b\":73},{\"tag\":\"incompatible\",\"a\":83,\"b\":74},{\"tag\":\"incompatible\",\"a\":83,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":69},{\"tag\":\"incompatible\",\"a\":86,\"b\":70},{\"tag\":\"incompatible\",\"a\":86,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":77},{\"tag\":\"incompatible\",\"a\":86,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":30},{\"tag\":\"incompatible\",\"a\":89,\"b\":34},{\"tag\":\"incompatible\",\"a\":89,\"b\":38},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":40},{\"tag\":\"incompatible\",\"a\":89,\"b\":55},{\"tag\":\"incompatible\",\"a\":89,\"b\":71},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":85},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"mate\",\"ridge\":13,\"a\":16,\"owners\":[0,17,30,31,32,33,65,66,67]},{\"tag\":\"mate\",\"ridge\":13,\"a\":63,\"owners\":[0,17,30,31,33,65,67]},{\"tag\":\"mate\",\"ridge\":13,\"a\":64,\"owners\":[0,17,30,31,32,65,66]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[23,25,35]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,35,81]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[25,35,82]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[17,35,71]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[24,26,35]},{\"tag\":\"mate\",\"ridge\":134,\"a\":27,\"owners\":[4,25,31,40,80]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[20,58,77]},{\"tag\":\"three\",\"ridge\":161,\"vertices\":[20,59,76]},{\"tag\":\"mate\",\"ridge\":545,\"a\":45,\"owners\":[70,77,78]},{\"tag\":\"mate\",\"ridge\":100,\"a\":71,\"owners\":[26,83]},{\"tag\":\"mate\",\"ridge\":164,\"a\":71,\"owners\":[27,86]},{\"tag\":\"mate\",\"ridge\":164,\"a\":89,\"owners\":[20,68]},{\"tag\":\"mate\",\"ridge\":300,\"a\":66,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":300,\"a\":84,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":556,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":556,\"a\":85,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":308,\"a\":69,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":564,\"a\":70,\"owners\":[88]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[30,35,40,43,65,83],\"full_literals\":[-65,11,16,21,22,41,58]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[34,68,71],\"full_literals\":[-66,15,44,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[86,89],\"full_literals\":[-67,61,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,37,49,50,51,52,53,54],\"full_literals\":[-68,17,18,25,26,27,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[38,39,44,45,55,56,57,58,59,60],\"full_literals\":[-69,19,20,23,24,31,32,33,34,35,36]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,65,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,71,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-74,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,68,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-77,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-77,74,76],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[66,67,73,74,75],\"full_literals\":[-78,42,43,48,49,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[69,70,76,77,78],\"full_literals\":[-79,45,46,51,52,53]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-80,78,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-81,80,false],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":17,\"owners\":[0,16,17,23,24,30,31,32,33,61,62,63,64,65,66,67,79,80,81,82,83,84,85]}]}"
  "135 73 0 127 125 0\n136 70 0 135 118 0\n137 80 0 133 132 0\n138 78 0 137 130 0\n139 79 0 137 131 0\n140 -61 0 139 71 72 73 74 75 129 0\n141 -44 -64 0 139 87 108 86 107 52 58 63 129 0\n142 -41 -64 0 138 85 105 84 103 44 45 46 128 0\n143 -22 35 34 24 -64 -69 0 81 79 78 15 24 26 32 113 0\n144 52 53 -64 -75 0 136 139 142 82 77 141 110 114 102 87 108 86 107 83 80 76 123 122 99 129 47 48 49 50 51 98 143 109 7 8 19 20 112 0\n145 -16 -52 -68 0 56 55 54 53 7 8 18 20 112 0\n146 -52 -64 -75 0 136 142 82 77 141 110 114 102 83 80 76 123 122 57 97 145 109 17 143 0\n147 -22 -64 -69 0 17 28 30 143 0\n148 -64 -75 0 136 123 122 76 77 80 82 83 141 110 114 142 146 144 59 60 61 62 147 109 7 8 18 19 112 0\n149 -58 0 138 66 67 68 69 70 128 0\n150 -47 -16 21 11 41 0 140 149 65 64 34 33 5 4 3 2 1 42 43 101 100 94 104 106 96 95 88 90 89 91 92 93 134 0\n151 21 11 41 22 -75 0 140 135 149 148 111 117 119 116 115 122 109 6 7 8 18 19 20 150 110 38 39 40 112 0\n152 -21 -66 0 11 37 41 110 0\n153 -11 -69 0 9 10 14 16 21 23 25 27 29 31 113 0\n154 -41 0 138 35 36 44 45 46 128 0\n155 -75 0 140 135 154 123 148 111 117 119 116 152 153 151 12 13 15 17 22 24 26 28 30 32 113 0\n156 -76 0 155 124 0\n157 74 0 156 127 126 0\n158 71 0 157 120 0\n159 72 0 157 121 0\n160 66 0 158 116 0\n161 67 0 159 117 0\n162 64 0 161 140 111 0\n163 -15 0 162 77 0\n164 -47 0 162 82 0\n165 -44 0 162 141 0\n166 0 165 163 164 160 110 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "26c6ca3a4e8ba69966399968b92e2b86e8791e2785ecc6b16c6698e5392e725a95a59956539715a55959362d4b4ad1b51d2745d68d6338d938cd332ce2b4acab86d1b26c5b0ed8751cc789d2729c6785c5783d0f23c2f8706a458961381e8a46986615454958344d0752328c6344c9312c2b06d0721c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6da6da4926da4db6db69249b49249269249249249a492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 59), (facetIndex 62), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 38), (facetIndex 39), (facetIndex 40)]))
 (.leaf ([(facetIndex 41), (facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 54), (facetIndex 55)])))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 52)]))
 (.leaf ([(facetIndex 48)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "30016db002400000000440200b6e16fb76dac901240921z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 73), (facetIndex 74), (facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 95)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 60), (facetIndex 61), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87), (facetIndex 89), (facetIndex 90), (facetIndex 91), (facetIndex 96)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "355fcfc000002aa800a000000000008z12;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
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
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [2]
def grouped3_0020 : List Nat := [2, 3]
def grouped3_0021 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013" 55

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013" "{\"ridges\":[[10,35],[11,35],[48,35],[48,545],[69,97],[71,676],[72,804],[77,161],[78,688],[79,816]],\"owners\":[[69,97,[10,20,53,54],[34,59,67,68,76]],[77,161,[11,35,46,53,60,67,71],[49,55,70,73,78]],[48,545,[69,71,72,78,79],[21,37,51,62,75,76]],[71,676,[],[]],[72,804,[],[]],[78,688,[],[]],[79,816,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-4],[-6,-4],[-7,-4],[-11,-8],[-11,-9],[-11,-10],[-12,-4],[-13,-4],[-14,-4],[-16,-3],[-16,-15],[-17,-16],[-18,-16],[-19,-16],[-20,-11],[-21,-8],[-21,-9],[-21,-10],[-21,-16],[-21,-20],[-22,-8],[-22,-9],[-22,-10],[-22,-20],[-24,-23],[-25,-8],[-25,-9],[-25,-10],[-25,-20],[-26,-8],[-26,-9],[-26,-10],[-26,-20],[-27,-8],[-27,-9],[-27,-10],[-27,-20],[-27,-25],[-28,-8],[-28,-9],[-28,-10],[-28,-20],[-31,-16],[-32,-16],[-33,-23],[-34,-23],[-38,-11],[-38,-21],[-38,-22],[-38,-25],[-38,-26],[-38,-27],[-38,-28],[-1,-2,-16],[-27,1,3,18,19],[-35,2,9,15,18,21,25,29],[-16,27,29,30,36,37],[-29],[-30],[-36],[-37],[-39,4,8,9,10,20,23,38],[-40,24,33,34],[-41,5,6,7,12,13,14],[-42,16],[-43,39],[-44,40],[-45,43],[-45,44],[-46,41],[-47,42],[-48,46,47],[-49,47],[-50,45,49],[-50,48],[50],[-51,17,31,32,35,36,37],[-52,11,21,22,25,26,27,28,29,30],[-53,51],[-54,52],[-55,53],[-55,54],[55]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":28},{\"tag\":\"incompatible\",\"a\":30,\"b\":28},{\"tag\":\"incompatible\",\"a\":31,\"b\":28},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":28},{\"tag\":\"incompatible\",\"a\":39,\"b\":28},{\"tag\":\"incompatible\",\"a\":40,\"b\":28},{\"tag\":\"incompatible\",\"a\":48,\"b\":20},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":37},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":35},{\"tag\":\"incompatible\",\"a\":60,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":48},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":34},{\"tag\":\"incompatible\",\"a\":61,\"b\":35},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":61,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":34},{\"tag\":\"incompatible\",\"a\":67,\"b\":35},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":34},{\"tag\":\"incompatible\",\"a\":68,\"b\":35},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":69,\"b\":34},{\"tag\":\"incompatible\",\"a\":69,\"b\":35},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":59},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":35},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":48},{\"tag\":\"incompatible\",\"a\":74,\"b\":48},{\"tag\":\"incompatible\",\"a\":75,\"b\":62},{\"tag\":\"incompatible\",\"a\":76,\"b\":62},{\"tag\":\"incompatible\",\"a\":84,\"b\":37},{\"tag\":\"incompatible\",\"a\":84,\"b\":60},{\"tag\":\"incompatible\",\"a\":84,\"b\":61},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":84,\"b\":68},{\"tag\":\"incompatible\",\"a\":84,\"b\":69},{\"tag\":\"incompatible\",\"a\":84,\"b\":70},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[10,11,48]},{\"tag\":\"mate\",\"ridge\":97,\"a\":69,\"owners\":[10,20,53,54]},{\"tag\":\"mate\",\"ridge\":161,\"a\":77,\"owners\":[11,35,46,53,60,67,71]},{\"tag\":\"mate\",\"ridge\":545,\"a\":48,\"owners\":[69,71,72,78,79]},{\"tag\":\"mate\",\"ridge\":676,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":79,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[28,34,35,36,59,62,84],\"full_literals\":[-39,4,8,9,10,20,23,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[63,75,76],\"full_literals\":[-40,24,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[29,30,31,38,39,40],\"full_literals\":[-41,5,6,7,12,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48],\"full_literals\":[-42,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,46,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-50,45,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[51,73,74,77,78,79],\"full_literals\":[-51,17,31,32,35,36,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[37,60,61,67,68,69,70,71,72],\"full_literals\":[-52,11,21,22,25,26,27,28,29,30]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,51,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,52,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true}]}"
  "84 48 0 76 75 0\n85 -51 17 31 32 35 0 60 61 77 0\n86 -52 11 21 22 25 26 27 28 0 58 59 78 0\n87 53 0 83 81 0\n88 54 0 83 82 0\n89 51 0 87 79 0\n90 52 0 88 80 0\n91 -16 0 61 60 59 89 58 10 11 12 13 14 19 43 44 57 55 85 35 38 54 56 0\n92 -42 0 91 65 0\n93 -47 0 92 71 0\n94 -49 0 93 73 0\n95 46 0 93 84 72 0\n96 45 0 94 76 74 0\n97 41 0 95 70 0\n98 43 0 96 68 0\n99 44 0 96 69 0\n100 39 0 98 66 0\n101 40 0 99 67 0\n102 -8 11 0 90 16 21 26 30 34 39 86 0\n103 -20 11 0 90 20 24 29 33 37 42 86 0\n104 -38 0 90 47 48 49 50 51 52 53 86 0\n105 -4 0 97 1 2 3 7 8 9 64 0\n106 -8 0 4 102 0\n107 -9 0 90 5 17 22 27 31 35 40 86 0\n108 -10 0 90 6 18 23 28 32 36 41 86 0\n109 -20 0 15 103 0\n110 23 0 109 104 108 105 106 107 100 62 0\n111 -24 0 110 25 0\n112 -33 0 110 45 0\n113 -34 0 110 46 0\n114 0 111 112 101 113 63 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00083.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00083.record013
