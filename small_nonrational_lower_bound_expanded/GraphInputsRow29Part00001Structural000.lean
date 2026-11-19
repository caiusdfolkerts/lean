module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00001Data
public import GraphInputsRow29Part00001Frames
public import GraphInputsRow29Part00001Leaves
public import GraphInputsRow29Part00001Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 80401787781120, 4398046511104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [105003092017152, 35734127902720, (certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 4), 3023656976384, (certNat% 6), (certNat% 8), (certNat% 5)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [139362830385152, 1374389534720, (certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 71476845740032, (certNat% 11), (certNat% 8), (certNat% 12), 481036337152, 44014824849408]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c1
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c0
  c9
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b8d325cf0b92d2a9a968ba699962d94e1b85ef0791ac749aa699966392e74569715656552d70d9354d1b61d17783d0ec370da3c4e9364e53c2e8b92d4b2ac6b86c9b16d8749ca719d1725c5743c3c2c83a518361382e07b81d06912c64986439514351342d0758350ca324c3312c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db69b49249269249b6d349249349a4db492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 69)]))
 (.leaf ([(facetIndex 48), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 88), (facetIndex 94)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 92), (facetIndex 93)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 56)]))
 (.leaf ([(facetIndex 87), (facetIndex 89), (facetIndex 90), (facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "edffbe120000002000041040000060301b1z24;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010" "{\"ridges\":[[12,386],[19,529],[19,536],[20,584],[22,656],[23,832],[24,641],[24,896],[40,386],[43,536],[47,584],[48,650],[51,386],[52,656],[53,786],[54,386],[55,386],[56,706],[57,832],[58,896],[60,529],[60,536],[63,584],[67,404],[68,788],[69,420],[70,832],[72,529],[72,536],[73,536],[73,584],[74,536],[74,656],[75,680],[76,584],[77,656],[78,656],[78,896],[79,896],[84,404],[85,420],[88,650],[90,786],[91,706],[94,680]],\"owners\":[[12,386,[84,85,90,91],[40,51,54,55,58]],[40,386,[90,91],[12,51,54,55,58,84,85]],[51,386,[85,91],[12,40,54,55,58,84,90]],[54,386,[84,90,91],[12,40,51,55,58,85]],[55,386,[84,85,90],[12,40,51,54,58,91]],[19,529,[22,50,52,53,66,68,77,78],[43,60,72,73]],[60,529,[22,50,52,53,77,78],[19,43,66,68,72,73]],[72,529,[22,50,52,53,66,68,78],[19,43,60,73,77]],[19,536,[87,88,92,94],[43,60,72,73,74]],[43,536,[92,94],[19,60,72,73,74,87,88]],[60,536,[87,88,94],[19,43,72,73,74,92]],[72,536,[87,88,92],[19,43,60,73,74,94]],[73,536,[88,94],[19,43,60,72,74,87,92]],[74,536,[87,92],[19,43,60,72,73,88,94]],[20,584,[87,89,92,93],[47,63,73,76]],[47,584,[92,93],[20,63,73,76,87,89]],[63,584,[87,89],[20,47,73,76,92,93]],[73,584,[89,93],[20,47,63,76,87,92]],[76,584,[87,92],[20,47,63,73,89,93]],[24,641,[22,48,52,56,74,75,77],[58,79]],[22,656,[88,90,94],[52,74,77,78]],[52,656,[94],[22,74,77,78,88,90]],[74,656,[90],[22,52,77,78,88,94]],[77,656,[88,90],[22,52,74,78,94]],[78,656,[88,94],[22,52,74,77,90]],[23,832,[89,91,93],[57,70,76,79]],[57,832,[93],[23,70,76,79,89,91]],[70,832,[89,91],[23,57,76,79,93]],[24,896,[90,91],[58,78,79]],[58,896,[],[24,78,79,90,91]],[78,896,[91],[24,58,79,90]],[79,896,[90],[24,58,78,91]],[48,650,[88],[]],[88,650,[48],[]],[53,786,[90],[]],[90,786,[53],[]],[56,706,[91],[]],[91,706,[56],[]],[67,404,[84],[]],[84,404,[67],[]],[68,788,[],[]],[69,420,[85],[]],[85,420,[69],[]],[75,680,[94],[]],[94,680,[75],[]]],\"edges\":[[29,[19,20,43,47,48,49,60,63,64,72,73,74,75,76,87,88,89,92,93,94]],[34,[19,22,43,50,52,53,60,66,68,72,73,74,77,78,87,88,90,92,94]],[41,[20,23,47,50,56,57,63,66,70,73,76,79,87,89,91,92,93]],[42,[12,24,40,51,54,55,58,67,69,78,79,84,85,90,91]],[43,[22,24,48,52,56,58,74,75,77,78,79,88,90,91,94]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-17,-15],[-35,-32],[-40,-12],[-40,-18],[-40,-39],[-41,-40],[-42,-11],[-42,-39],[-42,-41],[-43,-12],[-43,-39],[-43,-40],[-1,37,38,42,43],[-7,42,43],[-13,38,43],[-16,37,42,43],[-17,37,38,42],[-2,4,12,14,15,24,26,34,35],[-21,4,12,14,15,34,35],[-29,4,12,14,15,24,26,35],[-2,39,40,44,46],[-8,44,46],[-21,39,40,46],[-29,39,40,44],[-30,40,46],[-31,39,44],[-3,39,41,44,45],[-9,44,45],[-22,39,41],[-30,41,45],[-33,39,44],[-6,4,10,14,18,31,32,34],[-4,40,42,46],[-14,46],[-31,42],[-34,40,42],[-35,40,46],[-5,41,43,45],[-19,45],[-28,41,43],[-6,42,43],[-20],[-35,43],[-36,42],[-10,40],[-40,10],[-15,42],[-42,15],[-18,43],[-43,18],[-25,37],[-37,25],[-26],[-27,38],[-38,27],[-32,46],[-46,32],[-47,25,27],[-25,47],[-27,47],[-48,10,32],[-10,48],[-32,48],[-49,37,38],[-37,49],[-38,49],[-50,40,46],[-40,50],[-46,50],[-23,51],[-24,51],[-44,52],[-45,52],[-15,53],[-18,53],[-42,54],[-43,54],[-55,47,48],[-48,55],[-47,55],[-47,-48,56],[-57,49,50],[-50,57],[-49,57],[-49,-50,58],[-59,55,57],[-57,59],[-55,59],[-55,-57,60],[-55,-58,61],[-56,-57,61],[-52,62],[-51,62],[-54,63],[-53,63],[-53,-54,64],[-63,65],[-64,66],[-62,65],[-62,-63,66],[-62,-64,67],[-67,68],[-59,-66,68],[-60,-65,68],[-61,68],[-68],[2,3,8,9,10,11,21,22,23,29,30,31,32,33,39,40,41,44,45,46],[2,4,8,12,14,15,21,24,26,29,30,31,34,35,39,40,42,44,46],[3,5,9,12,18,19,22,24,28,30,33,36,39,41,43,44,45],[1,6,7,13,16,17,20,25,27,35,36,37,38,42,43],[4,6,10,14,18,20,31,32,34,35,36,40,42,43,46]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":78,\"b\":75},{\"tag\":\"incompatible\",\"a\":88,\"b\":50},{\"tag\":\"incompatible\",\"a\":88,\"b\":56},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":49},{\"tag\":\"incompatible\",\"a\":90,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":89},{\"tag\":\"incompatible\",\"a\":91,\"b\":50},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"mate\",\"ridge\":386,\"a\":12,\"owners\":[84,85,90,91]},{\"tag\":\"mate\",\"ridge\":386,\"a\":40,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[85,91]},{\"tag\":\"mate\",\"ridge\":386,\"a\":54,\"owners\":[84,90,91]},{\"tag\":\"mate\",\"ridge\":386,\"a\":55,\"owners\":[84,85,90]},{\"tag\":\"mate\",\"ridge\":529,\"a\":19,\"owners\":[22,50,52,53,66,68,77,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[22,50,52,53,77,78]},{\"tag\":\"mate\",\"ridge\":529,\"a\":72,\"owners\":[22,50,52,53,66,68,78]},{\"tag\":\"mate\",\"ridge\":536,\"a\":19,\"owners\":[87,88,92,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":43,\"owners\":[92,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":60,\"owners\":[87,88,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":72,\"owners\":[87,88,92]},{\"tag\":\"mate\",\"ridge\":536,\"a\":73,\"owners\":[88,94]},{\"tag\":\"mate\",\"ridge\":536,\"a\":74,\"owners\":[87,92]},{\"tag\":\"mate\",\"ridge\":584,\"a\":20,\"owners\":[87,89,92,93]},{\"tag\":\"mate\",\"ridge\":584,\"a\":47,\"owners\":[92,93]},{\"tag\":\"mate\",\"ridge\":584,\"a\":63,\"owners\":[87,89]},{\"tag\":\"mate\",\"ridge\":584,\"a\":73,\"owners\":[89,93]},{\"tag\":\"mate\",\"ridge\":584,\"a\":76,\"owners\":[87,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":24,\"owners\":[22,48,52,56,74,75,77]},{\"tag\":\"mate\",\"ridge\":656,\"a\":22,\"owners\":[88,90,94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":52,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":656,\"a\":77,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":656,\"a\":78,\"owners\":[88,94]},{\"tag\":\"mate\",\"ridge\":832,\"a\":23,\"owners\":[89,91,93]},{\"tag\":\"mate\",\"ridge\":832,\"a\":57,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":832,\"a\":70,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":896,\"a\":24,\"owners\":[90,91]},{\"tag\":\"mate\",\"ridge\":896,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":78,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":896,\"a\":79,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":650,\"a\":48,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":650,\"a\":88,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":786,\"a\":53,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":786,\"a\":90,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":706,\"a\":56,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":706,\"a\":91,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":404,\"a\":67,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":404,\"a\":84,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":788,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":69,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":420,\"a\":85,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":680,\"a\":75,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":680,\"a\":94,\"owners\":[75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[67,69],\"full_literals\":[-47,25,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-25,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-27,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[48,75],\"full_literals\":[-48,10,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":48,\"full_literals\":[-10,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-32,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[84,85],\"full_literals\":[-49,37,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-37,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-38,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[88,94],\"full_literals\":[-50,40,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-40,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-46,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-23,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-44,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-45,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-15,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-18,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":90,\"full_literals\":[-42,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-43,54]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-57,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-58,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-63,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-59,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-65,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[19,20,43,47,48,49,60,63,64,72,73,74,75,76,87,88,89,92,93,94]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,22,43,50,52,53,60,66,68,72,73,74,77,78,87,88,90,92,94]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,23,47,50,56,57,63,66,70,73,76,79,87,89,91,92,93]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[12,24,40,51,54,55,58,67,69,78,79,84,85,90,91]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,24,48,52,56,58,74,75,77,78,79,88,90,91,94]}]}"
  "112 -67 0 106 102 0\n113 -61 0 106 105 0\n114 2 4 8 12 14 15 21 24 29 30 31 34 35 39 40 42 44 46 0 53 108 0\n115 1 6 7 13 16 17 25 27 35 36 37 38 42 43 0 42 110 0\n116 4 6 10 14 18 31 32 34 35 36 40 42 43 46 0 42 111 0\n117 -17 49 0 66 65 1 17 48 0\n118 18 4 46 10 14 31 32 34 35 36 40 42 43 0 116 32 0\n119 43 42 59 0 87 83 68 69 33 36 44 35 37 34 88 79 63 62 49 118 0\n120 42 62 59 0 53 87 83 69 92 72 22 93 71 68 37 25 34 35 47 36 33 119 10 11 19 18 20 114 0\n121 62 59 0 87 83 68 69 25 88 79 63 62 92 93 72 73 70 22 28 120 7 8 9 23 24 21 26 31 29 27 107 0\n122 -42 64 0 48 76 74 96 0\n123 59 0 112 121 101 122 119 50 77 75 96 0\n124 -66 0 123 106 103 0\n125 -64 0 124 98 0\n126 -42 0 125 122 0\n127 -31 0 126 35 0\n128 -36 0 126 44 0\n129 40 46 63 0 126 128 127 56 34 94 77 43 95 75 45 36 33 118 0\n130 -40 60 0 46 68 62 83 79 89 0\n131 -62 0 124 106 99 100 104 130 129 57 69 63 83 79 89 0\n132 -52 0 131 92 0\n133 -51 0 131 93 0\n134 -44 0 132 72 0\n135 -45 0 132 73 0\n136 -24 0 133 71 0\n137 -9 0 134 135 28 0\n138 -19 0 135 39 0\n139 -46 0 113 106 126 128 57 69 2 63 83 79 91 89 90 81 104 85 59 60 97 65 66 117 94 77 41 14 16 15 13 115 0\n140 -32 0 139 56 0\n141 -57 40 0 139 106 129 97 104 67 82 89 80 59 60 52 55 64 0\n142 40 0 140 123 45 61 141 84 86 65 66 78 51 54 58 0\n143 -12 0 142 3 0\n144 -18 0 142 4 0\n145 -39 0 142 5 0\n146 -41 0 142 6 0\n147 -43 0 142 12 0\n148 -33 0 145 134 31 0\n149 -22 0 146 145 29 0\n150 -28 0 146 147 40 0\n151 -3 0 146 145 134 135 27 0\n152 -30 0 146 135 30 0\n153 -5 0 146 147 135 38 0\n154 0 153 149 151 137 143 138 144 136 150 152 148 128 145 146 147 134 135 109 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3549715cf0b92d4ab2b2a9a968bae1b46a9b16959568da8e938ae1ba1e17bc1e47516c5c9665592e785d15a5c5655555356354d2b46d4745de0f43b0dc3c4e9364e5354cb332c6b26c5bc1e8761e4751ca719e1745c5723f44c503c2a83a91a160d84e0b81e2a439515150d44d0b41d28c3322c4b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "9b6db6da69a4d34924db6db4d34d269249b6db6da4926da492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 71)]))
 (.leaf ([(facetIndex 85), (facetIndex 92)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 80), (facetIndex 89), (facetIndex 90), (facetIndex 91)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 96), (facetIndex 97)]))
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 47), (facetIndex 50), (facetIndex 82)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 87), (facetIndex 93), (facetIndex 94), (facetIndex 95)]))
 (.branch 8
 (.leaf ([(facetIndex 38), (facetIndex 48), (facetIndex 51), (facetIndex 52), (facetIndex 62)]))
 (.leaf ([(facetIndex 53), (facetIndex 66), (facetIndex 72), (facetIndex 73), (facetIndex 74)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "4466613330601005030000088802220800070020000087756754400000575z25;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1, 2, 3]
def grouped3_0002 : List Nat := [4]
def grouped3_0003 : List Nat := [4, 5]
def grouped3_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0005 : List Nat := [5]
def grouped3_0006 : List Nat := [6]
def grouped3_0007 : List Nat := [6, 7, 8]
def grouped3_0008 : List Nat := [7]
def grouped3_0009 : List Nat := [7, 8]
def grouped3_0010 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0003\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009" 32

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009" "{\"ridges\":[[38,642],[48,642],[51,642],[53,896],[59,396],[64,420],[66,385],[66,896],[69,408],[70,456],[71,432],[73,385],[73,896],[74,385],[74,896],[80,652],[85,676],[87,390],[87,896],[90,664],[91,712],[92,688],[94,402],[94,896],[95,450],[95,896]],\"owners\":[[66,385,[47,50,69,70,71],[37,53,59,64,73,74]],[73,385,[37,50,59,64,70],[47,53,66,69,71,74]],[74,385,[37,47,59,64,69,71],[50,53,66,70,73]],[87,390,[37],[]],[38,642,[90,91,92,94,95],[48,51,53,80,85,87]],[48,642,[80,85,87,91,95],[38,51,53,90,92,94]],[51,642,[80,85,87,90,92,94],[38,48,53,91,95]],[94,402,[47],[]],[95,450,[50],[]],[53,896,[],[66,73,74,87,94,95]],[66,896,[94,95],[53,73,74,87]],[73,896,[87,95],[53,66,74,94]],[74,896,[87,94],[53,66,73,95]],[87,896,[73,74],[53,66,94,95]],[94,896,[66,74],[53,73,87,95]],[95,896,[66,73],[53,74,87,94]],[59,396,[],[]],[64,420,[],[]],[69,408,[],[]],[70,456,[],[]],[71,432,[],[]],[80,652,[],[]],[85,676,[],[]],[90,664,[],[]],[91,712,[],[]],[92,688,[],[]]],\"edges\":[[42,[37,47,50,53,59,64,66,69,70,71,73,74,87,94,95]],[43,[38,48,51,53,66,73,74,80,85,87,90,91,92,94,95]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,3,5,11,12,13],[-14,1,5,8,9,12],[-15,1,3,8,9,11,13],[-18,1],[-2,19,20,21,22,23],[-4,16,17,18,20,23],[-6,16,17,18,19,21,22],[-22,3],[-23,5],[-7],[-10,22,23],[-14,18,23],[-15,18,22],[-18,14,15],[-22,10,15],[-23,10,14],[-8],[-9],[-11],[-12],[-13],[-16],[-17],[-19],[-20],[-21],[-1,24],[-3,24],[-5,24],[-18,25],[-22,25],[-23,25],[-2,26],[-4,26],[-6,26],[-10,27],[-14,27],[-15,27],[-24,28],[-27,29],[-26,29],[-25,-29,30],[-28,-30,31],[-31,32],[-32],[1,3,5,7,8,9,10,11,12,13,14,15,18,22,23],[2,4,6,7,10,14,15,16,17,18,19,20,21,22,23]],\"atoms\":[{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":385,\"a\":66,\"owners\":[47,50,69,70,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":73,\"owners\":[37,50,59,64,70]},{\"tag\":\"mate\",\"ridge\":385,\"a\":74,\"owners\":[37,47,59,64,69,71]},{\"tag\":\"mate\",\"ridge\":390,\"a\":87,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":642,\"a\":38,\"owners\":[90,91,92,94,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":48,\"owners\":[80,85,87,91,95]},{\"tag\":\"mate\",\"ridge\":642,\"a\":51,\"owners\":[80,85,87,90,92,94]},{\"tag\":\"mate\",\"ridge\":402,\"a\":94,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":450,\"a\":95,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":896,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":896,\"a\":66,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":896,\"a\":73,\"owners\":[87,95]},{\"tag\":\"mate\",\"ridge\":896,\"a\":74,\"owners\":[87,94]},{\"tag\":\"mate\",\"ridge\":896,\"a\":87,\"owners\":[73,74]},{\"tag\":\"mate\",\"ridge\":896,\"a\":94,\"owners\":[66,74]},{\"tag\":\"mate\",\"ridge\":896,\"a\":95,\"owners\":[66,73]},{\"tag\":\"mate\",\"ridge\":396,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":85,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":90,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":712,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":92,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":37,\"full_literals\":[-1,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-3,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":50,\"full_literals\":[-5,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":87,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-22,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":95,\"full_literals\":[-23,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":38,\"full_literals\":[-2,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":48,\"full_literals\":[-4,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":51,\"full_literals\":[-6,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":66,\"full_literals\":[-10,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":73,\"full_literals\":[-14,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-15,27]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-28,-30,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[37,47,50,53,59,64,66,69,70,71,73,74,87,94,95]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[38,48,51,53,66,73,74,80,85,87,90,91,92,94,95]}]}"
  "48 -31 0 45 44 0\n49 1 3 5 10 14 15 18 22 23 0 10 17 18 19 20 21 46 0\n50 2 4 6 10 14 15 18 22 23 0 10 22 23 24 25 26 47 0\n51 24 0 21 19 20 18 17 27 28 29 4 1 8 3 9 2 49 0\n52 28 0 51 39 0\n53 -30 0 52 48 43 0\n54 25 0 26 24 25 23 22 30 31 32 11 5 13 7 12 6 50 0\n55 -29 0 54 53 42 0\n56 -27 0 55 40 0\n57 -26 0 55 41 0\n58 -10 0 56 36 0\n59 -14 0 56 37 0\n60 -15 0 56 38 0\n61 -2 0 57 33 0\n62 -4 0 57 34 0\n63 -6 0 57 35 0\n64 -18 0 59 60 14 0\n65 -23 0 59 58 16 0\n66 -22 0 60 58 15 0\n67 0 62 63 61 58 59 60 64 66 65 50 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009
