module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00080Data
public import GraphInputsRow24Part00080Frames
public import GraphInputsRow24Part00080Leaves
public import GraphInputsRow24Part00080Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 4638707618339094528, (certNat% 4), 32178700288, 68410239090688, 72292889526272]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c0 c2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c0 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 10737418240]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 35184372088832, 4612811918334230528, (certNat% 10)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c1 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c0 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c0 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 8), 13194139533312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 10), 8804682956800, 39584566083584, 18014398509481984]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c16 c8
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 19703248369745920, (certNat% 15), 4611686018427387904]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 4613374868287651840, (certNat% 18), 18014398509481984]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 57174873079808, 4613374868287651840, (certNat% 20), (certNat% 21), 2323857407723175936]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 39926015983616, (certNat% 23), 4613515605776007168, 9223389766479773696, 288230376151711744]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 28147497671065600, (certNat% 21), 4611686499463725056, 2199023255552]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 8804682956800, 4611686499463725056, (certNat% 26), 21392098297118720, 39584566083584]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), 2305843028843036672, (certNat% 28), (certNat% 29), 57174604644352, 4611686430761025536, 22095785738895360]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c29 c24
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c30 c23
  c31
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b48f13cac95a36a3ab1aa6a5a362d94e33a2e1ba1e4789e0f9d1ac55936539716a5a55958d5352d4cd4b46d4749d0f6a3a4d5334e332cd4b32c6b46c9b16e8751e2729c6785d1725c3743c8f07d4ca4a320ea8631a261382e525190e5453150d1342d30c930cc4b0ac1b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d369249a4936d369a4db6da4934d349249249249b492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 65), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 33), (facetIndex 50), (facetIndex 57)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 77)]))
 (.leaf ([(facetIndex 61), (facetIndex 67), (facetIndex 88)])))
 (.branch 6
 (.leaf ([(facetIndex 32), (facetIndex 52), (facetIndex 58), (facetIndex 60), (facetIndex 72)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 86), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4d81200018005d808000e5750005080000000000015z18;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004" "{\"ridges\":[[16,280],[22,644],[25,656],[38,644],[41,280],[48,338],[49,656],[50,673],[53,273],[53,280],[59,533],[60,404],[61,533],[62,673],[64,280],[66,280],[67,673],[68,464],[77,180],[79,656],[80,644],[81,644],[84,338],[85,656],[88,180]],\"owners\":[[53,273,[48,68],[16,32,41,58,60,64,66]],[16,280,[71,84,86],[41,53,64,66]],[41,280,[86],[16,53,64,66,71,84]],[53,280,[84],[16,41,64,66,71,86]],[64,280,[71,84],[16,41,53,66,86]],[66,280,[71,86],[16,41,53,64,84]],[22,644,[61,62,88],[38,79,80,81]],[38,644,[88],[22,61,62,79,80,81]],[80,644,[61],[22,38,62,79,81,88]],[81,644,[61,62,88],[22,38,79,80]],[25,656,[61,67,88],[49,79,85]],[49,656,[88],[25,61,67,79,85]],[79,656,[67],[25,49,61,85,88]],[85,656,[61],[25,49,67,79,88]],[59,533,[33,61],[]],[61,533,[33,59],[]],[48,338,[84],[]],[84,338,[48],[]],[50,673,[62,67],[]],[62,673,[50,67],[]],[67,673,[50,62],[]],[77,180,[57,88],[]],[88,180,[57,77],[]],[60,404,[],[]],[68,464,[],[]]],\"edges\":[[33,[16,32,41,48,53,58,60,64,66,68,71,84,86]],[43,[22,25,38,49,50,61,62,67,79,80,81,85,88]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,8,21],[-1,22,27,29],[-7,29],[-11,27],[-18,22,27],[-19,22,29],[-2,16,17,30],[-6,30],[-25,16],[-26,16,17,30],[-3,16,20,30],[-9,30],[-24,20],[-28,16],[-14,5,16],[-16,5,14],[-8,27],[-27,8],[-10,17,20],[-17,10,20],[-20,10,17],[-23,12,30],[-30,12,23],[-15],[-21],[-8,31],[-27,32],[-5,33],[-10,33],[-12,33],[-34,14,17,23],[-14,34],[-17,34],[-23,34],[-35,16,20,30],[-16,35],[-20,35],[-30,35],[-4,36],[-13,36],[-22,37],[-29,37],[-33,38],[-32,38],[-38,39],[-31,39],[-31,-38,40],[-41,34,35],[-35,41],[-34,41],[-34,-35,42],[-37,43],[-36,43],[-41,44],[-41,-43,45],[-42,-43,46],[-46,47],[-39,-45,47],[-40,-44,47],[-47],[1,4,7,8,11,13,15,18,19,21,22,27,29],[2,3,6,9,10,16,17,20,24,25,26,28,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":273,\"a\":53,\"owners\":[48,68]},{\"tag\":\"mate\",\"ridge\":280,\"a\":16,\"owners\":[71,84,86]},{\"tag\":\"mate\",\"ridge\":280,\"a\":41,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":280,\"a\":53,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":280,\"a\":64,\"owners\":[71,84]},{\"tag\":\"mate\",\"ridge\":280,\"a\":66,\"owners\":[71,86]},{\"tag\":\"mate\",\"ridge\":644,\"a\":22,\"owners\":[61,62,88]},{\"tag\":\"mate\",\"ridge\":644,\"a\":38,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":644,\"a\":80,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":644,\"a\":81,\"owners\":[61,62,88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":25,\"owners\":[61,67,88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":49,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":79,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":656,\"a\":85,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":533,\"a\":59,\"owners\":[33,61]},{\"tag\":\"mate\",\"ridge\":533,\"a\":61,\"owners\":[33,59]},{\"tag\":\"mate\",\"ridge\":338,\"a\":48,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":338,\"a\":84,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":673,\"a\":50,\"owners\":[62,67]},{\"tag\":\"mate\",\"ridge\":673,\"a\":62,\"owners\":[50,67]},{\"tag\":\"mate\",\"ridge\":673,\"a\":67,\"owners\":[50,62]},{\"tag\":\"mate\",\"ridge\":180,\"a\":77,\"owners\":[57,88]},{\"tag\":\"mate\",\"ridge\":180,\"a\":88,\"owners\":[57,77]},{\"tag\":\"mate\",\"ridge\":404,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":68,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-8,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":84,\"full_literals\":[-27,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":33,\"full_literals\":[-5,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":50,\"full_literals\":[-10,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":57,\"full_literals\":[-12,33]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[59,62,77],\"full_literals\":[-34,14,17,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":59,\"full_literals\":[-14,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-17,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-23,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[61,67,88],\"full_literals\":[-35,16,20,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-16,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-20,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":88,\"full_literals\":[-30,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":32,\"full_literals\":[-4,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-13,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":71,\"full_literals\":[-22,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-29,37]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-31,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-43,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-39,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-40,-44,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[16,32,41,48,53,58,60,64,66,68,71,84,86]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,25,38,49,50,61,62,67,79,80,81,85,88]}]}"
  "63 -46 0 60 57 0\n64 1 4 7 8 11 13 18 19 22 27 29 0 24 25 61 0\n65 41 10 0 49 50 36 37 38 33 7 9 14 13 11 8 12 10 62 0\n66 35 33 0 29 65 30 28 36 37 38 48 15 20 22 31 0\n67 43 39 0 25 46 26 1 45 44 27 52 53 41 42 39 40 5 3 6 2 64 0\n68 39 0 63 45 43 28 29 30 66 67 56 51 32 33 34 16 21 23 35 0\n69 -45 0 68 60 58 0\n70 41 0 49 50 65 37 33 19 0\n71 44 0 70 54 0\n72 -43 0 70 69 55 0\n73 -40 0 71 60 59 0\n74 -37 0 72 52 0\n75 -36 0 72 53 0\n76 -22 0 74 41 0\n77 -29 0 74 42 0\n78 -4 0 75 39 0\n79 -13 0 75 40 0\n80 -7 0 77 3 0\n81 -19 0 77 76 6 0\n82 27 0 77 76 80 81 79 78 4 17 5 2 64 0\n83 8 0 82 18 0\n84 32 0 82 27 0\n85 31 0 83 26 0\n86 38 0 84 44 0\n87 0 85 86 73 47 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ad15c372b28e93aa9a968d8b6538ce1b91e2783e746b1564d98e539a9695554d58d4b5534cd1b51d2745db0dc3a8f13a4d938cd332cccb8ad2b1ae1b46c9b0ee8751e2729c6785d1725c3743c8f07c3c528c61382ea4631525190e4c5254351342d0768350cc388d0b12c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db49369a4d269a4924924934d36924d349249b492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 70), (facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 33), (facetIndex 47), (facetIndex 67)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 80), (facetIndex 81), (facetIndex 83)]))
 (.leaf ([(facetIndex 82), (facetIndex 86), (facetIndex 89)])))
 (.branch 6
 (.leaf ([(facetIndex 32), (facetIndex 40), (facetIndex 42), (facetIndex 48), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 84), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2133671b006c00000400000000005145400145000015z18;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005" "{\"ridges\":[[10,642],[18,280],[21,656],[38,642],[41,273],[41,280],[50,402],[51,656],[52,786],[53,642],[55,642],[58,280],[65,340],[66,656],[67,676],[68,280],[71,280],[72,656],[73,464],[80,178],[81,534],[82,534],[83,676],[86,178],[88,340],[89,676]],\"owners\":[[10,642,[82,83,86],[38,51,53,55]],[38,642,[86],[10,51,53,55,82,83]],[53,642,[82],[10,38,51,55,83,86]],[55,642,[82,83,86],[10,38,51,53]],[41,273,[65,73],[18,32,48,50,52,58,68,71]],[18,280,[76,84,88],[41,58,68,71]],[41,280,[88],[18,58,68,71,76,84]],[58,280,[84],[18,41,68,71,76,88]],[68,280,[76,88],[18,41,58,71,84]],[71,280,[76,84],[18,41,58,68,88]],[21,656,[82,86,89],[51,66,72]],[51,656,[89],[21,66,72,82,86]],[66,656,[86],[21,51,72,82,89]],[72,656,[82],[21,51,66,86,89]],[81,534,[33,82],[]],[82,534,[33,81],[]],[80,178,[47,86],[]],[86,178,[47,80],[]],[50,402,[],[]],[52,786,[],[]],[65,340,[88],[]],[88,340,[65],[]],[67,676,[83,89],[]],[83,676,[67,89],[]],[89,676,[67,83],[]],[73,464,[],[]]],\"edges\":[[33,[18,32,41,48,50,52,58,65,68,71,73,76,84,88]],[43,[10,21,38,51,53,55,66,67,72,82,83,86,89]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,26,27,29],[-6,29],[-13,26],[-14,26,27,29],[-7,16,22],[-2,23,28,30],[-7,30],[-15,28],[-19,23,30],[-20,23,28],[-3,26,29,31],[-11,31],[-17,29],[-21,26],[-25,5,26],[-26,5,25],[-24,8,29],[-29,8,24],[-10],[-12],[-16,30],[-30,16],[-18,27,31],[-27,18,31],[-31,18,27],[-22],[-16,32],[-30,33],[-5,34],[-8,34],[-18,34],[-35,24,25,27],[-24,35],[-25,35],[-27,35],[-36,26,29,31],[-26,36],[-29,36],[-31,36],[-4,37],[-9,37],[-23,38],[-28,38],[-34,39],[-33,39],[-39,40],[-32,40],[-32,-39,41],[-42,35,36],[-36,42],[-35,42],[-35,-36,43],[-38,44],[-37,44],[-42,45],[-42,-44,46],[-43,-44,47],[-47,48],[-40,-46,48],[-41,-45,48],[-48],[2,4,7,9,10,12,15,16,19,20,22,23,28,30],[1,3,6,11,13,14,17,18,21,26,27,29,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[82,83,86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":38,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":53,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[82,83,86]},{\"tag\":\"mate\",\"ridge\":273,\"a\":41,\"owners\":[65,73]},{\"tag\":\"mate\",\"ridge\":280,\"a\":18,\"owners\":[76,84,88]},{\"tag\":\"mate\",\"ridge\":280,\"a\":41,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":280,\"a\":58,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":280,\"a\":68,\"owners\":[76,88]},{\"tag\":\"mate\",\"ridge\":280,\"a\":71,\"owners\":[76,84]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[82,86,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":51,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":66,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":656,\"a\":72,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":534,\"a\":81,\"owners\":[33,82]},{\"tag\":\"mate\",\"ridge\":534,\"a\":82,\"owners\":[33,81]},{\"tag\":\"mate\",\"ridge\":178,\"a\":80,\"owners\":[47,86]},{\"tag\":\"mate\",\"ridge\":178,\"a\":86,\"owners\":[47,80]},{\"tag\":\"mate\",\"ridge\":402,\"a\":50,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":786,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":65,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":340,\"a\":88,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":676,\"a\":67,\"owners\":[83,89]},{\"tag\":\"mate\",\"ridge\":676,\"a\":83,\"owners\":[67,89]},{\"tag\":\"mate\",\"ridge\":676,\"a\":89,\"owners\":[67,83]},{\"tag\":\"mate\",\"ridge\":464,\"a\":73,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":65,\"full_literals\":[-16,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-30,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":33,\"full_literals\":[-5,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-8,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-18,34]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[80,81,83],\"full_literals\":[-35,24,25,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-24,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-25,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-27,35]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[82,86,89],\"full_literals\":[-36,26,29,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-26,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-29,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-31,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":32,\"full_literals\":[-4,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":48,\"full_literals\":[-9,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-23,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-28,38]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-32,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-36,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-40,-46,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-45,48],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[18,32,41,48,50,52,58,65,68,71,73,76,84,88]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,21,38,51,53,55,66,67,72,82,83,86,89]}]}"
  "64 -47 0 61 58 0\n65 2 4 7 9 15 16 19 20 23 28 30 0 19 20 26 62 0\n66 42 18 0 50 51 37 38 39 35 1 3 4 11 14 2 13 12 63 0\n67 36 34 0 31 66 30 29 37 38 39 49 15 17 24 32 0\n68 44 40 0 26 47 27 5 46 45 28 53 54 42 43 40 41 9 8 10 6 65 0\n69 40 0 64 46 44 29 30 31 67 68 57 52 33 34 35 18 16 25 36 0\n70 -46 0 69 61 59 0\n71 42 0 50 51 66 39 35 23 0\n72 45 0 71 55 0\n73 -44 0 71 70 56 0\n74 -41 0 72 61 60 0\n75 -38 0 73 53 0\n76 -37 0 73 54 0\n77 -23 0 75 42 0\n78 -28 0 75 43 0\n79 -4 0 76 40 0\n80 -9 0 76 41 0\n81 -15 0 78 8 0\n82 -20 0 78 77 10 0\n83 30 0 81 78 77 82 80 79 7 21 9 6 65 0\n84 16 0 83 22 0\n85 33 0 83 28 0\n86 32 0 84 27 0\n87 39 0 85 45 0\n88 0 86 87 74 48 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ac9ca368ba1ea9655a365392e2785e0fad1ac5c9aa4d92e479a5555a354d8b52d2745d0f5c3a8e9354e332cc7362d2b2ac6b26c5b0ee8751e2749e1745c9715c8f13c1f8d0d2528ca0d90e0ba9134631524c9896150d50d0b54330c9314c3342c8b12c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6936da49b49269b4da49b49a492492493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.leaf ([(facetIndex 6)])))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.leaf ([(facetIndex 8)])))
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.leaf ([(facetIndex 10)]))))
 (.branch 13
 (.branch 12
 (.leaf ([(facetIndex 11)]))
 (.leaf ([(facetIndex 12)])))
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)]))))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)]))))
 (.branch 20
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)])))
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)])))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)]))))
 (.branch 28
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)])))
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "3bcdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 30
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 55), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 36), (facetIndex 50), (facetIndex 52), (facetIndex 76)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 31), (facetIndex 39), (facetIndex 46), (facetIndex 47), (facetIndex 60), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 30), (facetIndex 71), (facetIndex 74)]))
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 54), (facetIndex 68), (facetIndex 82)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 48), (facetIndex 49), (facetIndex 51)]))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 43), (facetIndex 45)]))
 (.leaf ([(facetIndex 66), (facetIndex 81)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "58000013400422508002003000005016166337575703001666734z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 56), (facetIndex 62)]))
 (.branch 2
 (.leaf ([(facetIndex 72), (facetIndex 77)]))
 (.leaf ([(facetIndex 40), (facetIndex 53)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 61), (facetIndex 67)]))
 (.leaf ([(facetIndex 78), (facetIndex 83)])))
 (.branch 6
 (.leaf ([(facetIndex 57), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 73), (facetIndex 79), (facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "806d0803100062d018028010000000002z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4, 5, 6]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def grouped1_0003 : List Nat := [7, 8, 9, 10]
def grouped1_0004 : List Nat := [7, 8, 9, 10, 11, 12, 13, 14]
def grouped1_0005 : List Nat := [11, 12]
def grouped1_0006 : List Nat := [11, 12, 13, 14]
def grouped1_0007 : List Nat := [13]
def grouped1_0008 : List Nat := [13, 14]
def grouped1_0009 : List Nat := [14]
def grouped1_0010 : List Nat := [15, 16, 17]
def grouped1_0011 : List Nat := [15, 16, 17, 18, 19, 20, 21]
def grouped1_0012 : List Nat := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
def grouped1_0013 : List Nat := [18, 19]
def grouped1_0014 : List Nat := [18, 19, 20, 21]
def grouped1_0015 : List Nat := [20]
def grouped1_0016 : List Nat := [20, 21]
def grouped1_0017 : List Nat := [21]
def grouped1_0018 : List Nat := [22, 23]
def grouped1_0019 : List Nat := [22, 23, 24, 25]
def grouped1_0020 : List Nat := [22, 23, 24, 25, 26, 27, 28, 29]
def grouped1_0021 : List Nat := [24]
def grouped1_0022 : List Nat := [24, 25]
def grouped1_0023 : List Nat := [25]
def grouped1_0024 : List Nat := [26]
def grouped1_0025 : List Nat := [26, 27]
def grouped1_0026 : List Nat := [26, 27, 28, 29]
def grouped1_0027 : List Nat := [27]
def grouped1_0028 : List Nat := [28]
def grouped1_0029 : List Nat := [28, 29]
def grouped1_0030 : List Nat := [29]
def grouped2_0031 : List Nat := [0]
def grouped2_0032 : List Nat := [0, 1]
def grouped2_0033 : List Nat := [0, 1, 2, 3]
def grouped2_0035 : List Nat := [1]
def grouped2_0036 : List Nat := [2]
def grouped2_0037 : List Nat := [2, 3]
def grouped2_0038 : List Nat := [3]
def grouped2_0039 : List Nat := [4]
def grouped2_0040 : List Nat := [4, 5]
def grouped2_0041 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0042 : List Nat := [5]
def grouped2_0043 : List Nat := [6]
def grouped2_0044 : List Nat := [6, 7, 8]
def grouped2_0045 : List Nat := [7]
def grouped2_0046 : List Nat := [7, 8]
def grouped2_0047 : List Nat := [8]
def grouped3_0048 : List Nat := [0]
def grouped3_0049 : List Nat := [0, 1, 2]
def grouped3_0051 : List Nat := [1]
def grouped3_0052 : List Nat := [1, 2]
def grouped3_0053 : List Nat := [2]
def grouped3_0054 : List Nat := [3]
def grouped3_0055 : List Nat := [3, 4]
def grouped3_0056 : List Nat := [3, 4, 5, 6]
def grouped3_0057 : List Nat := [4]
def grouped3_0058 : List Nat := [5, 6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":29},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0008\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0020\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0032\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0032\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0037\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0033\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0033\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0044\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0041\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0052\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0049\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0056\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011" 97

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011" "{\"ridges\":[[1,7],[22,641],[39,7],[40,7],[40,646],[52,656],[53,674],[59,545],[59,548],[61,652],[63,641],[67,680],[68,265],[69,641],[70,641],[78,22],[78,646],[81,74],[83,674]],\"owners\":[[78,22,[1,25,30,33,35,71,72,77],[34,36,73,76]],[81,74,[5,27,31,44,75],[26,42,72,79]],[68,265,[7,14,46,58],[19,47]],[59,545,[20,50,53,69],[17,38,67]],[59,548,[29,76],[17,38]],[22,641,[40,53,61,67],[52,63,69,70]],[63,641,[53,67],[22,40,52,61,69,70]],[69,641,[40,61],[22,52,53,63,67,70]],[70,641,[40,53,61,67],[22,52,63,69]],[52,656,[],[22,63,69,70,78,83]],[40,646,[78],[]],[78,646,[40],[]],[53,674,[83],[]],[83,674,[53],[]],[61,652,[],[]],[67,680,[],[]]],\"edges\":[[43,[22,40,52,53,61,63,67,69,70,78,83]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-10],[-18,-13],[-19,-14],[-19,-15],[-19,-17],[-20,-10],[-22,-10],[-24,-2],[-24,-3],[-24,-10],[-24,-23],[-26,-24],[-27,-19],[-29,-15],[-29,-20],[-29,-22],[-29,-24],[-29,-27],[-37,-20],[-37,-22],[-39,-34],[-40,-24],[-41,-37],[-42,-37],[-44,-11],[-44,-12],[-44,-16],[-44,-25],[-44,-32],[-45,-44],[-46,-19],[-46,-29],[-49,-20],[-49,-21],[-49,-22],[-49,-30],[-49,-31],[-49,-42],[-50,-49],[-51,-24],[-1,-18,-19],[-48,1,7,10,13,14,42,43,47],[-49,2,8,11,23,45],[-39,3,4,25,32],[-33,5,27,29,40],[-33,9,46],[-6,19,29,35,38],[-36,29,38],[-40,19,35],[-41,19,29,35,38],[-28],[-19,48],[-48,19],[-29,51],[-51,29],[-35],[-38],[-4,52],[-5,53],[-7,54],[-8,55],[-9,56],[-52,57],[-57,58],[-58,59],[-59,60],[-53,61],[-61,62],[-62,63],[-54,64],[-64,65],[-55,66],[-56,67],[-66,-67,68],[-65,-68,69],[-63,-69,70],[-60,-70,71],[-71],[-72,16,17,31,32,33],[-73,15,27,28,46],[-74,36,40,41],[-75,11,18,25,26,34,45],[-76,10,42,44],[-77,21,23,30,39,50],[-78,12,20,22,24],[-79,37,49],[-80,72,73],[-81,73],[-82,74],[-82,75],[-83,80],[-83,81,82],[-84,81],[-85,76],[-85,77],[-86,78],[-86,79],[-87,86],[-88,85],[-88,87],[-89,83],[-89,84,88],[89],[-43,90],[-47,90],[-91,19,29],[-19,91],[-29,91],[-92,48,51],[-48,92],[-51,92],[-90,-91,93],[-93,94],[-92,95],[-95,96],[-94,-96,97],[-97],[6,19,28,29,35,36,38,40,41,48,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":29,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":30},{\"tag\":\"incompatible\",\"a\":43,\"b\":30},{\"tag\":\"incompatible\",\"a\":45,\"b\":5},{\"tag\":\"incompatible\",\"a\":45,\"b\":7},{\"tag\":\"incompatible\",\"a\":45,\"b\":30},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":53,\"b\":36},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":43},{\"tag\":\"incompatible\",\"a\":53,\"b\":45},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":66,\"b\":41},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":68,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":45},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":32},{\"tag\":\"incompatible\",\"a\":74,\"b\":37},{\"tag\":\"incompatible\",\"a\":74,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":40},{\"tag\":\"incompatible\",\"a\":76,\"b\":53},{\"tag\":\"incompatible\",\"a\":81,\"b\":41},{\"tag\":\"incompatible\",\"a\":81,\"b\":42},{\"tag\":\"incompatible\",\"a\":81,\"b\":43},{\"tag\":\"incompatible\",\"a\":81,\"b\":54},{\"tag\":\"incompatible\",\"a\":81,\"b\":55},{\"tag\":\"incompatible\",\"a\":81,\"b\":71},{\"tag\":\"incompatible\",\"a\":82,\"b\":81},{\"tag\":\"incompatible\",\"a\":83,\"b\":45},{\"tag\":\"three\",\"ridge\":7,\"vertices\":[1,39,40]},{\"tag\":\"mate\",\"ridge\":22,\"a\":78,\"owners\":[1,25,30,33,35,71,72,77]},{\"tag\":\"mate\",\"ridge\":74,\"a\":81,\"owners\":[5,27,31,44,75]},{\"tag\":\"mate\",\"ridge\":265,\"a\":68,\"owners\":[7,14,46,58]},{\"tag\":\"mate\",\"ridge\":545,\"a\":59,\"owners\":[20,50,53,69]},{\"tag\":\"mate\",\"ridge\":548,\"a\":59,\"owners\":[29,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":22,\"owners\":[40,53,61,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":63,\"owners\":[53,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[40,61]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[40,53,61,67]},{\"tag\":\"mate\",\"ridge\":656,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":646,\"a\":40,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":646,\"a\":78,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":674,\"a\":53,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":674,\"a\":83,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":652,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":680,\"a\":67,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-4,52]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-5,53]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-7,54]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-8,55]},{\"tag\":\"group_take\",\"kind\":1,\"index\":29,\"member\":29,\"full_literals\":[-9,56]},{\"tag\":\"merge\",\"left\":[13],\"right\":[14],\"left_name\":\"grouped1_0007\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,57],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12],\"right\":[13,14],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7,8,9,10],\"right\":[11,12,13,14],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,59],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13,14],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,61],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18,19],\"right\":[20,21],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17],\"right\":[18,19,20,21],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0014\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,64],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22,23],\"right\":[24,25],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26],\"right\":[27],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,66],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,67],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26,27],\"right\":[28,29],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,68],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22,23,24,25],\"right\":[26,27,28,29],\"left_name\":\"grouped1_0019\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"grouped1_0020\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-68,69],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15,16,17,18,19,20,21],\"right\":[22,23,24,25,26,27,28,29],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0012\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-63,-69,70],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],\"right\":[15,16,17,18,19,20,21,22,23,24,25,26,27,28,29],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-60,-70,71],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[37,38,55,58,59],\"full_literals\":[-72,16,17,31,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[36,50,52,76],\"full_literals\":[-73,15,27,28,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[63,69,70],\"full_literals\":[-74,36,40,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[31,39,46,47,60,75],\"full_literals\":[-75,11,18,25,26,34,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[30,71,74],\"full_literals\":[-76,10,42,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[42,44,54,68,82],\"full_literals\":[-77,21,23,30,39,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,41,43,45],\"full_literals\":[-78,12,20,22,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[66,81],\"full_literals\":[-79,37,49]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0031\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"grouped2_0032\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,72,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0031\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"grouped2_0032\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-81,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0037\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-82,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0036\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0037\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-82,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0032\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"grouped2_0033\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-83,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0032\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"grouped2_0033\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,81,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0032\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"grouped2_0033\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-84,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0042\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0042\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"grouped2_0046\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0043\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0044\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0041\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-88,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0040\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0041\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-88,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-89,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-89,84,88],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-43,90]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-47,90]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[40,53],\"full_literals\":[-91,19,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":40,\"full_literals\":[-19,91]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-29,91]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[78,83],\"full_literals\":[-92,48,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-48,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-51,92]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0051\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0052\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-91,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0048\",\"right_name\":\"grouped3_0052\",\"joined_name\":\"grouped3_0049\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-93,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0056\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-95,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0049\",\"right_name\":\"grouped3_0056\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-94,-96,97],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,40,52,53,61,63,67,69,70,78,83]}]}"
  "119 -73 15 27 46 0 51 80 0\n120 83 0 103 101 0\n121 80 0 120 91 0\n122 6 19 29 36 40 41 48 51 0 51 56 57 118 0\n123 91 0 57 56 107 108 49 53 48 55 47 50 122 0\n124 92 0 123 110 111 52 54 106 0\n125 95 0 124 114 0\n126 96 0 125 115 0\n127 -94 0 126 117 116 0\n128 -93 0 127 113 0\n129 -90 0 128 123 112 0\n130 -43 0 129 104 0\n131 -47 0 129 105 0\n132 -10 -78 0 1 6 7 10 85 0\n133 -42 -79 0 24 38 86 0\n134 -37 -74 -88 0 57 99 94 100 98 96 132 97 133 83 26 19 20 23 85 17 22 48 81 0\n135 -82 -88 0 123 124 121 131 130 78 99 94 100 98 96 132 97 133 83 29 27 30 28 26 25 95 89 90 134 86 33 34 35 36 39 85 8 9 11 12 17 22 40 43 84 106 109 61 21 3 4 13 31 72 82 119 37 44 5 2 41 87 79 58 42 45 46 63 60 59 62 64 70 67 73 65 71 68 74 66 69 75 77 76 0\n136 -19 -73 0 4 13 31 119 0\n137 -88 0 120 123 99 100 94 98 96 97 132 133 83 26 135 92 88 136 106 15 16 17 85 0\n138 84 0 137 103 102 0\n139 81 0 138 93 0\n140 73 0 139 88 0\n141 -19 0 140 136 0\n142 29 0 141 123 106 0\n143 -15 0 142 14 0\n144 -27 0 142 18 0\n145 -46 0 142 32 0\n146 0 145 144 143 140 119 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record011_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ad1cc370bcb48da1ea96558d68d94e3392e2785e0fad1ac5c9aa4d92e479716a5a5555356352d58d534cd4b4ad2745d0f6c3a4e5354cd31ce8b32e2b4ac6b26c5b0ee8751cc789d2785d1725c5723c4f07e32528364382ea44d18c549324950d50d2342d50e2384c530cd0b12c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6d269b49269b6d34924924d34924d249a4d3492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 69), (facetIndex 71)]))
 (.leaf ([(facetIndex 38), (facetIndex 91)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 54), (facetIndex 64), (facetIndex 67)]))
 (.leaf ([(facetIndex 41), (facetIndex 68), (facetIndex 76), (facetIndex 88)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 79), (facetIndex 83), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 77), (facetIndex 85)])))
 (.branch 7
 (.leaf ([(facetIndex 46), (facetIndex 52), (facetIndex 82), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "323fae98082b000003402000000086000180018042z1b;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012" "{\"ridges\":[[8,82],[13,140],[16,145],[17,200],[20,145],[20,193],[20,208],[21,145],[21,641],[21,656],[29,140],[38,646],[40,82],[41,145],[41,154],[45,200],[46,650],[47,82],[48,208],[49,82],[50,82],[51,641],[51,656],[52,706],[55,140],[56,140],[58,140],[58,200],[60,140],[63,208],[65,656],[66,133],[66,676],[67,452],[68,120],[69,184],[70,200],[70,208],[71,680],[72,200],[73,641],[73,656],[74,193],[74,208],[74,656],[84,646],[86,154],[86,208],[87,706],[88,184],[89,92],[90,452],[91,148],[91,676]],\"owners\":[[8,82,[76,82,83,85,86,87],[30,40,47,48,49,50]],[40,82,[82,83,87],[8,30,47,48,49,50,76,85,86]],[47,82,[76,82,83,86,87],[8,30,40,48,49,50,85]],[49,82,[76,82,85,86,87],[8,30,40,47,48,50,83]],[50,82,[76,82,83,85,86],[8,30,40,47,48,49,87]],[66,133,[13,16,29,31,36,58,60,63,67],[38,56,61,65]],[13,140,[77,79,88,89,90],[29,55,56,58,60]],[29,140,[88,89,90],[13,55,56,58,60,77,79]],[55,140,[79,90],[13,29,56,58,60,77,88,89]],[56,140,[77,79,89,90],[13,29,55,58,60,88]],[58,140,[77,88],[13,29,55,56,60,79,89,90]],[60,140,[77,79,88,89],[13,29,55,56,58,90]],[91,148,[16,31,55,63,77,82,89],[61,65,84,88]],[20,193,[17,36,45,52,58,67,72],[48,63,74]],[74,193,[17,36,45,58,67,72],[20,48,52,63]],[17,200,[79,86,89,90],[45,58,70,72]],[45,200,[89,90],[17,58,70,72,79,86]],[58,200,[86],[17,45,70,72,79,89,90]],[70,200,[79,90],[17,45,58,72,86,89]],[72,200,[79,86,89],[17,45,58,70,90]],[20,208,[82,86,87,89],[48,63,70,74]],[48,208,[89],[20,63,70,74,82,86,87]],[63,208,[86,87],[20,48,70,74,82,89]],[70,208,[82,87],[20,48,63,74,86,89]],[74,208,[82,86,89],[20,48,63,70,87]],[86,208,[20,63,74],[48,70,82,87,89]],[21,641,[38,46,52,66,71],[51,65,73,74]],[51,641,[66,71],[21,38,46,52,65,73,74]],[73,641,[38,46,52],[21,51,65,66,71,74]],[21,656,[84,87,91],[51,65,73,74]],[51,656,[91],[21,65,73,74,84,87]],[65,656,[87],[21,51,73,74,84,91]],[73,656,[84,87],[21,51,65,74,91]],[74,656,[84,91],[21,51,65,73,87]],[38,646,[84],[]],[84,646,[38],[]],[41,154,[77,86],[]],[86,154,[41,77],[]],[46,650,[],[]],[52,706,[87],[]],[87,706,[52],[]],[89,92,[54,76],[]],[66,676,[91],[]],[91,676,[66],[]],[67,452,[90],[]],[90,452,[67],[]],[68,120,[85],[]],[69,184,[88],[]],[88,184,[69],[]],[71,680,[],[]]],\"edges\":[[27,[13,17,29,41,45,46,55,56,58,60,69,70,71,72,77,79,86,88,89,90]],[31,[8,20,30,40,47,48,49,50,54,63,64,68,70,74,76,82,83,85,86,87,89]],[39,[17,20,36,45,48,52,58,63,67,70,72,74,79,82,86,87,89,90]],[43,[21,38,46,51,52,65,66,71,73,74,84,87,91]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-13],[-38,-13],[-38,-33],[-40,-10],[-41,-8],[-41,-22],[-41,-28],[-41,-39],[-42,-40],[-43,-41],[-46,-9],[-46,-10],[-46,-11],[-46,-20],[-46,-23],[-46,-41],[-46,-42],[-46,-44],[-47,-40],[-47,-41],[-47,-46],[-48,-30],[-48,-37],[-51,-48],[-1,39,42,43,45,46,47],[-12,42,43,47],[-16,39,42,43,46,47],[-18,39,42,45,46,47],[-19,39,42,43,45,46],[-30,2,3,7,9,10,25,26,27,31],[-2,40,41,48,49,50],[-7,48,49,50],[-23,41,50],[-24,40,41,49,50],[-25,40,48],[-26,40,41,48,49],[-3,-5,-13],[-5,-6,-13],[-51,3,9,23,27,40,42,49],[-5,4,10,14,21,25,31,36],[-38,4,10,14,25,31,36],[-4,41,46,49,50],[-14,49,50],[-25,46],[-34,41,50],[-36,41,46,49],[-5,42,46,47,49],[-17,49],[-27,46,47],[-34,42,47],[-38,42,46,49],[-46,5,27,38],[-6,11,15,21,30,35],[-20,30,35],[-37,11,15,21],[-6,44,47,51],[-20,51],[-29,47],[-37,44,47],[-38,44,51],[-11,44],[-44,11],[-13,40,46],[-46,13,40],[-15],[-21,47],[-47,21],[-49,22,39],[-30,51],[-51,30],[-31,50],[-50,31],[-32,45],[-33,48],[-48,33],[-35],[-30,52],[-33,52],[-11,53],[-51,53],[-22,54],[-31,54],[-13,55],[-39,55],[-48,55],[-41,56],[-49,56],[-50,56],[-40,57],[-45,57],[-21,58],[-42,58],[-44,58],[-46,58],[-47,59],[-53,60],[-52,60],[-52,-53,61],[-55,62],[-54,62],[-62,63],[-60,63],[-61,64],[-61,-62,65],[-57,66],[-56,66],[-56,-57,67],[-58,68],[-58,-59,69],[-69,71],[-66,70],[-66,-68,71],[-67,71],[-63,-71,72],[-64,-70,72],[-65,72],[-72],[2,4,7,13,14,15,23,24,25,26,33,34,35,36,40,41,46,48,49,50],[1,5,8,12,16,17,18,19,22,27,28,32,34,38,39,42,43,45,46,47,49],[4,5,10,14,17,21,25,27,31,34,36,38,41,42,46,47,49,50],[6,11,15,20,21,29,30,35,37,38,44,47,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":63,\"b\":41},{\"tag\":\"incompatible\",\"a\":74,\"b\":41},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":36},{\"tag\":\"incompatible\",\"a\":79,\"b\":30},{\"tag\":\"incompatible\",\"a\":79,\"b\":54},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":82,\"b\":77},{\"tag\":\"incompatible\",\"a\":83,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":31},{\"tag\":\"incompatible\",\"a\":86,\"b\":36},{\"tag\":\"incompatible\",\"a\":86,\"b\":38},{\"tag\":\"incompatible\",\"a\":86,\"b\":51},{\"tag\":\"incompatible\",\"a\":86,\"b\":55},{\"tag\":\"incompatible\",\"a\":86,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":82},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":77},{\"tag\":\"incompatible\",\"a\":87,\"b\":79},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":66},{\"tag\":\"incompatible\",\"a\":88,\"b\":73},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"mate\",\"ridge\":82,\"a\":8,\"owners\":[76,82,83,85,86,87]},{\"tag\":\"mate\",\"ridge\":82,\"a\":40,\"owners\":[82,83,87]},{\"tag\":\"mate\",\"ridge\":82,\"a\":47,\"owners\":[76,82,83,86,87]},{\"tag\":\"mate\",\"ridge\":82,\"a\":49,\"owners\":[76,82,85,86,87]},{\"tag\":\"mate\",\"ridge\":82,\"a\":50,\"owners\":[76,82,83,85,86]},{\"tag\":\"mate\",\"ridge\":133,\"a\":66,\"owners\":[13,16,29,31,36,58,60,63,67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":13,\"owners\":[77,79,88,89,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":29,\"owners\":[88,89,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":55,\"owners\":[79,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":56,\"owners\":[77,79,89,90]},{\"tag\":\"mate\",\"ridge\":140,\"a\":58,\"owners\":[77,88]},{\"tag\":\"mate\",\"ridge\":140,\"a\":60,\"owners\":[77,79,88,89]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[16,20,41]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[20,21,41]},{\"tag\":\"mate\",\"ridge\":148,\"a\":91,\"owners\":[16,31,55,63,77,82,89]},{\"tag\":\"mate\",\"ridge\":193,\"a\":20,\"owners\":[17,36,45,52,58,67,72]},{\"tag\":\"mate\",\"ridge\":193,\"a\":74,\"owners\":[17,36,45,58,67,72]},{\"tag\":\"mate\",\"ridge\":200,\"a\":17,\"owners\":[79,86,89,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":45,\"owners\":[89,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":58,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":200,\"a\":70,\"owners\":[79,90]},{\"tag\":\"mate\",\"ridge\":200,\"a\":72,\"owners\":[79,86,89]},{\"tag\":\"mate\",\"ridge\":208,\"a\":20,\"owners\":[82,86,87,89]},{\"tag\":\"mate\",\"ridge\":208,\"a\":48,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":208,\"a\":63,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":70,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":74,\"owners\":[82,86,89]},{\"tag\":\"mate\",\"ridge\":208,\"a\":86,\"owners\":[20,63,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":21,\"owners\":[38,46,52,66,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":51,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":73,\"owners\":[38,46,52]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[84,87,91]},{\"tag\":\"mate\",\"ridge\":656,\"a\":51,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":656,\"a\":65,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":656,\"a\":73,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[84,91]},{\"tag\":\"mate\",\"ridge\":646,\"a\":38,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":646,\"a\":84,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":154,\"a\":41,\"owners\":[77,86]},{\"tag\":\"mate\",\"ridge\":154,\"a\":86,\"owners\":[41,77]},{\"tag\":\"mate\",\"ridge\":650,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":52,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":706,\"a\":87,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":92,\"a\":89,\"owners\":[54,76]},{\"tag\":\"mate\",\"ridge\":676,\"a\":66,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":676,\"a\":91,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":452,\"a\":67,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":452,\"a\":90,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":120,\"a\":68,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":184,\"a\":69,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":184,\"a\":88,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":680,\"a\":71,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-30,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-33,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":38,\"full_literals\":[-11,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":91,\"full_literals\":[-51,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":54,\"full_literals\":[-22,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-31,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":41,\"full_literals\":[-13,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-39,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":88,\"full_literals\":[-48,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-41,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-49,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-50,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-40,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-45,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":52,\"full_literals\":[-21,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-42,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-44,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-46,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-47,59]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-53,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-59,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-68,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[13,17,29,41,45,46,55,56,58,60,69,70,71,72,77,79,86,88,89,90]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[8,20,30,40,47,48,49,50,54,63,64,68,70,74,76,82,83,85,86,87,89]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[17,20,36,45,48,52,58,63,67,70,72,74,79,82,86,87,89,90]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[21,38,46,51,52,65,66,71,73,74,84,87,91]}]}"
  "122 -65 0 117 116 0\n123 2 4 7 13 14 23 24 25 26 33 34 36 40 41 46 48 49 50 0 65 76 118 0\n124 6 11 20 21 29 30 37 38 44 47 51 0 65 76 121 0\n125 -47 63 0 101 99 85 100 81 84 68 82 72 32 43 102 97 78 83 19 20 21 31 34 35 36 33 42 45 46 123 0\n126 63 0 102 96 97 79 80 77 62 57 60 125 58 66 59 56 124 0\n127 -71 0 126 117 114 0\n128 -69 0 127 110 0\n129 -67 0 127 113 0\n130 40 41 46 48 49 50 0 46 45 42 33 44 32 74 43 31 34 36 63 123 0\n131 41 46 48 49 50 47 0 49 44 48 43 71 66 42 45 46 130 4 9 40 41 120 0\n132 46 48 49 50 47 0 129 127 48 49 131 5 6 7 8 10 86 106 107 112 90 108 73 92 26 47 50 51 28 25 27 29 119 0\n133 48 49 50 47 0 65 127 71 66 58 32 132 11 12 13 14 15 16 17 18 94 55 108 112 105 89 31 35 36 64 1 2 52 37 38 30 39 124 0\n134 -48 47 0 122 76 65 66 58 22 23 24 75 85 54 3 78 99 104 98 79 62 53 124 0\n135 -51 61 0 70 80 77 98 0\n136 -66 47 0 127 117 66 58 111 112 115 108 103 93 61 59 135 57 69 60 56 124 0\n137 47 0 134 136 106 87 88 133 0\n138 21 0 137 67 0\n139 59 0 137 95 0\n140 58 0 138 91 0\n141 0 140 139 128 109 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record012
