module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00081Data
public import GraphInputsRow24Part00081Frames
public import GraphInputsRow24Part00081Leaves
public import GraphInputsRow24Part00081Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 180425528791007232, (certNat% 4), 72163284593147904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 72303884642549760]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 180566197559885824, 72163215907225600]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 180566197559885824, (certNat% 15), 72163353346179072]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), 36310306623848448, 25971130368, (certNat% 18), (certNat% 19)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), 180566197559885824, 885233025024, (certNat% 23), 105759308251136]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011
def vertexColumn : Fields := ⟨10, (certNat% 24)⟩
def kindColumn : Fields := ⟨3, (certNat% 25)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), 4719772478203756544, 576460759819616256, (certNat% 28), 1152921504606846976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 9800536476616753152, (certNat% 30), (certNat% 31), 1099780063232, (certNat% 32)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 1729945206863691776, (certNat% 34), 19516331393024, (certNat% 35), (certNat% 36)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 21), 48318382080, 23364622090240, 8796093022208]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 1729382260131495936, (certNat% 39), 42949672960, (certNat% 40), 4611686018427387904]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 21), 13194139533312, 576460759819616256, 42949672960]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 28), (certNat% 44), 576460759819616256, 1152921504606846976]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 5764607524107976704, (certNat% 46), (certNat% 47), (certNat% 44), 576460758762651648, (certNat% 48)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record011_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae15c372d2ac9caaaa9a36a3a2e8d68d876538ce4b89e1783eb46b1726a9a6559366392e555356351d54d3352d4749d176c370ea3a4e5334e332cc73a2d8b52ccb8ad2b2ae1b26c5b0ecc789d2719e1725c570dc8f13c1f0f1464382ea44d18c4990e545154354342d0768350cc388d0b22c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6db6d34da49b4d249249a49249349b4924934d2493692489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 49), (facetIndex 72)]))
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 88), (facetIndex 91), (facetIndex 95)]))
 (.leaf ([(facetIndex 38), (facetIndex 61), (facetIndex 70), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 77), (facetIndex 80), (facetIndex 90), (facetIndex 94)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 48), (facetIndex 52), (facetIndex 87)])))
 (.branch 7
 (.leaf ([(facetIndex 78), (facetIndex 82), (facetIndex 83), (facetIndex 92)]))
 (.leaf ([(facetIndex 84), (facetIndex 93)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "53e50aa4fd841a00180c00000180000050050000000c0005az17;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000" "{\"ridges\":[[7,546],[8,194],[10,642],[15,84],[19,560],[20,208],[21,656],[30,84],[35,546],[36,194],[38,90],[43,546],[44,194],[47,642],[50,560],[51,208],[53,656],[54,546],[54,642],[55,194],[56,194],[56,642],[57,84],[63,84],[64,560],[65,84],[65,208],[66,84],[68,560],[69,208],[70,344],[71,656],[72,680],[74,560],[74,656],[75,208],[75,656],[89,680],[90,456],[91,178],[94,344],[95,680]],\"owners\":[[7,546,[83,86,89,91],[35,43,50,54]],[35,546,[86,89,91],[7,43,50,54,83]],[43,546,[83,91],[7,35,50,54,86,89]],[54,546,[83,86],[7,35,43,50,89,91]],[8,194,[80,84,87,90,92],[36,44,51,55,56]],[36,194,[87,90,92],[8,44,51,55,56,80,84]],[44,194,[84,92],[8,36,51,55,56,80,87,90]],[55,194,[80,84,87,92],[8,36,44,51,56,90]],[56,194,[80,84,87,90],[8,36,44,51,55,92]],[10,642,[88,89,91,92],[47,53,54,56]],[47,642,[91,92],[10,53,54,56,88,89]],[54,642,[88,92],[10,47,53,56,89,91]],[56,642,[88,89,91],[10,47,53,54,92]],[15,84,[77,82,84,93,94],[30,57,63,65,66]],[30,84,[93,94],[15,57,63,65,66,77,82,84]],[57,84,[82,84],[15,30,63,65,66,77,93,94]],[63,84,[77,84,93,94],[15,30,57,65,66,82]],[65,84,[77,82,94],[15,30,57,63,66,84,93]],[66,84,[77,82,84,93],[15,30,57,63,65,94]],[19,560,[83,86,91,95],[50,64,68,74]],[50,560,[95],[19,64,68,74,83,86,91]],[64,560,[86,91,95],[19,50,68,74,83]],[68,560,[83,91],[19,50,64,74,86,95]],[74,560,[83,86],[19,50,64,68,91,95]],[20,208,[84,87,92,93],[51,65,69,75]],[51,208,[93],[20,65,69,75,84,87,92]],[65,208,[87,92],[20,51,69,75,84,93]],[69,208,[84,92],[20,51,65,75,87,93]],[75,208,[84,87,93],[20,51,65,69,92]],[21,656,[88,91,92,95],[53,71,74,75]],[53,656,[95],[21,71,74,75,88,91,92]],[71,656,[91,92],[21,53,74,75,88,95]],[74,656,[88,92],[21,53,71,75,91,95]],[75,656,[88,91,95],[21,53,71,74,92]],[38,90,[77,87],[]],[91,178,[49,85],[]],[70,344,[94],[]],[94,344,[70],[]],[72,680,[89,95],[]],[89,680,[72,95],[]],[95,680,[72,89],[]],[90,456,[73],[]]],\"edges\":[[31,[15,20,30,38,48,51,52,57,63,65,66,69,70,75,77,82,84,87,92,93,94]],[38,[7,19,35,43,50,54,64,68,72,74,83,86,89,91,95]],[39,[8,20,36,44,51,55,56,61,65,69,73,75,80,84,87,90,92,93]],[43,[10,21,47,53,54,56,71,72,74,75,88,89,91,92,95]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-44,-14],[-44,-18],[-44,-33],[-44,-42],[-45,-44],[-46,-41],[-47,-46],[-49,-8],[-49,-11],[-49,-15],[-49,-18],[-49,-19],[-49,-38],[-49,-40],[-49,-42],[-49,-45],[-50,-41],[-50,-44],[-50,-49],[-1,41,44,47,49],[-9,44,47,49],[-12,41,49],[-21,41,44],[-2,39,42,45,48,50],[-10,45,48,50],[-13,42,50],[-22,39,42,45,50],[-23,39,42,45,48],[-3,46,47,49,50],[-14,49,50],[-21,46,50],[-23,46,47,49],[-4,38,40,42,51,52],[-8,51,52],[-24,40,42],[-26,38,42,51,52],[-28,38,40,52],[-29,38,40,42,51],[-5,41,44,49,53],[-17,53],[-27,44,49,53],[-30,41,49],[-36,41,44],[-6,42,45,50,51],[-18,51],[-28,45,50],[-31,42,50],[-37,42,45,51],[-7,46,49,50,53],[-20,53],[-33,49,50],[-36,46,50],[-37,46,49,53],[-11,38,45],[-49,16,43],[-32,52],[-52,32],[-34,47,53],[-47,34,53],[-53,34,47],[-48,35],[-16,54],[-34,54],[-43,55],[-44,55],[-47,55],[-46,56],[-49,56],[-53,56],[-25,57],[-32,57],[-35,57],[-38,58],[-39,58],[-52,58],[-15,59],[-19,59],[-45,59],[-40,60],[-50,60],[-42,61],[-51,61],[-55,62],[-54,62],[-54,-55,63],[-57,64],[-56,64],[-56,-57,65],[-62,-64,66],[-62,-65,67],[-63,66],[-63,-64,67],[-59,68],[-58,68],[-61,69],[-60,69],[-69,70],[-68,70],[-66,-70,71],[-67,71],[-71],[4,6,8,11,15,18,19,24,26,28,29,31,32,37,38,40,42,45,50,51,52],[1,5,9,12,17,21,27,30,34,36,41,44,47,49,53],[2,6,10,13,18,22,23,25,28,31,35,37,39,42,45,48,50,51],[3,7,14,20,21,23,33,34,36,37,46,47,49,50,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":86,\"b\":47},{\"tag\":\"incompatible\",\"a\":86,\"b\":51},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":30},{\"tag\":\"incompatible\",\"a\":91,\"b\":38},{\"tag\":\"incompatible\",\"a\":91,\"b\":48},{\"tag\":\"incompatible\",\"a\":91,\"b\":51},{\"tag\":\"incompatible\",\"a\":91,\"b\":52},{\"tag\":\"incompatible\",\"a\":91,\"b\":77},{\"tag\":\"incompatible\",\"a\":91,\"b\":82},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":92,\"b\":83},{\"tag\":\"incompatible\",\"a\":92,\"b\":86},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"mate\",\"ridge\":546,\"a\":7,\"owners\":[83,86,89,91]},{\"tag\":\"mate\",\"ridge\":546,\"a\":35,\"owners\":[86,89,91]},{\"tag\":\"mate\",\"ridge\":546,\"a\":43,\"owners\":[83,91]},{\"tag\":\"mate\",\"ridge\":546,\"a\":54,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":194,\"a\":8,\"owners\":[80,84,87,90,92]},{\"tag\":\"mate\",\"ridge\":194,\"a\":36,\"owners\":[87,90,92]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[84,92]},{\"tag\":\"mate\",\"ridge\":194,\"a\":55,\"owners\":[80,84,87,92]},{\"tag\":\"mate\",\"ridge\":194,\"a\":56,\"owners\":[80,84,87,90]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[88,89,91,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":47,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":54,\"owners\":[88,92]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[88,89,91]},{\"tag\":\"mate\",\"ridge\":84,\"a\":15,\"owners\":[77,82,84,93,94]},{\"tag\":\"mate\",\"ridge\":84,\"a\":30,\"owners\":[93,94]},{\"tag\":\"mate\",\"ridge\":84,\"a\":57,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":84,\"a\":63,\"owners\":[77,84,93,94]},{\"tag\":\"mate\",\"ridge\":84,\"a\":65,\"owners\":[77,82,94]},{\"tag\":\"mate\",\"ridge\":84,\"a\":66,\"owners\":[77,82,84,93]},{\"tag\":\"mate\",\"ridge\":560,\"a\":19,\"owners\":[83,86,91,95]},{\"tag\":\"mate\",\"ridge\":560,\"a\":50,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":560,\"a\":64,\"owners\":[86,91,95]},{\"tag\":\"mate\",\"ridge\":560,\"a\":68,\"owners\":[83,91]},{\"tag\":\"mate\",\"ridge\":560,\"a\":74,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":208,\"a\":20,\"owners\":[84,87,92,93]},{\"tag\":\"mate\",\"ridge\":208,\"a\":51,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":208,\"a\":65,\"owners\":[87,92]},{\"tag\":\"mate\",\"ridge\":208,\"a\":69,\"owners\":[84,92]},{\"tag\":\"mate\",\"ridge\":208,\"a\":75,\"owners\":[84,87,93]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[88,91,92,95]},{\"tag\":\"mate\",\"ridge\":656,\"a\":53,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[91,92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":74,\"owners\":[88,92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":75,\"owners\":[88,91,95]},{\"tag\":\"mate\",\"ridge\":90,\"a\":38,\"owners\":[77,87]},{\"tag\":\"mate\",\"ridge\":178,\"a\":91,\"owners\":[49,85]},{\"tag\":\"mate\",\"ridge\":344,\"a\":70,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":344,\"a\":94,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":680,\"a\":72,\"owners\":[89,95]},{\"tag\":\"mate\",\"ridge\":680,\"a\":89,\"owners\":[72,95]},{\"tag\":\"mate\",\"ridge\":680,\"a\":95,\"owners\":[72,89]},{\"tag\":\"mate\",\"ridge\":456,\"a\":90,\"owners\":[73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-16,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":72,\"full_literals\":[-34,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-43,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-44,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-47,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":88,\"full_literals\":[-46,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":91,\"full_literals\":[-49,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-53,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":61,\"full_literals\":[-25,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-32,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":73,\"full_literals\":[-35,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-38,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":80,\"full_literals\":[-39,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":94,\"full_literals\":[-52,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":48,\"full_literals\":[-15,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-19,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-45,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-40,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":92,\"full_literals\":[-50,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-42,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":93,\"full_literals\":[-51,61]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-55,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-57,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":31,\"owners\":[15,20,30,38,48,51,52,57,63,65,66,69,70,75,77,82,84,87,92,93,94]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[7,19,35,43,50,54,64,68,72,74,83,86,89,91,95]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[8,20,36,44,51,55,56,61,65,69,73,75,80,84,87,90,92,93]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,21,47,53,54,56,71,72,74,75,88,89,91,92,95]}]}"
  "106 -67 0 101 100 0\n107 -41 47 49 53 0 58 50 6 17 53 32 30 29 49 31 52 51 105 0\n108 44 47 49 53 0 107 42 22 58 40 21 41 39 23 43 20 103 0\n109 -56 -44 0 106 101 65 83 90 18 5 46 4 47 26 2 87 88 89 70 72 99 61 97 98 25 95 94 82 74 44 48 28 24 27 104 0\n110 46 3 53 7 14 23 33 20 34 37 21 47 49 50 0 105 52 0\n111 47 49 53 0 50 58 108 1 3 18 109 67 53 32 29 49 31 110 0\n112 49 53 0 101 106 111 7 59 66 53 63 85 91 92 99 86 97 98 70 71 72 95 96 93 94 57 61 81 82 79 80 78 73 74 37 25 26 47 45 44 28 24 27 104 0\n113 70 37 -49 0 19 16 46 14 15 35 47 13 12 11 10 9 8 97 98 95 94 82 75 44 36 33 38 56 102 0\n114 62 -49 0 83 84 64 62 55 0\n115 -49 0 101 15 16 68 87 114 89 99 97 113 95 48 82 0\n116 53 0 115 112 0\n117 56 0 116 69 0\n118 64 0 117 87 0\n119 70 0 97 98 95 96 93 94 81 82 79 80 76 77 78 73 75 47 35 45 34 44 36 33 38 48 54 46 56 102 0\n120 -66 0 119 101 99 0\n121 -62 0 120 118 89 0\n122 -55 0 121 83 0\n123 -54 0 121 84 0\n124 -47 0 122 66 0\n125 -34 0 123 63 0\n126 0 125 124 116 60 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "571d25693aa9956358b61da8e53a2e4789e1783e746b1a65598e539a95552d475a354d8b51d2745db0dc3a8d9354cd34ccb31cf0ba2d4b4ad1b26c5b0ee8751e2729c6745c9715c3783d0f23c4f07cd40f22a3182e544d18a5190e4c5254550d42d0768350cc388e0b42c2b21c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db4db69b6936926926d24924d26da4926d2492692492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 63), (facetIndex 67)]))
 (.leaf ([(facetIndex 71), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 80), (facetIndex 85)]))
 (.leaf ([(facetIndex 35), (facetIndex 42), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 75), (facetIndex 77), (facetIndex 79)]))
 (.leaf ([(facetIndex 84), (facetIndex 87), (facetIndex 89)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 54)]))
 (.leaf ([(facetIndex 76), (facetIndex 81), (facetIndex 82), (facetIndex 86), (facetIndex 88)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2fbd51fa8278012000000c0000180db0000cc00006z1a;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004" 41

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004" "{\"ridges\":[[5,266],[10,641],[10,642],[18,280],[30,266],[40,642],[44,280],[45,266],[46,266],[47,641],[47,642],[48,266],[55,641],[55,642],[57,641],[57,642],[60,280],[62,332],[63,652],[67,676],[68,280],[70,280],[71,664],[72,688],[80,652],[85,676]],\"owners\":[[5,266,[77,79,86,87],[30,44,45,46,48]],[30,266,[86,87],[5,44,45,46,48,77,79]],[45,266,[77,79,87],[5,30,44,46,48,86]],[46,266,[77,86],[5,30,44,45,48,79,87]],[48,266,[77,79,86,87],[5,30,44,45,46]],[10,641,[63,67,71,72],[40,47,55,57]],[47,641,[67,72],[10,40,55,57,63,71]],[55,641,[63,71],[10,40,47,57,67,72]],[57,641,[63,67,71,72],[10,40,47,55]],[10,642,[80,85],[40,47,55,57]],[40,642,[],[10,47,55,57,80,85]],[47,642,[85],[10,40,55,57,80]],[55,642,[80],[10,40,47,57,85]],[57,642,[80,85],[10,40,47,55]],[18,280,[77,86,87,89],[44,60,68,70]],[44,280,[89],[18,60,68,70,77,86,87]],[60,280,[86,87],[18,44,68,70,77,89]],[68,280,[77,87,89],[18,44,60,70,86]],[70,280,[77,86],[18,44,60,68,87,89]],[62,332,[79,89],[]],[63,652,[80],[]],[80,652,[63],[]],[67,676,[85],[]],[85,676,[67],[]],[71,664,[],[]],[72,688,[],[]]],\"edges\":[[28,[5,18,30,44,45,46,48,60,62,68,70,77,79,86,87,89]],[43,[10,40,47,55,57,63,67,71,72,80,85]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,21,22,25,26],[-4,25,26],[-7,21,22,26],[-8,21,25],[-10,21,22,25,26],[-2,15,16,19,20],[-9,16,20],[-11,15,19],[-12,15,16,19,20],[-2,23,24],[-5],[-9,24],[-11,23],[-12,23,24],[-3,21,25,26,27],[-6,27],[-13,25,26],[-17,21,26,27],[-18,21,25],[-14,22,27],[-15,23],[-23,15],[-16,24],[-24,16],[-19],[-20],[-28,15,16],[-15,28],[-16,28],[-29,19,20],[-23,30],[-24,30],[-21,31],[-22,31],[-26,32],[-27,32],[-25,33],[-34,28,29],[-28,34],[-30,35],[-36,34,35],[-35,36],[-34,36],[-34,-35,37],[-32,38],[-31,38],[-33,39],[-39,40],[-38,40],[-37,-40,41],[-41],[1,3,4,6,7,8,10,13,14,17,18,21,22,25,26,27],[2,5,9,11,12,15,16,19,20,23,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":266,\"a\":5,\"owners\":[77,79,86,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":30,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":45,\"owners\":[77,79,87]},{\"tag\":\"mate\",\"ridge\":266,\"a\":46,\"owners\":[77,86]},{\"tag\":\"mate\",\"ridge\":266,\"a\":48,\"owners\":[77,79,86,87]},{\"tag\":\"mate\",\"ridge\":641,\"a\":10,\"owners\":[63,67,71,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[63,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[63,67,71,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":10,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":40,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":642,\"a\":47,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":280,\"a\":18,\"owners\":[77,86,87,89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":44,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":60,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":280,\"a\":68,\"owners\":[77,87,89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":70,\"owners\":[77,86]},{\"tag\":\"mate\",\"ridge\":332,\"a\":62,\"owners\":[79,89]},{\"tag\":\"mate\",\"ridge\":652,\"a\":63,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":652,\"a\":80,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":676,\"a\":67,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":676,\"a\":85,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":664,\"a\":71,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":72,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[63,67],\"full_literals\":[-28,15,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-15,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-16,28]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[71,72],\"full_literals\":[-29,19,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-23,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-24,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-21,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-22,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-26,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":89,\"full_literals\":[-27,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-25,33]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-36,34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[5,18,30,44,45,46,48,60,62,68,70,77,79,86,87,89]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[10,40,47,55,57,63,67,71,72,80,85]}]}"
  "54 -29 0 25 26 30 0\n55 -34 28 0 54 38 0\n56 2 9 11 12 15 16 23 24 0 11 25 26 53 0\n57 36 0 42 43 40 39 31 32 28 29 10 13 14 12 56 0\n58 35 0 57 40 41 31 32 55 21 23 27 0\n59 15 16 0 26 25 6 8 9 22 7 24 56 0\n60 28 0 28 29 59 0\n61 34 0 60 39 0\n62 37 0 61 58 44 0\n63 -40 0 62 51 50 0\n64 -39 0 63 48 0\n65 -38 0 63 49 0\n66 -33 0 64 47 0\n67 -32 0 65 45 0\n68 -31 0 65 46 0\n69 -25 0 66 37 0\n70 -26 0 67 35 0\n71 -27 0 67 36 0\n72 -21 0 68 33 0\n73 -22 0 68 34 0\n74 -4 0 69 70 2 0\n75 -13 0 69 70 17 0\n76 -1 0 69 73 72 70 1 0\n77 -8 0 69 72 4 0\n78 -3 0 69 72 70 71 15 0\n79 -18 0 69 72 19 0\n80 -10 0 69 72 73 70 5 0\n81 -6 0 71 16 0\n82 -7 0 72 73 70 3 0\n83 -17 0 72 70 71 18 0\n84 -14 0 73 71 20 0\n85 0 78 80 76 74 82 77 81 75 84 83 79 72 73 69 70 71 52 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae0dc74aaa368ba558d64d87633a2e4789e1783e746b1aa699366392e4d54d4753362d4749d176c370ea364d5334d332cc7332cab46c9b16c3b31e2749c6745c9715c3783d0f23c4f07d540f28a8a9460b951346898a4990e545454550d42d0768350cc388e0b22c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6d36da6da4d249249a49249a4db49a692493492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 54), (facetIndex 65), (facetIndex 69), (facetIndex 84)]))
 (.leaf ([(facetIndex 58), (facetIndex 66), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 47), (facetIndex 51), (facetIndex 55), (facetIndex 56)]))
 (.leaf ([(facetIndex 57), (facetIndex 64), (facetIndex 67), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 29), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 42), (facetIndex 44), (facetIndex 52), (facetIndex 72), (facetIndex 81)]))
 (.leaf ([(facetIndex 59), (facetIndex 62), (facetIndex 63)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 40), (facetIndex 60), (facetIndex 76)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 38), (facetIndex 39)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20006004601643b46a5a404400404116fe0937fez16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 70)]))
 (.branch 2
 (.leaf ([(facetIndex 82), (facetIndex 87)]))
 (.leaf ([(facetIndex 36), (facetIndex 43), (facetIndex 61)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 80), (facetIndex 83), (facetIndex 86)])))
 (.branch 6
 (.leaf ([(facetIndex 45), (facetIndex 48), (facetIndex 50), (facetIndex 53)]))
 (.leaf ([(facetIndex 75), (facetIndex 78), (facetIndex 79), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "330844d98cd8000000010000028145028400002z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [1, 2]
def grouped3_0019 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006" 96

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006" "{\"ridges\":[[6,515],[7,35],[7,515],[9,67],[10,131],[13,37],[18,25],[18,137],[20,137],[20,641],[23,38],[24,322],[27,56],[30,67],[31,131],[31,137],[32,11],[38,37],[38,38],[38,67],[39,35],[39,37],[39,38],[43,25],[44,25],[45,259],[48,35],[48,49],[48,67],[50,49],[50,259],[51,194],[52,67],[54,131],[55,131],[55,194],[56,67],[56,515],[56,641],[57,25],[57,69],[58,152],[60,37],[60,44],[60,545],[62,37],[62,69],[63,37],[63,49],[64,69],[64,208],[66,25],[66,521],[67,152],[67,208],[69,641],[72,38],[74,28],[75,282],[76,38],[76,546],[78,38],[78,52],[79,38],[79,52],[81,262],[82,178],[83,152],[84,642],[85,402]],\"owners\":[[32,11,[4,5,6,42,43,44,47],[0,29,30,45]],[62,37,[1,12,39,40,60],[13,38,63]],[63,37,[1,12,38,40,60],[13,39,62]],[72,38,[1,38,39,40],[23,34,76,78,79]],[57,69,[2,16,38,41],[14,30,61,62,64]],[62,69,[2,16,30,41,61],[14,38,57,64]],[64,69,[2,16,30,38],[14,41,57,61,62]],[45,259,[3,9,39,55],[32,37,50,52,53]],[50,259,[3,9,32,55],[37,39,45,52,53]],[81,262,[3,32,39],[24,37,75,79]],[20,137,[5,18,31,46,47,58,61,65,67],[69]],[66,521,[6,20,33],[19,60,68]],[60,545,[7,54,70],[19,40,66,69]],[76,546,[7,54],[25,40,84]],[51,194,[77],[8,41,47,55,56,80,83,85]],[55,194,[77,80,83],[8,41,47,51,56,85]],[24,322,[9,52,55,85],[81]],[20,641,[10,54,56,70],[68,69]],[56,641,[20,68,69,70],[10,54]],[69,641,[10,56],[20,54,68,70]],[84,642,[10,56],[26,54]],[74,28,[11,27,57,59],[29,58,72,73,75,86]],[60,44,[23,27],[12,76]],[48,49,[13,17,63,65,66,70],[34,42,49,50,62]],[50,49,[13,17,62,65,66,70],[34,42,48,49,63]],[63,49,[17,42,48,49,65,66,70],[13,34,50,62]],[78,52,[13,27,63],[34,62,72,79]],[79,52,[13,27,62],[34,63,72,78]],[27,56,[17,42,65,66,82,87],[72]],[58,152,[82,83,87],[18,44,65,67,68,74,86]],[67,152,[74,82,87],[18,44,58,65,68,83,86]],[83,152,[18,58,65,68,87],[44,67,74,82,86]],[64,208,[83,85],[21,51,67,71,80,86]],[67,208,[80,85],[21,51,64,71,83,86]],[75,282,[45],[]],[82,178,[49],[]],[85,402,[53],[]]],\"edges\":[[15,[3,9,24,32,37,39,45,50,52,53,55,75,79,81,85]],[30,[13,17,27,34,42,48,49,50,62,63,65,66,70,72,78,79,82,87]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-20,-11],[-21,-1],[-21,-3],[-21,-20],[-22,-6],[-23,-1],[-23,-21],[-24,-21],[-24,-22],[-24,-23],[-25,-11],[-25,-21],[-26,-21],[-28,-21],[-28,-23],[-29,-3],[-29,-23],[-29,-24],[-29,-25],[-29,-28],[-30,-2],[-30,-20],[-30,-21],[-30,-24],[-30,-25],[-30,-26],[-30,-28],[-30,-29],[-31,-21],[-31,-23],[-31,-29],[-31,-30],[-32,-21],[-32,-22],[-32,-23],[-32,-29],[-32,-30],[-33,-11],[-33,-24],[-33,-31],[-34,-26],[-34,-28],[-38,-9],[-38,-22],[-38,-37],[-41,-30],[-42,-20],[-42,-25],[-42,-26],[-42,-28],[-42,-35],[-43,-13],[-43,-34],[-43,-42],[-45,-38],[-46,-2],[-46,-21],[-46,-26],[-46,-29],[-46,-43],[-47,-5],[-47,-22],[-47,-27],[-47,-32],[-47,-35],[-47,-37],[-47,-38],[-47,-40],[-47,-44],[-47,-45],[-47,-46],[-49,-22],[-49,-35],[-50,-12],[-50,-23],[-50,-49],[-51,-4],[-51,-14],[-51,-20],[-51,-25],[-51,-33],[-52,-34],[-53,-10],[-53,-48],[-53,-49],[-53,-50],[-54,-30],[-54,-49],[-55,-43],[-55,-53],[-56,-49],[-56,-50],[-56,-51],[-57,-4],[-57,-11],[-57,-33],[-57,-49],[-57,-51],[-57,-56],[-58,-34],[-58,-35],[-59,-22],[-59,-35],[-59,-38],[-59,-52],[-59,-56],[-59,-57],[-60,-57],[-60,-59],[-61,-57],[-61,-59],[-62,-43],[-62,-46],[-62,-53],[-63,-11],[-63,-42],[-63,-51],[-64,-43],[-66,-4],[-66,-33],[-66,-63],[-67,-22],[-69,-30],[-70,-22],[-71,-13],[-71,-34],[-71,-42],[-71,-64],[-71,-70],[-72,-66],[-73,-35],[-73,-38],[-73,-71],[-74,-6],[-74,-24],[-74,-66],[-75,-46],[-76,-57],[-76,-59],[-23,4,5,6,33,34,35,38],[-7,-30,-39],[-53,1,11,30,31,51],[-54,1,11,29,31,51],[-12,-30,-51],[-29,-51,-54],[-30,-51,-53],[-63,1,29,30,31],[-17,-30,-68],[-29,-66,-69],[-8,-29,-47],[-21,-39,-47],[-21,-43,-47],[-29,-43,-47],[-48,2,13,29,32],[-53,2,13,21,32,52],[-55,2,13,21,29],[-36,3,8,30,46],[-41,3,8,23,46],[-71,3,23,30],[-9,-22,-46],[-22,-45,-46],[-16,5,15,22,37,38,49,52,56,58],[-15,-16,-22],[-6,-7,-47],[-57,6,16,24],[-51,7,45,61],[-66,7,45],[-42,67],[-46,67,70,73],[-18,8,43,46,75],[-16,9,45,47,61],[-47,16,59,60,61],[-60,9,47],[-74,9,47],[-15,-34,-57],[-35,-48,-57],[-64,10,19,48,50],[-51,17,19],[-39,12,14,54,56,57,61],[-41,12,14,53,56,57,61],[-54,14,33,39,40,56,57,61],[-68,12,19,54],[-69,12,19,53],[-19,14,33,56,57,72,76],[-49,72,73,76],[-58,64,72,76],[-73,15,49,56,59,76],[-55,73,75],[-58,70,75],[-65,36],[-72,40],[-75,44],[-77,37,45,56,60,74],[-78,49,57,59],[-79,32,38,42,46,47],[-80,48,55,58,62],[-81,20,25,26,28,33,35,43,63,71],[-82,50,53,54],[-83,24,31,51,66],[-84,21,22,23,29,30],[-85,77],[-85,78],[-86,79],[-86,80],[-87,85],[-87,86],[-88,81],[-88,82],[-89,83],[-89,84],[-90,88],[-90,89],[-91,87],[-91,90],[91],[-92,40,61],[-40,92],[-61,92],[-93,72,76],[-72,93],[-76,93],[-94,27,34,52],[-34,94],[-52,94],[-95,93,94],[-94,95],[-93,95],[-96,92,95],[-95,96],[-92,96],[3,8,18,23,28,30,36,41,43,44,46,65,69,71,75],[12,14,19,25,33,39,40,41,53,54,56,57,61,63,68,69,72,76]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":12},{\"tag\":\"incompatible\",\"a\":30,\"b\":1},{\"tag\":\"incompatible\",\"a\":30,\"b\":3},{\"tag\":\"incompatible\",\"a\":30,\"b\":29},{\"tag\":\"incompatible\",\"a\":31,\"b\":6},{\"tag\":\"incompatible\",\"a\":32,\"b\":1},{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":31},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":34,\"b\":12},{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":30},{\"tag\":\"incompatible\",\"a\":37,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":3},{\"tag\":\"incompatible\",\"a\":38,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":33},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":2},{\"tag\":\"incompatible\",\"a\":39,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":33},{\"tag\":\"incompatible\",\"a\":39,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":39,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":39},{\"tag\":\"incompatible\",\"a\":41,\"b\":30},{\"tag\":\"incompatible\",\"a\":41,\"b\":31},{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":12},{\"tag\":\"incompatible\",\"a\":42,\"b\":33},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":43,\"b\":37},{\"tag\":\"incompatible\",\"a\":47,\"b\":10},{\"tag\":\"incompatible\",\"a\":47,\"b\":31},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":29},{\"tag\":\"incompatible\",\"a\":51,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":35},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":44},{\"tag\":\"incompatible\",\"a\":52,\"b\":16},{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":2},{\"tag\":\"incompatible\",\"a\":55,\"b\":30},{\"tag\":\"incompatible\",\"a\":55,\"b\":35},{\"tag\":\"incompatible\",\"a\":55,\"b\":38},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":5},{\"tag\":\"incompatible\",\"a\":56,\"b\":31},{\"tag\":\"incompatible\",\"a\":56,\"b\":36},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":31},{\"tag\":\"incompatible\",\"a\":58,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":13},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":4},{\"tag\":\"incompatible\",\"a\":60,\"b\":17},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":43},{\"tag\":\"incompatible\",\"a\":62,\"b\":11},{\"tag\":\"incompatible\",\"a\":62,\"b\":57},{\"tag\":\"incompatible\",\"a\":62,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":65,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":4},{\"tag\":\"incompatible\",\"a\":66,\"b\":12},{\"tag\":\"incompatible\",\"a\":66,\"b\":42},{\"tag\":\"incompatible\",\"a\":66,\"b\":58},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":31},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":71,\"b\":52},{\"tag\":\"incompatible\",\"a\":71,\"b\":55},{\"tag\":\"incompatible\",\"a\":71,\"b\":62},{\"tag\":\"incompatible\",\"a\":72,\"b\":12},{\"tag\":\"incompatible\",\"a\":72,\"b\":51},{\"tag\":\"incompatible\",\"a\":72,\"b\":60},{\"tag\":\"incompatible\",\"a\":74,\"b\":52},{\"tag\":\"incompatible\",\"a\":76,\"b\":4},{\"tag\":\"incompatible\",\"a\":76,\"b\":42},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":77,\"b\":31},{\"tag\":\"incompatible\",\"a\":79,\"b\":39},{\"tag\":\"incompatible\",\"a\":80,\"b\":31},{\"tag\":\"incompatible\",\"a\":81,\"b\":16},{\"tag\":\"incompatible\",\"a\":81,\"b\":43},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":76},{\"tag\":\"incompatible\",\"a\":83,\"b\":44},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":81},{\"tag\":\"incompatible\",\"a\":84,\"b\":6},{\"tag\":\"incompatible\",\"a\":84,\"b\":33},{\"tag\":\"incompatible\",\"a\":84,\"b\":76},{\"tag\":\"incompatible\",\"a\":85,\"b\":55},{\"tag\":\"incompatible\",\"a\":87,\"b\":66},{\"tag\":\"incompatible\",\"a\":87,\"b\":68},{\"tag\":\"mate\",\"ridge\":11,\"a\":32,\"owners\":[4,5,6,42,43,44,47]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[7,39,48]},{\"tag\":\"mate\",\"ridge\":37,\"a\":62,\"owners\":[1,12,39,40,60]},{\"tag\":\"mate\",\"ridge\":37,\"a\":63,\"owners\":[1,12,38,40,60]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[13,39,60]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[38,60,63]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[39,60,62]},{\"tag\":\"mate\",\"ridge\":38,\"a\":72,\"owners\":[1,38,39,40]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[23,39,78]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[38,76,79]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[9,38,56]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[30,48,56]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[30,52,56]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[38,52,56]},{\"tag\":\"mate\",\"ridge\":69,\"a\":57,\"owners\":[2,16,38,41]},{\"tag\":\"mate\",\"ridge\":69,\"a\":62,\"owners\":[2,16,30,41,61]},{\"tag\":\"mate\",\"ridge\":69,\"a\":64,\"owners\":[2,16,30,38]},{\"tag\":\"mate\",\"ridge\":259,\"a\":45,\"owners\":[3,9,39,55]},{\"tag\":\"mate\",\"ridge\":259,\"a\":50,\"owners\":[3,9,32,55]},{\"tag\":\"mate\",\"ridge\":262,\"a\":81,\"owners\":[3,32,39]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[10,31,55]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[31,54,55]},{\"tag\":\"mate\",\"ridge\":137,\"a\":20,\"owners\":[5,18,31,46,47,58,61,65,67]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[18,20,31]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[6,7,56]},{\"tag\":\"mate\",\"ridge\":521,\"a\":66,\"owners\":[6,20,33]},{\"tag\":\"mate\",\"ridge\":545,\"a\":60,\"owners\":[7,54,70]},{\"tag\":\"mate\",\"ridge\":546,\"a\":76,\"owners\":[7,54]},{\"tag\":\"mate\",\"ridge\":194,\"a\":51,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":194,\"a\":55,\"owners\":[77,80,83]},{\"tag\":\"mate\",\"ridge\":322,\"a\":24,\"owners\":[9,52,55,85]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[10,54,56,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[20,68,69,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[10,56]},{\"tag\":\"mate\",\"ridge\":642,\"a\":84,\"owners\":[10,56]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[18,43,66]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[44,57,66]},{\"tag\":\"mate\",\"ridge\":28,\"a\":74,\"owners\":[11,27,57,59]},{\"tag\":\"mate\",\"ridge\":44,\"a\":60,\"owners\":[23,27]},{\"tag\":\"mate\",\"ridge\":49,\"a\":48,\"owners\":[13,17,63,65,66,70]},{\"tag\":\"mate\",\"ridge\":49,\"a\":50,\"owners\":[13,17,62,65,66,70]},{\"tag\":\"mate\",\"ridge\":49,\"a\":63,\"owners\":[17,42,48,49,65,66,70]},{\"tag\":\"mate\",\"ridge\":52,\"a\":78,\"owners\":[13,27,63]},{\"tag\":\"mate\",\"ridge\":52,\"a\":79,\"owners\":[13,27,62]},{\"tag\":\"mate\",\"ridge\":56,\"a\":27,\"owners\":[17,42,65,66,82,87]},{\"tag\":\"mate\",\"ridge\":152,\"a\":58,\"owners\":[82,83,87]},{\"tag\":\"mate\",\"ridge\":152,\"a\":67,\"owners\":[74,82,87]},{\"tag\":\"mate\",\"ridge\":152,\"a\":83,\"owners\":[18,58,65,68,87]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[83,85]},{\"tag\":\"mate\",\"ridge\":208,\"a\":67,\"owners\":[80,85]},{\"tag\":\"mate\",\"ridge\":282,\"a\":75,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":178,\"a\":82,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":402,\"a\":85,\"owners\":[53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[46,54,65,69,84],\"full_literals\":[-77,37,45,56,60,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[58,66,68],\"full_literals\":[-78,49,57,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,47,51,55,56],\"full_literals\":[-79,32,38,42,46,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[57,64,67,71],\"full_literals\":[-80,48,55,58,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[29,34,35,37,42,44,52,72,81],\"full_literals\":[-81,20,25,26,28,33,35,43,63,71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[59,62,63],\"full_literals\":[-82,50,53,54]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,40,60,76],\"full_literals\":[-83,24,31,51,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[30,31,32,38,39],\"full_literals\":[-84,21,22,23,29,30]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-85,77,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,79,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,80],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-87,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,false,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,81,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,false,82],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-90,88,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-90,false,89],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-91,87,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-91,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[49,70],\"full_literals\":[-92,40,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-40,92]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-61,92]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[82,87],\"full_literals\":[-93,72,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-72,93]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":87,\"full_literals\":[-76,93]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[36,43,61],\"full_literals\":[-94,27,34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":43,\"full_literals\":[-34,94]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-52,94]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,93,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-96,92,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"edge\",\"edge\":15,\"owners\":[3,9,24,32,37,39,45,50,52,53,55,75,79,81,85]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[13,17,27,34,42,48,49,50,62,63,65,66,70,72,78,79,82,87]}]}"
  "233 87 0 215 213 0\n234 90 0 215 214 0\n235 85 0 233 205 0\n236 86 0 233 206 0\n237 88 0 234 211 0\n238 89 0 234 212 0\n239 77 0 235 201 0\n240 78 0 235 202 0\n241 79 0 236 203 0\n242 80 0 236 204 0\n243 81 0 237 207 0\n244 82 0 237 208 0\n245 83 0 238 209 0\n246 84 0 238 210 0\n247 29 30 21 22 51 11 0 246 244 200 6 30 75 142 143 198 0\n248 -57 -47 22 34 0 239 245 246 70 67 66 65 61 94 96 98 99 108 193 134 135 136 140 199 29 31 32 200 0\n249 -31 22 0 246 29 30 31 32 200 0\n250 23 29 30 51 -47 22 0 246 245 243 65 249 200 2 3 4 8 12 13 14 152 147 159 199 197 120 0\n251 29 30 51 -47 22 34 0 245 70 67 65 61 249 250 7 10 247 199 38 119 167 140 164 0\n252 30 51 -47 22 34 0 245 69 192 71 249 251 16 17 18 20 150 153 159 199 157 158 170 149 190 231 0\n253 -43 -30 32 93 0 242 28 21 221 220 52 89 112 118 154 196 186 0\n254 51 -47 22 95 0 245 243 244 240 239 226 223 248 70 66 65 64 249 227 221 220 224 252 21 22 23 24 25 26 27 87 199 120 121 136 253 197 125 133 155 185 198 194 92 109 193 0\n255 -30 -7 -51 57 96 0 229 227 221 220 93 81 78 184 178 117 80 230 218 217 46 87 123 146 144 141 148 232 0\n256 53 54 63 56 33 25 14 57 96 0 244 229 227 221 220 184 230 218 217 198 74 182 183 180 179 232 0\n257 -53 19 93 0 242 221 220 83 84 86 90 114 177 196 186 0\n258 -47 22 96 0 246 229 227 221 220 226 223 230 218 217 61 65 67 70 248 254 77 78 80 81 93 117 166 184 164 140 255 257 256 181 145 151 200 0\n259 -32 22 0 246 33 35 36 37 200 0\n260 -42 35 25 63 33 0 243 47 49 50 54 127 197 0\n261 -20 -46 22 0 59 57 1 22 79 247 0\n262 -28 -46 22 0 246 59 57 15 27 200 0\n263 -46 35 25 63 33 22 93 0 243 242 259 221 220 56 57 58 59 60 113 261 262 197 125 128 156 154 186 196 0\n264 -38 56 47 0 239 43 45 55 174 173 193 0\n265 -42 25 63 33 0 51 260 0\n266 -35 57 0 240 73 103 194 0\n267 57 25 63 33 47 22 93 0 241 240 265 259 221 220 266 263 195 104 132 194 185 0\n268 25 63 33 47 22 93 0 241 242 259 265 267 99 264 195 113 137 263 101 131 176 196 188 0\n269 -25 22 0 11 12 19 25 80 247 0\n270 -63 22 0 245 249 115 117 121 199 8 18 24 247 0\n271 22 96 0 245 229 227 249 258 269 270 268 39 81 120 199 0\n272 96 0 240 241 229 227 221 271 5 9 34 44 62 72 102 122 124 194 168 99 165 195 163 169 187 0\n273 -22 42 0 241 240 5 9 34 44 62 72 102 195 194 160 161 110 165 171 0\n274 -57 24 -93 31 0 245 98 138 199 219 130 0\n275 -46 35 25 63 33 0 243 242 265 273 259 56 57 58 59 60 113 137 261 262 197 125 129 156 154 189 196 0\n276 57 47 25 63 33 0 241 240 265 273 259 266 275 195 104 264 194 91 0\n277 47 25 63 33 0 265 273 249 268 276 95 98 274 8 18 24 247 0\n278 -57 -47 22 0 67 66 61 97 99 107 108 110 248 172 82 100 175 162 0\n279 -49 0 244 76 85 88 198 0\n280 25 63 33 0 243 245 272 239 240 279 265 277 273 63 65 66 68 70 278 249 191 194 105 106 109 111 139 193 216 219 135 136 228 199 225 79 222 41 42 53 126 197 0\n281 -25 0 48 269 273 0\n282 -63 0 116 270 273 0\n283 33 0 282 281 280 0\n284 -24 0 283 39 0\n285 -31 0 283 40 0\n286 -51 0 283 81 0\n287 -66 0 283 120 0\n288 0 287 286 245 285 284 199 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2b2b2a9a36a3a71aa6358b65392e1b91e1783eac6c9a64d98e5c5a94d52d54d4b46d4745d0f6c370ea3a4cd38ccb3c2e8b92ccb4ac6b86d1b26c5ba1d8789d2729c6745c5743c4f0bc1f52a2a0e946318960d9498a439514c525435a0d4330e2324c3382d0b12c2b06d0721c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da4d24db69b6d26926db492492492492492492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 36), (facetIndex 40), (facetIndex 57), (facetIndex 68), (facetIndex 83)]))
 (.leaf ([(facetIndex 45), (facetIndex 53), (facetIndex 55), (facetIndex 69), (facetIndex 84)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 65), (facetIndex 66)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 59), (facetIndex 64), (facetIndex 74), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 39), (facetIndex 41)])))
 (.branch 7
 (.leaf ([(facetIndex 52), (facetIndex 54), (facetIndex 56), (facetIndex 58)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10246000c000809300078638effffcffe8b50a186cz16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 67), (facetIndex 73)]))
 (.branch 2
 (.leaf ([(facetIndex 82), (facetIndex 88)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72)]))))
 (.branch 4
 (.leaf ([(facetIndex 85), (facetIndex 86), (facetIndex 87)]))
 (.branch 5
 (.leaf ([(facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "16d804016da02480000924z2d;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4, 5]
def grouped3_0023 : List Nat := [4, 5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013" 49

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013" "{\"ridges\":[[15,641],[15,642],[41,641],[41,642],[50,641],[55,641],[55,642],[56,641],[56,642],[58,641],[58,642],[65,145],[67,676],[70,216],[71,664],[72,712],[73,688],[80,146],[82,676],[86,664],[87,712],[88,688]],\"owners\":[[65,145,[11,43,54,55,70,71],[17,52,66,73]],[80,146,[11,43,54,55,85,86],[24,52,81,88]],[15,641,[67,71,72,73],[41,50,55,56,58]],[41,641,[71,72,73],[15,50,55,56,58,67]],[50,641,[67,73],[15,41,55,56,58,71,72]],[55,641,[67,72],[15,41,50,56,58,71,73]],[56,641,[71,72],[15,41,50,55,58,67,73]],[58,641,[67,71,73],[15,41,50,55,56,72]],[15,642,[82,86,87,88],[41,50,55,56,58]],[41,642,[86,87,88],[15,50,55,56,58,82]],[55,642,[82,87],[15,41,50,56,58,86,88]],[56,642,[86,87],[15,41,50,55,58,82,88]],[58,642,[82,86,88],[15,41,50,55,56,87]],[67,676,[82],[]],[82,676,[67],[]],[70,216,[85],[]],[71,664,[86],[]],[86,664,[71],[]],[72,712,[87],[]],[87,712,[72],[]],[73,688,[88],[]],[88,688,[73],[]]],\"edges\":[[43,[15,41,50,55,56,58,67,71,72,73,82,86,87,88]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-1],[-13,-3],[-13,-5],[-13,-10],[-13,-11],[-14,-8],[-14,-12],[-15,-10],[-22,-3],[-22,-8],[-22,-12],[-22,-14],[-23,-3],[-23,-10],[-23,-15],[-27,-6],[-27,-9],[-27,-17],[-27,-25],[-28,-13],[-14,1,5,10,11,18,19],[-22,1,5,10,11,26,27],[-2,16,19,20,21],[-4,19,20,21],[-7,16,21],[-11,16,20],[-12,19,20],[-13,16,19,21],[-2,24,27,28,29],[-4,27,28,29],[-11,24,28],[-12,27,28],[-13,24,27,29],[-16,24],[-24,16],[-18,26],[-19,27],[-27,19],[-20,28],[-28,20],[-21,29],[-29,21],[-30,6,9,11,17,25],[-31,3,14,15],[-32,22,23],[-33,8,10,12,13],[-34,30],[-35,31],[-36,34],[-36,35],[-37,32],[-38,33],[-39,37],[-39,38],[-40,36],[-40,39],[40],[-41,16,21],[-16,41],[-21,41],[-24,42],[-29,42],[-19,43],[-20,43],[-26,44],[-27,44],[-43,45],[-42,45],[-46,41,45],[-45,46],[-41,46],[-41,-45,47],[-44,48],[-47,-48,49],[-49],[2,4,7,11,12,13,16,19,20,21,24,27,28,29]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":58,\"b\":11},{\"tag\":\"incompatible\",\"a\":58,\"b\":37},{\"tag\":\"incompatible\",\"a\":58,\"b\":43},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":52},{\"tag\":\"incompatible\",\"a\":65,\"b\":56},{\"tag\":\"incompatible\",\"a\":66,\"b\":54},{\"tag\":\"incompatible\",\"a\":80,\"b\":37},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":56},{\"tag\":\"incompatible\",\"a\":80,\"b\":65},{\"tag\":\"incompatible\",\"a\":81,\"b\":37},{\"tag\":\"incompatible\",\"a\":81,\"b\":54},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":86,\"b\":45},{\"tag\":\"incompatible\",\"a\":86,\"b\":53},{\"tag\":\"incompatible\",\"a\":86,\"b\":69},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"mate\",\"ridge\":145,\"a\":65,\"owners\":[11,43,54,55,70,71]},{\"tag\":\"mate\",\"ridge\":146,\"a\":80,\"owners\":[11,43,54,55,85,86]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[67,71,72,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":41,\"owners\":[71,72,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":50,\"owners\":[67,73]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":641,\"a\":58,\"owners\":[67,71,73]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[82,86,87,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":41,\"owners\":[86,87,88]},{\"tag\":\"mate\",\"ridge\":642,\"a\":55,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":58,\"owners\":[82,86,88]},{\"tag\":\"mate\",\"ridge\":676,\"a\":67,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":676,\"a\":82,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":216,\"a\":70,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":664,\"a\":71,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":664,\"a\":86,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":712,\"a\":72,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":712,\"a\":87,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":688,\"a\":73,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":688,\"a\":88,\"owners\":[73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[45,53,55,69,84],\"full_literals\":[-30,6,9,11,17,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[37,65,66],\"full_literals\":[-31,3,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[80,81],\"full_literals\":[-32,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[52,54,56,58],\"full_literals\":[-33,8,10,12,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-36,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-37,32,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-39,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-40,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[67,73],\"full_literals\":[-41,16,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":67,\"full_literals\":[-16,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":73,\"full_literals\":[-21,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-29,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-19,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-20,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":85,\"full_literals\":[-26,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-27,44]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-46,41,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,41,50,55,56,58,67,71,72,73,82,86,87,88]}]}"
  "77 36 0 57 55 0\n78 39 0 57 56 0\n79 34 0 77 49 0\n80 35 0 77 50 0\n81 37 0 78 53 0\n82 38 0 78 54 0\n83 30 0 79 47 0\n84 31 0 80 48 0\n85 32 0 81 51 0\n86 33 0 82 52 0\n87 46 0 70 71 67 68 59 60 63 64 61 62 23 25 27 38 28 40 26 24 76 0\n88 45 0 87 68 69 61 62 34 41 58 0\n89 27 28 41 0 59 35 31 39 60 42 25 32 37 29 33 30 76 0\n90 28 41 0 83 59 35 31 89 16 17 18 19 43 0\n91 -22 13 0 86 84 9 10 11 12 46 44 8 0\n92 13 0 85 84 86 91 45 13 14 15 44 6 7 46 0\n93 -1 0 92 1 0\n94 -3 0 92 2 0\n95 -5 0 92 3 0\n96 -10 0 92 4 0\n97 -11 0 92 5 0\n98 -28 0 92 20 0\n99 41 0 98 90 0\n100 47 0 99 88 72 0\n101 -48 0 100 75 74 0\n102 -44 0 101 73 0\n103 -26 0 102 65 0\n104 -27 0 102 66 0\n105 -18 0 103 36 0\n106 -22 0 103 95 93 97 96 104 22 0\n107 -19 0 104 37 0\n108 -14 0 105 95 96 97 93 107 21 0\n109 23 0 106 85 45 0\n110 15 0 108 84 94 44 0\n111 0 109 110 15 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record013
