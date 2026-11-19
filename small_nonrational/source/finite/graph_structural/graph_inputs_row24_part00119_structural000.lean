module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00119Data
public import GraphInputsRow24Part00119Frames
public import GraphInputsRow24Part00119Leaves
public import GraphInputsRow24Part00119Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010
def vertexColumn : Fields := ⟨10, hexnat% "1f1aa96a3a2e87a69a56358b61d94e4b86e1783e6a5998e4b91e5a565655354755352d1b51d1743d68e9394cd38ccb31cf0b62d4b8ad2b2ac6b86c9b16c3b91d4731d2719e1725c570dd0f13c2f07e582d24a618a6944b19261916439614a5254550d58390ca382d0b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db4da6db6db4924926db4934da6924924d24924d2492649249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e70c97f3f9f0000000", hexnat% "8100000000080200000000", hexnat% "800100200000000000000", hexnat% "80000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400e87f2f970000000", hexnat% "250000000000000000", hexnat% "800000090000000000", hexnat% "1a0000000200000000", hexnat% "900000000000000000000", hexnat% "8000000010000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bb0007fbfbf0000000", hexnat% "400410000000000000", hexnat% "800000200000000000000", hexnat% "40880000000000000", hexnat% "8100000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81007b0690bbfbf0000000", hexnat% "800800000000000000", hexnat% "800000000400000000000", hexnat% "40000000000000000", 1970324836974592]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800310217fbfbf0000000", hexnat% "a0000000000000000", hexnat% "c00400000000000000", hexnat% "8100000080000000000000", hexnat% "40800000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100210097fbfbf0000000", hexnat% "60800000000000000", hexnat% "180000000000000000", hexnat% "c00400000000000000", hexnat% "800000200000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80003b0014b0fbf0000000", 144748506773454848, hexnat% "40880020000000000", hexnat% "c00400010000000000", hexnat% "900000000000000000000", 290271069732864]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bf0c80022b70000000", 282299610431488, hexnat% "400002200000000000", hexnat% "8100000010090080000000", hexnat% "800000200401000000000", 1284229581242368]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b0800000a20000000", hexnat% "40080028100000000", hexnat% "e00400010000000000", hexnat% "800100200003000000000", hexnat% "8100000010080080000000", 844700881780736, 1389782965944320]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c2
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019
def vertexColumn : Fields := ⟨10, hexnat% "7a338751b4731ac4f16a8e93a558d64d8b65392e8791e0f9e1746b16c5c96a5693a6394e5c569595554d54d4b56354d3352d2b61d4743d38cd32ce4b1ae1b0ecc729e1725c570de0f0bc1f6c1c46514c8ca2a13a312c629314951362384c3382c4b0ac4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4936d36db4db6da4db69a69a69a4db6db49249a492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨67, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20080000180000000000", hexnat% "2000040000180400000", 25794969600, 1729452660014186496, hexnat% "c0000004000000000000", 503316480, 4785075677822976]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021
def vertexColumn : Fields := ⟨10, hexnat% "7c1e8751b4731accc9aa8e9a6559366394e4b8ae8785e0f9e1745b15c4f1aa4e9966391e5c569595554d54d4b52b61d1743d68d534ccab86c5b0ed8751d2729e1745c570de0f23c4f0bc1f71154332324ca2a45a31326292a4c51548d1362384c3382c2b05c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4d34d349b6db6db6d269a6d26d34db4934db692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000011000000000000", 216208241363779584, hexnat% "8400000008008000000", hexnat% "800002000030000000", hexnat% "2000040082800400000", 125829120, 1073741824]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2743d29c970bc9c99a968ba69a6695a362d876c398e938ae8789e1783e3c599964b9694e5954d52d475934ad8749d1743d68d9394cb362e4b2ae1b46c9b16c3b61e4751d2729e1725c570de0f23c4f0bc1f632521ca1a918668390e2c47162499614a51950d2346314c3342c1b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6d34da4da4934db49a49b49a69b6d24da4924924da492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 54), (facetIndex 56), (facetIndex 64), (facetIndex 66)]))
 (.leaf ([(facetIndex 31), (facetIndex 58), (facetIndex 59), (facetIndex 62), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 49), (facetIndex 83), (facetIndex 85)]))
 (.leaf ([(facetIndex 29), (facetIndex 35), (facetIndex 36), (facetIndex 39), (facetIndex 63)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 47), (facetIndex 48), (facetIndex 74)]))
 (.leaf ([(facetIndex 30), (facetIndex 71), (facetIndex 73), (facetIndex 75)])))
 (.branch 7
 (.leaf ([(facetIndex 26), (facetIndex 40), (facetIndex 43), (facetIndex 44)]))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 32), (facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 76), (facetIndex 79), (facetIndex 80)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "202008800854505000100031001100000000244006642637733007153776z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 46), (facetIndex 53)]))
 (.leaf ([(facetIndex 55), (facetIndex 57), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 65), (facetIndex 87)]))
 (.leaf ([(facetIndex 33), (facetIndex 45), (facetIndex 50), (facetIndex 51)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 70), (facetIndex 72), (facetIndex 81), (facetIndex 84)]))
 (.leaf ([(facetIndex 52), (facetIndex 60), (facetIndex 77), (facetIndex 78), (facetIndex 88)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 82), (facetIndex 86)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b55c41e016800410e0100150082056c0018000000018z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7, 8]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7]
def grouped3_0023 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002" 78

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002" "{\"ridges\":[[14,152],[17,176],[19,524],[22,536],[24,592],[30,524],[33,150],[42,152],[44,536],[48,176],[49,592],[50,402],[52,60],[54,152],[59,176],[60,212],[61,533],[64,176],[65,585],[66,152],[67,176],[68,60],[70,150],[71,524],[71,536],[72,170],[73,524],[75,524],[77,150],[78,564],[79,580],[81,418],[82,170],[83,536],[84,402],[85,592],[86,60],[87,92],[88,660],[89,212],[90,564]],\"owners\":[[14,152,[70,82,84,86,88],[42,54,64,66]],[42,152,[86,88],[14,54,64,66,70,82,84]],[54,152,[82,84],[14,42,64,66,70,86,88]],[66,152,[70,82,86,88],[14,42,54,64,84]],[17,176,[77,82,86,89],[48,59,64,67]],[48,176,[86,89],[17,59,64,67,77,82]],[59,176,[82],[17,48,64,67,77,86,89]],[64,176,[77,89],[17,48,59,67,82,86]],[67,176,[77,82,86],[17,48,59,64,89]],[19,524,[55,57,87,88],[30,71,73,75]],[30,524,[87,88],[19,55,57,71,73,75]],[71,524,[57],[19,30,55,73,75,87,88]],[73,524,[55,88],[19,30,57,71,75,87]],[75,524,[55,57,87,88],[19,30,71,73]],[79,580,[57],[21,38,61,73,80,87,90]],[22,536,[55,65,87,88],[44,71,83]],[44,536,[87,88],[22,55,65,71,83]],[71,536,[65],[22,44,55,83,87,88]],[83,536,[55,88],[22,44,65,71,87]],[24,592,[61,65,87,90],[49,79,83,85]],[49,592,[87,90],[24,61,65,79,83,85]],[85,592,[61,65,87],[24,49,79,83,90]],[33,150,[70,77],[]],[70,150,[33,77],[]],[77,150,[33,70],[]],[61,533,[34,55],[]],[72,170,[45,82],[]],[82,170,[45,72],[]],[65,585,[46,57],[]],[50,402,[84],[]],[84,402,[50],[]],[81,418,[51],[]],[52,60,[68,86],[]],[68,60,[52,86],[]],[86,60,[52,68],[]],[87,92,[53,69],[]],[60,212,[89],[]],[89,212,[60],[]],[78,564,[90],[]],[90,564,[78],[]],[88,660,[],[]]],\"edges\":[[29,[19,22,30,44,46,55,57,65,71,73,75,83,87,88]],[32,[14,17,33,42,48,50,54,59,60,64,66,67,70,77,82,84,86,88,89]],[34,[22,24,34,44,49,55,61,65,71,78,79,83,85,87,88,90]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-6],[-14,-12],[-45,-10],[-45,-11],[-45,-13],[-45,-16],[-45,-17],[-45,-39],[-1,35,45,47,49,51],[-11,49,51],[-23,45,47],[-31,35,45,49,51],[-2,41,45,49,52],[-17,49,52],[-26,45],[-29,41,52],[-32,41,45,49],[-3,24,25,50,51],[-7,50,51],[-36,25],[-38,24,51],[-40,24,25,50,51],[-43,25],[-4,24,30,50,51],[-13,50,51],[-36,30],[-46,24,51],[-5,28,30,50,53],[-18,50,53],[-48,28,30,50],[-8,35,41],[-35,8,41],[-41,8,35],[-28,9,24],[-37,14,45],[-45,14,37],[-30,15,25],[-19,47],[-47,19],[-44,20],[-21,33,49],[-33,21,49],[-49,21,33],[-50,22,34],[-27,52],[-52,27],[-42,53],[-53,42],[-51],[-54,11,16,17,39],[-55,6,10,12,13],[-56,54],[-57,55],[-58,56,57],[-59,58],[59],[-9,60],[-15,60],[-22,60],[-24,61],[-25,61],[-34,61],[-30,62],[-50,62],[-8,63],[-14,63],[-19,63],[-20,63],[-64,35,37,44,47],[-35,64],[-37,64],[-47,64],[-65,21,27,41,42,51],[-21,65],[-27,65],[-41,65],[-42,65],[-66,33,52,53],[-33,66],[-52,66],[-53,66],[-67,45,49],[-45,67],[-49,67],[-61,68],[-60,68],[-63,69],[-62,69],[-69,70],[-68,70],[-68,-69,71],[-72,64,65],[-65,72],[-64,72],[-64,-65,73],[-74,66,67],[-67,74],[-66,74],[-66,-67,75],[-76,72,74],[-75,77],[-72,76],[-72,-74,77],[-73,77],[-70,-77,78],[-71,-76,78],[-78],[3,4,7,13,15,24,25,30,36,38,40,46,50,51],[1,2,8,11,17,19,23,26,27,29,31,32,35,41,45,47,49,51,52],[4,5,9,13,18,24,28,30,36,42,43,46,48,50,51,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":26},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":82,\"b\":40},{\"tag\":\"incompatible\",\"a\":82,\"b\":42},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":82,\"b\":47},{\"tag\":\"incompatible\",\"a\":82,\"b\":48},{\"tag\":\"incompatible\",\"a\":82,\"b\":74},{\"tag\":\"mate\",\"ridge\":152,\"a\":14,\"owners\":[70,82,84,86,88]},{\"tag\":\"mate\",\"ridge\":152,\"a\":42,\"owners\":[86,88]},{\"tag\":\"mate\",\"ridge\":152,\"a\":54,\"owners\":[82,84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":66,\"owners\":[70,82,86,88]},{\"tag\":\"mate\",\"ridge\":176,\"a\":17,\"owners\":[77,82,86,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":48,\"owners\":[86,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":59,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":176,\"a\":64,\"owners\":[77,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":67,\"owners\":[77,82,86]},{\"tag\":\"mate\",\"ridge\":524,\"a\":19,\"owners\":[55,57,87,88]},{\"tag\":\"mate\",\"ridge\":524,\"a\":30,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":524,\"a\":71,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":524,\"a\":73,\"owners\":[55,88]},{\"tag\":\"mate\",\"ridge\":524,\"a\":75,\"owners\":[55,57,87,88]},{\"tag\":\"mate\",\"ridge\":580,\"a\":79,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":536,\"a\":22,\"owners\":[55,65,87,88]},{\"tag\":\"mate\",\"ridge\":536,\"a\":44,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":536,\"a\":71,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":536,\"a\":83,\"owners\":[55,88]},{\"tag\":\"mate\",\"ridge\":592,\"a\":24,\"owners\":[61,65,87,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":49,\"owners\":[87,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":85,\"owners\":[61,65,87]},{\"tag\":\"mate\",\"ridge\":150,\"a\":33,\"owners\":[70,77]},{\"tag\":\"mate\",\"ridge\":150,\"a\":70,\"owners\":[33,77]},{\"tag\":\"mate\",\"ridge\":150,\"a\":77,\"owners\":[33,70]},{\"tag\":\"mate\",\"ridge\":533,\"a\":61,\"owners\":[34,55]},{\"tag\":\"mate\",\"ridge\":170,\"a\":72,\"owners\":[45,82]},{\"tag\":\"mate\",\"ridge\":170,\"a\":82,\"owners\":[45,72]},{\"tag\":\"mate\",\"ridge\":585,\"a\":65,\"owners\":[46,57]},{\"tag\":\"mate\",\"ridge\":402,\"a\":50,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":402,\"a\":84,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":418,\"a\":81,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":60,\"a\":52,\"owners\":[68,86]},{\"tag\":\"mate\",\"ridge\":60,\"a\":68,\"owners\":[52,86]},{\"tag\":\"mate\",\"ridge\":60,\"a\":86,\"owners\":[52,68]},{\"tag\":\"mate\",\"ridge\":92,\"a\":87,\"owners\":[53,69]},{\"tag\":\"mate\",\"ridge\":212,\"a\":60,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":212,\"a\":89,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":564,\"a\":78,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":564,\"a\":90,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":660,\"a\":88,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[42,47,48,74],\"full_literals\":[-54,11,16,17,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[26,40,43,44],\"full_literals\":[-55,6,10,12,13]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-57,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-58,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":34,\"full_literals\":[-9,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-15,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-22,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":55,\"full_literals\":[-24,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-25,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-34,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-30,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-50,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":33,\"full_literals\":[-8,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":45,\"full_literals\":[-14,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-19,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":51,\"full_literals\":[-20,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[70,72,81,84],\"full_literals\":[-64,35,37,44,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-35,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-37,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-47,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[52,60,77,78,88],\"full_literals\":[-65,21,27,41,42,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-21,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-27,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-41,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-42,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[68,89,90],\"full_literals\":[-66,33,52,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-33,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-52,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-53,66]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[82,86],\"full_literals\":[-67,45,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-45,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-49,67]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-65,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-76,78],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[19,22,30,44,46,55,57,65,71,73,75,83,87,88]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[14,17,33,42,48,50,54,59,60,64,66,67,70,77,82,84,86,88,89]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[22,24,34,44,49,55,61,65,71,78,79,83,85,87,88,90]}]}"
  "p cnf 78 110\n-14 -6 0\n-14 -12 0\n-45 -10 0\n-45 -11 0\n-45 -13 0\n-45 -16 0\n-45 -17 0\n-45 -39 0\n-1 35 45 47 49 51 0\n-11 49 51 0\n-23 45 47 0\n-31 35 45 49 51 0\n-2 41 45 49 52 0\n-17 49 52 0\n-26 45 0\n-29 41 52 0\n-32 41 45 49 0\n-3 24 25 50 51 0\n-7 50 51 0\n-36 25 0\n-38 24 51 0\n-40 24 25 50 51 0\n-43 25 0\n-4 24 30 50 51 0\n-13 50 51 0\n-36 30 0\n-46 24 51 0\n-5 28 30 50 53 0\n-18 50 53 0\n-48 28 30 50 0\n-8 35 41 0\n-35 8 41 0\n-41 8 35 0\n-28 9 24 0\n-37 14 45 0\n-45 14 37 0\n-30 15 25 0\n-19 47 0\n-47 19 0\n-44 20 0\n-21 33 49 0\n-33 21 49 0\n-49 21 33 0\n-50 22 34 0\n-27 52 0\n-52 27 0\n-42 53 0\n-53 42 0\n-51 0\n-54 11 16 17 39 0\n-55 6 10 12 13 0\n-56 54 0\n-57 55 0\n-58 56 57 0\n-59 58 0\n59 0\n-9 60 0\n-15 60 0\n-22 60 0\n-24 61 0\n-25 61 0\n-34 61 0\n-30 62 0\n-50 62 0\n-8 63 0\n-14 63 0\n-19 63 0\n-20 63 0\n-64 35 37 44 47 0\n-35 64 0\n-37 64 0\n-47 64 0\n-65 21 27 41 42 51 0\n-21 65 0\n-27 65 0\n-41 65 0\n-42 65 0\n-66 33 52 53 0\n-33 66 0\n-52 66 0\n-53 66 0\n-67 45 49 0\n-45 67 0\n-49 67 0\n-61 68 0\n-60 68 0\n-63 69 0\n-62 69 0\n-69 70 0\n-68 70 0\n-68 -69 71 0\n-72 64 65 0\n-65 72 0\n-64 72 0\n-64 -65 73 0\n-74 66 67 0\n-67 74 0\n-66 74 0\n-66 -67 75 0\n-76 72 74 0\n-75 77 0\n-72 76 0\n-72 -74 77 0\n-73 77 0\n-70 -77 78 0\n-71 -76 78 0\n-78 0\n3 4 7 13 15 24 25 30 36 38 40 46 50 51 0\n1 2 8 11 17 19 23 26 27 29 31 32 35 41 45 47 49 51 52 0\n4 5 9 13 18 24 28 30 36 42 43 46 48 50 51 53 0\n"
  "111 58 0 56 55 0\n112 -65 21 27 41 42 0 49 73 0\n113 3 4 7 13 15 24 25 30 36 38 40 46 50 0 49 108 0\n114 1 2 8 11 17 19 23 26 27 29 31 32 35 41 45 47 49 52 0 49 109 0\n115 4 5 9 13 18 24 28 30 36 42 43 46 48 50 53 0 49 110 0\n116 70 0 49 89 90 88 85 86 63 64 60 61 58 26 19 25 18 21 22 27 24 113 0\n117 -77 0 116 107 105 0\n118 -75 0 117 101 0\n119 -73 0 117 104 0\n120 -67 45 21 0 118 82 99 43 79 0\n121 67 -74 0 117 103 93 77 48 75 46 74 84 96 42 78 0\n122 -74 0 117 111 103 93 94 74 71 121 120 3 4 5 6 7 8 36 50 1 2 52 51 54 53 0\n123 -67 0 122 97 0\n124 -66 0 122 98 0\n125 -45 0 123 83 0\n126 -49 0 123 84 0\n127 -33 0 124 79 0\n128 -52 0 124 80 0\n129 -53 0 124 81 0\n130 -26 0 125 15 0\n131 -11 0 126 49 10 0\n132 -17 0 126 128 14 0\n133 -21 0 126 127 41 0\n134 -27 0 128 45 0\n135 -42 0 129 47 0\n136 68 0 49 129 135 85 86 60 61 62 57 58 59 27 34 20 23 37 44 30 28 24 25 29 115 0\n137 65 -76 0 122 125 136 107 106 91 87 68 40 67 39 66 35 65 100 76 92 32 69 0\n138 -76 0 107 136 135 133 134 119 106 91 87 65 137 112 95 33 70 0\n139 -72 0 138 102 0\n140 -65 0 139 93 0\n141 -64 0 139 94 0\n142 -41 0 140 76 0\n143 -35 0 141 70 0\n144 -47 0 141 72 0\n145 -29 0 142 128 16 0\n146 -2 0 142 126 125 128 13 0\n147 -32 0 142 126 125 17 0\n148 -8 0 143 142 31 0\n149 -31 0 143 125 126 49 12 0\n150 -1 0 143 125 126 144 49 9 0\n151 -19 0 144 38 0\n152 -23 0 144 125 11 0\n153 0 147 152 150 148 131 151 132 130 134 145 149 146 143 142 125 144 126 128 114 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6725c2f2723ca9a968ba69a562d87663a4e2ba1e2785e0fa713c699666592e5a5656552d58d934ad8751d2745d0f5a398ce3a4e5334e332cc73c2e8b92cab86c9b16c3b61e4751d2729e1725c570de0f23c4f0bc1f1d18a1990e944b11c58986499194550d50d0758390ca318e0b42c8b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6936db6924936926d249249a6d249249b4924da492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 35), (facetIndex 39), (facetIndex 59), (facetIndex 64), (facetIndex 65), (facetIndex 81)]))
 (.leaf ([(facetIndex 26), (facetIndex 31), (facetIndex 32), (facetIndex 42), (facetIndex 43), (facetIndex 48), (facetIndex 49), (facetIndex 52), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 54), (facetIndex 56)]))
 (.branch 4
 (.leaf ([(facetIndex 57), (facetIndex 66), (facetIndex 73)]))
 (.leaf ([(facetIndex 55), (facetIndex 74)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 28), (facetIndex 45), (facetIndex 58), (facetIndex 70)]))
 (.leaf ([(facetIndex 61), (facetIndex 69), (facetIndex 71), (facetIndex 72)])))
 (.branch 8
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 37), (facetIndex 38)]))
 (.branch 9
 (.leaf ([(facetIndex 60)]))
 (.leaf ([(facetIndex 44), (facetIndex 46), (facetIndex 47)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100000004366560030000680532420100119959110007720001170571z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 41), (facetIndex 63)]))
 (.leaf ([(facetIndex 76), (facetIndex 78), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 84), (facetIndex 87), (facetIndex 92)]))
 (.leaf ([(facetIndex 33), (facetIndex 62), (facetIndex 67), (facetIndex 68)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 77), (facetIndex 79), (facetIndex 85), (facetIndex 93)]))
 (.leaf ([(facetIndex 40), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 75), (facetIndex 88), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 86), (facetIndex 91)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "22fb65e2a01861c000036000c0000028b40000005000018z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3, 4]
def grouped2_0006 : List Nat := [5]
def grouped2_0007 : List Nat := [5, 6]
def grouped2_0008 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0009 : List Nat := [6]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8, 9]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9]
def grouped2_0014 : List Nat := [9]
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
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7]
def grouped3_0029 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003" 86

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003" "{\"ridges\":[[6,522],[9,578],[16,152],[17,536],[20,176],[21,592],[30,522],[33,150],[38,578],[42,152],[43,536],[45,522],[45,578],[46,522],[47,522],[49,176],[50,562],[52,592],[55,578],[59,152],[61,536],[63,588],[65,176],[66,592],[67,404],[69,152],[69,176],[70,536],[70,592],[71,152],[72,152],[72,529],[72,536],[73,176],[74,592],[80,588],[84,534],[90,562],[92,588],[93,404]],\"owners\":[[6,522,[78,80,87,88],[30,43,45,46,47]],[30,522,[87,88],[6,43,45,46,47,78,80]],[45,522,[78,88],[6,30,43,46,47,80,87]],[46,522,[78,80,87],[6,30,43,45,47,88]],[47,522,[78,80,87,88],[6,30,43,45,46]],[9,578,[80,84,87,90],[38,45,52,55]],[38,578,[87,90],[9,45,52,55,80,84]],[45,578,[84,90],[9,38,52,55,80,87]],[55,578,[80,84,87],[9,38,45,52,90]],[16,152,[77,86,88,91,93],[42,59,69,71,72]],[42,152,[91,93],[16,59,69,71,72,77,86,88]],[59,152,[86,88],[16,42,69,71,72,77,91,93]],[69,152,[77,88,93],[16,42,59,71,72,86,91]],[71,152,[77,86,88,91],[16,42,59,69,72,93]],[72,152,[77,86,91,93],[16,42,59,69,71,88]],[72,529,[21,34,50,52,66,74],[17,43,53,61]],[17,536,[78,87,88,92],[43,61,70,72]],[43,536,[92],[17,61,70,72,78,87,88]],[61,536,[87,88],[17,43,70,72,78,92]],[70,536,[78,88],[17,43,61,72,87,92]],[72,536,[78,87,92],[17,43,61,70,88]],[20,176,[83,86,89,91],[49,65,69,73]],[49,176,[91],[20,65,69,73,83,86,89]],[65,176,[86,89],[20,49,69,73,83,91]],[69,176,[83,89],[20,49,65,73,86,91]],[73,176,[83,86,91],[20,49,65,69,89]],[21,592,[84,87,90,92],[52,66,70,74]],[52,592,[92],[21,66,70,74,84,87,90]],[66,592,[87,90],[21,52,70,74,84,92]],[70,592,[84,90],[21,52,66,74,87,92]],[74,592,[84,87,92],[21,52,66,70,90]],[33,150,[77,83],[]],[84,534,[34,78],[]],[50,562,[90],[]],[90,562,[50],[]],[63,588,[80,92],[]],[80,588,[63,92],[]],[92,588,[63,80],[]],[67,404,[93],[]],[93,404,[67],[]]],\"edges\":[[29,[6,17,30,43,45,46,47,61,63,70,72,78,80,87,88,92]],[32,[16,20,33,42,49,51,53,59,65,67,69,71,72,73,77,83,86,88,89,91,93]],[41,[9,21,38,45,52,55,63,66,70,74,80,84,87,90,92]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-30,-29],[-37,-29],[-38,-29],[-43,-13],[-46,-12],[-46,-15],[-46,-21],[-46,-23],[-46,-25],[-46,-41],[-46,-45],[-47,-46],[-48,-7],[-48,-8],[-48,-10],[-48,-11],[-48,-15],[-48,-20],[-48,-21],[-48,-27],[-48,-44],[-48,-45],[-49,-46],[-50,-46],[-50,-48],[-51,-49],[-1,42,43,48,49],[-9,48,49],[-17,42,49],[-18,42,43,48],[-19,42,43,48,49],[-2,43,46,48,51],[-14,48,51],[-17,46,51],[-26,43,46,48],[-3,41,47,49,52,54],[-15,52,54],[-28,47,49],[-35,41,49,54],[-37,41,47,49,52],[-38,41,47,52,54],[-38,6,13,22,24,33,40],[-4,42,48,49,53],[-16,53],[-30,48,49],[-36,42,49],[-38,42,48,53],[-5,45,47,50,52],[-21,52],[-32,47,50],[-35,45,50],[-39,45,47,52],[-6,46,48,51,53],[-24,53],[-33,48,51],[-36,46,51],[-40,46,48,53],[-12,41,45],[-46,13,42],[-22,51],[-51,22],[-31,43,53],[-43,31,53],[-53,31,43],[-34,54],[-54,34],[-55,7,10,11,15,16,20,21,24,44],[-56,8,17,27,36],[-57,30,35,37,38],[-58,29],[-59,55],[-60,59],[-61,56,57],[-62,56],[-63,58],[-64,63],[-65,61],[-65,62,64],[-66,60,65],[66],[-13,67],[-31,67],[-42,68],[-43,68],[-46,69],[-48,69],[-53,69],[-12,70],[-34,70],[-41,71],[-54,71],[-22,72],[-23,72],[-25,72],[-45,72],[-49,73],[-50,73],[-51,73],[-47,74],[-52,74],[-68,75],[-67,75],[-67,-68,76],[-70,77],[-69,77],[-69,-70,78],[-77,79],[-75,79],[-75,-77,80],[-75,-78,81],[-76,80],[-76,-77,81],[-72,82],[-71,82],[-74,83],[-73,83],[-83,84],[-82,84],[-82,-83,85],[-79,-85,86],[-80,-84,86],[-81,86],[-86],[1,4,9,16,17,18,19,30,31,36,38,42,43,48,49,53],[3,5,12,15,21,23,25,28,32,34,35,37,38,39,41,45,47,49,50,52,54],[2,6,14,17,24,26,31,33,36,40,43,46,48,51,53]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":72,\"b\":60},{\"tag\":\"incompatible\",\"a\":80,\"b\":34},{\"tag\":\"incompatible\",\"a\":84,\"b\":33},{\"tag\":\"incompatible\",\"a\":84,\"b\":42},{\"tag\":\"incompatible\",\"a\":84,\"b\":49},{\"tag\":\"incompatible\",\"a\":84,\"b\":51},{\"tag\":\"incompatible\",\"a\":84,\"b\":53},{\"tag\":\"incompatible\",\"a\":84,\"b\":77},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":26},{\"tag\":\"incompatible\",\"a\":87,\"b\":28},{\"tag\":\"incompatible\",\"a\":87,\"b\":31},{\"tag\":\"incompatible\",\"a\":87,\"b\":32},{\"tag\":\"incompatible\",\"a\":87,\"b\":42},{\"tag\":\"incompatible\",\"a\":87,\"b\":48},{\"tag\":\"incompatible\",\"a\":87,\"b\":49},{\"tag\":\"incompatible\",\"a\":87,\"b\":58},{\"tag\":\"incompatible\",\"a\":87,\"b\":82},{\"tag\":\"incompatible\",\"a\":87,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":88},{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[78,80,87,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":30,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":45,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":46,\"owners\":[78,80,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":47,\"owners\":[78,80,87,88]},{\"tag\":\"mate\",\"ridge\":578,\"a\":9,\"owners\":[80,84,87,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":38,\"owners\":[87,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":45,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":578,\"a\":55,\"owners\":[80,84,87]},{\"tag\":\"mate\",\"ridge\":152,\"a\":16,\"owners\":[77,86,88,91,93]},{\"tag\":\"mate\",\"ridge\":152,\"a\":42,\"owners\":[91,93]},{\"tag\":\"mate\",\"ridge\":152,\"a\":59,\"owners\":[86,88]},{\"tag\":\"mate\",\"ridge\":152,\"a\":69,\"owners\":[77,88,93]},{\"tag\":\"mate\",\"ridge\":152,\"a\":71,\"owners\":[77,86,88,91]},{\"tag\":\"mate\",\"ridge\":152,\"a\":72,\"owners\":[77,86,91,93]},{\"tag\":\"mate\",\"ridge\":529,\"a\":72,\"owners\":[21,34,50,52,66,74]},{\"tag\":\"mate\",\"ridge\":536,\"a\":17,\"owners\":[78,87,88,92]},{\"tag\":\"mate\",\"ridge\":536,\"a\":43,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":536,\"a\":61,\"owners\":[87,88]},{\"tag\":\"mate\",\"ridge\":536,\"a\":70,\"owners\":[78,88]},{\"tag\":\"mate\",\"ridge\":536,\"a\":72,\"owners\":[78,87,92]},{\"tag\":\"mate\",\"ridge\":176,\"a\":20,\"owners\":[83,86,89,91]},{\"tag\":\"mate\",\"ridge\":176,\"a\":49,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":176,\"a\":65,\"owners\":[86,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":69,\"owners\":[83,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":73,\"owners\":[83,86,91]},{\"tag\":\"mate\",\"ridge\":592,\"a\":21,\"owners\":[84,87,90,92]},{\"tag\":\"mate\",\"ridge\":592,\"a\":52,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":592,\"a\":66,\"owners\":[87,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":70,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":592,\"a\":74,\"owners\":[84,87,92]},{\"tag\":\"mate\",\"ridge\":150,\"a\":33,\"owners\":[77,83]},{\"tag\":\"mate\",\"ridge\":534,\"a\":84,\"owners\":[34,78]},{\"tag\":\"mate\",\"ridge\":562,\"a\":50,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":562,\"a\":90,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":588,\"a\":63,\"owners\":[80,92]},{\"tag\":\"mate\",\"ridge\":588,\"a\":80,\"owners\":[63,92]},{\"tag\":\"mate\",\"ridge\":588,\"a\":92,\"owners\":[63,80]},{\"tag\":\"mate\",\"ridge\":404,\"a\":67,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":404,\"a\":93,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[26,31,32,42,43,48,49,52,82],\"full_literals\":[-55,7,10,11,15,16,20,21,24,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[28,45,58,70],\"full_literals\":[-56,8,17,27,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[61,69,71,72],\"full_literals\":[-57,30,35,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[60],\"full_literals\":[-58,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-65,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,62,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,60,65],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":34,\"full_literals\":[-13,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-31,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-42,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-43,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":84,\"full_literals\":[-46,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-48,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":92,\"full_literals\":[-53,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":33,\"full_literals\":[-12,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":67,\"full_literals\":[-34,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":77,\"full_literals\":[-41,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":93,\"full_literals\":[-54,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":50,\"full_literals\":[-22,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":51,\"full_literals\":[-23,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":53,\"full_literals\":[-25,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-45,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-49,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-50,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-51,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-47,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":91,\"full_literals\":[-52,74]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-67,-68,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-77,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-75,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-82,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-85,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,17,30,43,45,46,47,61,63,70,72,78,80,87,88,92]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[16,20,33,42,49,51,53,59,65,67,69,71,72,73,77,83,86,88,89,91,93]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[9,21,38,45,52,55,63,66,70,74,80,84,87,90,92]}]}"
  "p cnf 86 126\n-30 -29 0\n-37 -29 0\n-38 -29 0\n-43 -13 0\n-46 -12 0\n-46 -15 0\n-46 -21 0\n-46 -23 0\n-46 -25 0\n-46 -41 0\n-46 -45 0\n-47 -46 0\n-48 -7 0\n-48 -8 0\n-48 -10 0\n-48 -11 0\n-48 -15 0\n-48 -20 0\n-48 -21 0\n-48 -27 0\n-48 -44 0\n-48 -45 0\n-49 -46 0\n-50 -46 0\n-50 -48 0\n-51 -49 0\n-1 42 43 48 49 0\n-9 48 49 0\n-17 42 49 0\n-18 42 43 48 0\n-19 42 43 48 49 0\n-2 43 46 48 51 0\n-14 48 51 0\n-17 46 51 0\n-26 43 46 48 0\n-3 41 47 49 52 54 0\n-15 52 54 0\n-28 47 49 0\n-35 41 49 54 0\n-37 41 47 49 52 0\n-38 41 47 52 54 0\n-38 6 13 22 24 33 40 0\n-4 42 48 49 53 0\n-16 53 0\n-30 48 49 0\n-36 42 49 0\n-38 42 48 53 0\n-5 45 47 50 52 0\n-21 52 0\n-32 47 50 0\n-35 45 50 0\n-39 45 47 52 0\n-6 46 48 51 53 0\n-24 53 0\n-33 48 51 0\n-36 46 51 0\n-40 46 48 53 0\n-12 41 45 0\n-46 13 42 0\n-22 51 0\n-51 22 0\n-31 43 53 0\n-43 31 53 0\n-53 31 43 0\n-34 54 0\n-54 34 0\n-55 7 10 11 15 16 20 21 24 44 0\n-56 8 17 27 36 0\n-57 30 35 37 38 0\n-58 29 0\n-59 55 0\n-60 59 0\n-61 56 57 0\n-62 56 0\n-63 58 0\n-64 63 0\n-65 61 0\n-65 62 64 0\n-66 60 65 0\n66 0\n-13 67 0\n-31 67 0\n-42 68 0\n-43 68 0\n-46 69 0\n-48 69 0\n-53 69 0\n-12 70 0\n-34 70 0\n-41 71 0\n-54 71 0\n-22 72 0\n-23 72 0\n-25 72 0\n-45 72 0\n-49 73 0\n-50 73 0\n-51 73 0\n-47 74 0\n-52 74 0\n-68 75 0\n-67 75 0\n-67 -68 76 0\n-70 77 0\n-69 77 0\n-69 -70 78 0\n-77 79 0\n-75 79 0\n-75 -77 80 0\n-75 -78 81 0\n-76 80 0\n-76 -77 81 0\n-72 82 0\n-71 82 0\n-74 83 0\n-73 83 0\n-83 84 0\n-82 84 0\n-82 -83 85 0\n-79 -85 86 0\n-80 -84 86 0\n-81 86 0\n-86 0\n1 4 9 16 17 18 19 30 31 36 38 42 43 48 49 53 0\n3 5 12 15 21 23 25 28 32 34 35 37 38 39 41 45 47 49 50 52 54 0\n2 6 14 17 24 26 31 33 36 40 43 46 48 51 53 0\n"
  "127 -81 0 123 122 0\n128 51 79 0 107 105 86 85 108 101 84 35 87 57 54 102 82 34 55 53 56 33 32 126 0\n129 79 0 107 108 105 101 102 86 87 83 84 82 44 47 30 128 26 28 45 27 29 31 43 46 124 0\n130 -85 0 129 123 120 0\n131 -51 0 130 61 98 92 116 113 119 0\n132 -22 0 131 60 0\n133 43 46 48 53 0 131 56 53 34 57 33 55 54 35 62 32 126 0\n134 46 48 53 0 131 132 127 123 55 54 57 53 133 4 63 84 42 82 103 111 112 121 104 117 118 88 89 115 116 113 114 66 99 100 96 97 93 94 95 90 39 38 50 37 49 48 52 36 40 125 0\n135 84 38 -46 0 24 12 50 23 38 11 51 10 9 8 7 6 5 117 118 115 114 100 91 48 52 36 40 65 125 0\n136 75 -46 0 101 102 83 81 59 0\n137 -46 0 127 123 10 12 85 105 136 110 109 106 121 89 117 135 66 115 41 100 0\n138 -17 0 137 131 34 0\n139 -36 0 137 131 56 0\n140 53 0 137 138 139 80 44 54 134 13 14 15 16 17 18 19 20 21 22 25 67 68 51 71 74 72 79 77 78 73 76 75 70 1 2 3 69 0\n141 69 0 140 87 0\n142 77 0 141 105 0\n143 84 0 117 118 115 116 113 114 99 100 96 97 93 94 95 90 91 38 50 37 49 48 52 36 40 41 51 58 65 125 0\n144 -80 0 143 123 121 0\n145 -75 0 144 142 109 0\n146 -68 0 145 101 0\n147 -67 0 145 102 0\n148 -43 0 146 84 0\n149 -31 0 147 82 0\n150 0 148 149 140 64 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00119.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00119.record003
