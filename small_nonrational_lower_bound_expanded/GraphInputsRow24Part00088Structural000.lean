module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00088Data
public import GraphInputsRow24Part00088Frames
public import GraphInputsRow24Part00088Leaves
public import GraphInputsRow24Part00088Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 19241453486080, (certNat% 3), (certNat% 4)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 19241453486080, (certNat% 3), (certNat% 6), (certNat% 4)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 184750702592, 168225279049728, (certNat% 9), (certNat% 4)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), 141801029632, 1924145348608]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 12), (certNat% 13), 3023656976384, (certNat% 16)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), 214748364800, (certNat% 21)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 150633093005312, (certNat% 23), (certNat% 24), 4947802324992]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 24), 4947802324992, (certNat% 26), (certNat% 27), 18691831889920]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 30), (certNat% 13), 2203385331712, 137438953472]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), (certNat% 24), (certNat% 34), 3848374583296, 152471339008]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c17 c4
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003
def vertexColumn : Fields := ⟨10, (certNat% 35)⟩
def kindColumn : Fields := ⟨3, (certNat% 36)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨57, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨79, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), 2243003720663040, 8244189724672]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005
def vertexColumn : Fields := ⟨10, (certNat% 41)⟩
def kindColumn : Fields := ⟨3, (certNat% 42)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), 69659000832, 34359738368]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 48), 9223372054437298176, 107911053312, 4612248968380809216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), 17609365913600, (certNat% 51), 107202383708160, 106837311488]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), 13835058055684816896, 88583700480, 288230376151711744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 87960930222080, (certNat% 56), (certNat% 57), (certNat% 58), (certNat% 59)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 13835058055416381440, 35218731827200, (certNat% 61), 88583700480, 88510686035968]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 64), 92341796864, (certNat% 65), (certNat% 45)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 64), 288230393331580928, (certNat% 65), (certNat% 67), 69256347648]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), (certNat% 71), 17746939084800, (certNat% 72)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 13835058055282163712, (certNat% 74), (certNat% 50), 36319317196800, (certNat% 75)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), 106652627894272, (certNat% 77), (certNat% 78), (certNat% 50), (certNat% 79)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), 4611686018964258816, (certNat% 50), 106652627894272, (certNat% 44), 106300440576]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 17746804867072, 70368746274816, (certNat% 82), 13835058055282163712, (certNat% 74)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 17746804867072, (certNat% 84), 70368746274816, 13836183955189006336, (certNat% 74)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), 13835058055282163712, 17746804867072, (certNat% 74)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), 106652627894272, 13836183955189006336, (certNat% 88), (certNat% 89), (certNat% 90), 92878667776]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c24 c7
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c26 c5
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c27 c4
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c29 c2
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record005_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008
def vertexColumn : Fields := ⟨10, (certNat% 91)⟩
def kindColumn : Fields := ⟨3, (certNat% 92)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 94), (certNat% 95), 1587659606136455168, 657543137782136832, 6579477580611584]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 97), (certNat% 98), (certNat% 99), 6561885394567168, (certNat% 100)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), (certNat% 102), (certNat% 103), 6597069766656000, 657525545596092416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), (certNat% 106), (certNat% 107), (certNat% 108), (certNat% 109)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), (certNat% 112), 648518346341351424, (certNat% 113)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 111), (certNat% 115), 648518346341351424, (certNat% 116)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), (certNat% 118), (certNat% 106), 648518346341351424, (certNat% 119), (certNat% 100)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), 7740561859543040, (certNat% 121), (certNat% 122), 1459166279268040704]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), 1459166313627779072, (certNat% 124), (certNat% 125), (certNat% 126), 684564735546359808]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), 9007199791611904, (certNat% 128), 2053641430080946176, (certNat% 129)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), (certNat% 131), 621496748577128448, (certNat% 132), 1170935903116328960]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), (certNat% 134), 1155314041908887552, 27021598301093888, (certNat% 135), (certNat% 128)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 136), 73201086130814976, (certNat% 125), (certNat% 137), 4785074604081152, (certNat% 138)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 139), (certNat% 140), 649644796004007936, (certNat% 141), (certNat% 142), (certNat% 113)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 143), (certNat% 144), (certNat% 125), 685690635453202432, (certNat% 145), (certNat% 146), 5348024557502464]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c24 c3
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c25 c2
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c26 c1
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f4ab0bcaa95ab1aa6399561db0ea3a2e4b8ae8791e0f8f1726a9564d92e6c5716a539555354b51d70da358d8b52d2b61d4749d0f6c3a8ce354c73c2e8b52ccb8ad2b2ae1b46c5bc1e8791cc789d2729c6785d1783d0f23c2f07c3a518560da892a439a1545314a51543550c530ce0b42c2b06e0741c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6da4db6db4da6d24924934db4db4db4924d2492492492492691249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 48), (facetIndex 76)]))
 (.leaf ([(facetIndex 30), (facetIndex 41), (facetIndex 51), (facetIndex 68), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 67), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 28), (facetIndex 29), (facetIndex 55), (facetIndex 59), (facetIndex 63), (facetIndex 79)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 42), (facetIndex 44), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 66), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 33), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 50), (facetIndex 65), (facetIndex 87)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1e0000060002a4915786006006003e080410cdb2db6c5b0d8z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 74), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 52), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 57), (facetIndex 92)]))
 (.leaf ([(facetIndex 89), (facetIndex 96)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 82), (facetIndex 90), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64), (facetIndex 80), (facetIndex 85)]))
 (.branch 8
 (.leaf ([(facetIndex 81), (facetIndex 83), (facetIndex 84), (facetIndex 86), (facetIndex 94)]))
 (.leaf ([(facetIndex 93), (facetIndex 95)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "387825530076775760100000000000006066606260441z18;4z1b;"⟩
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
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006" "{\"ridges\":[[15,196],[36,196],[43,168],[46,202],[48,648],[52,226],[54,706],[67,196],[69,196],[71,196],[72,196],[74,216],[76,648],[77,456],[78,240],[85,142]],\"owners\":[[15,196,[89,91,96],[36,67,69,71,72]],[36,196,[96],[15,67,69,71,72,89,91]],[67,196,[89,91],[15,36,69,71,72,96]],[69,196,[91],[15,36,67,71,72,89,96]],[71,196,[89,91,96],[15,36,67,69,72]],[72,196,[89,96],[15,36,67,69,71,91]],[43,168,[94,95],[19,59,73,76,82,93]],[48,648,[95],[20,63,76,85,93]],[76,648,[85],[20,48,63,93,95]],[85,142,[27,82],[]],[46,202,[],[]],[52,226,[89],[]],[54,706,[91],[]],[74,216,[],[]],[77,456,[],[]],[78,240,[96],[]]],\"edges\":[[39,[15,36,46,52,54,67,69,71,72,74,77,78,89,91,96]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-4],[-8,-5],[-8,-7],[-10,-8],[-12,-8],[-28,-6],[-28,-11],[-29,-6],[-29,-11],[-29,-26],[-32,-13],[-32,-16],[-32,-27],[-1,28,29,32],[-3,32],[-17,28,29],[-18,29],[-19,28,29,32],[-20,28,32],[-6,30,31],[-11,31],[-22,26],[-26,2,25],[-9],[-14,28],[-15,29],[-21],[-23],[-24,32],[-33,6,8,11,22],[-34,4,5,7,10,12],[-35,13,16,27],[-36,33],[-37,36],[-38,34],[-39,35],[-40,38],[-40,39],[-41,37],[-41,40],[41],[-14,42],[-24,42],[-28,43],[-32,43],[-2,44],[-25,45],[-26,46],[-30,47],[-31,48],[-42,49],[-43,50],[-50,51],[-49,51],[-45,52],[-44,52],[-48,53],[-47,53],[-53,54],[-46,54],[-52,-54,55],[-51,-55,56],[-56],[1,3,9,14,15,17,18,19,20,21,23,24,28,29,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":45,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":89,\"b\":43},{\"tag\":\"incompatible\",\"a\":89,\"b\":48},{\"tag\":\"incompatible\",\"a\":91,\"b\":43},{\"tag\":\"incompatible\",\"a\":91,\"b\":48},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"incompatible\",\"a\":96,\"b\":50},{\"tag\":\"incompatible\",\"a\":96,\"b\":65},{\"tag\":\"incompatible\",\"a\":96,\"b\":87},{\"tag\":\"mate\",\"ridge\":196,\"a\":15,\"owners\":[89,91,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":36,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":67,\"owners\":[89,91]},{\"tag\":\"mate\",\"ridge\":196,\"a\":69,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":196,\"a\":71,\"owners\":[89,91,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":72,\"owners\":[89,96]},{\"tag\":\"mate\",\"ridge\":168,\"a\":43,\"owners\":[94,95]},{\"tag\":\"mate\",\"ridge\":648,\"a\":48,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":648,\"a\":76,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":142,\"a\":85,\"owners\":[27,82]},{\"tag\":\"mate\",\"ridge\":202,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":226,\"a\":52,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":706,\"a\":54,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":216,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":456,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":78,\"owners\":[96]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[43,45,48,76],\"full_literals\":[-33,6,8,11,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[40,42,44,47,49],\"full_literals\":[-34,4,5,7,10,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[50,65,87],\"full_literals\":[-35,13,16,27]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-38,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-39,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,38,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":52,\"full_literals\":[-14,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-28,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-32,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":27,\"full_literals\":[-2,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-25,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":85,\"full_literals\":[-26,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":94,\"full_literals\":[-30,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":95,\"full_literals\":[-31,48]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[15,36,46,52,54,67,69,71,72,74,77,78,89,91,96]}]}"
  "65 37 0 41 39 0\n66 40 0 41 40 0\n67 36 0 65 34 0\n68 38 0 66 37 0\n69 39 0 66 38 0\n70 33 0 67 33 0\n71 34 0 68 35 0\n72 35 0 69 36 0\n73 1 3 14 15 17 18 19 20 24 28 29 32 0 24 27 28 64 0\n74 29 51 0 53 52 45 15 44 19 54 51 43 42 17 26 14 16 18 73 0\n75 -8 0 71 1 2 3 4 5 31 0\n76 -29 0 75 70 8 9 10 30 22 0\n77 -18 0 76 17 0\n78 -15 0 76 26 0\n79 51 0 76 74 0\n80 -55 0 79 63 62 0\n81 54 0 75 70 59 60 57 58 48 50 49 22 21 20 30 0\n82 -52 0 81 80 61 0\n83 -45 0 82 55 0\n84 -44 0 82 56 0\n85 -25 0 83 47 0\n86 -2 0 84 46 0\n87 -26 0 85 86 23 0\n88 -22 0 87 22 0\n89 28 32 0 76 77 78 29 15 19 25 14 16 18 73 0\n90 -28 0 75 88 70 6 7 30 0\n91 32 0 90 89 0\n92 -13 0 91 11 0\n93 -16 0 91 12 0\n94 -27 0 91 13 0\n95 0 92 93 72 94 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c9caaa95a368bab1aa6399561db0e8b92e8791e0f8f1726a9564d92e6c5a94e555475c362d4b61d4743db0dc3a8ce354cd32cc73c2d8b52ccb8ad2b86d1b26c5bc1e8791cc789d2729c6785d1783d0f0bc1fa28aa0e94615836a24a90e54515435a0d4330ca314c3382d0b22c2b06e0741c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b4da6da4db6d369b4db49b6da492492492492492492492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 68), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 76), (facetIndex 85)]))
 (.leaf ([(facetIndex 86), (facetIndex 87)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 89), (facetIndex 90), (facetIndex 92)]))
 (.leaf ([(facetIndex 93)])))
 (.branch 7
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2c1206d01fffc2209000036dbz2e;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007" "{\"ridges\":[[4,517],[8,265],[13,193],[30,265],[31,517],[33,517],[37,517],[38,193],[38,194],[39,517],[40,518],[41,517],[44,265],[46,265],[48,193],[48,194],[49,266],[50,265],[51,265],[54,193],[56,193],[58,193],[59,193],[68,228],[69,676],[70,708],[72,216],[73,344],[75,456],[76,240],[85,228],[86,676],[87,708],[89,216],[90,344],[92,456],[93,240]],\"owners\":[[4,517,[62,64,65,69,70],[31,33,37,39,40,41]],[31,517,[69,70],[4,33,37,39,40,41,62,64,65]],[33,517,[64,65,69,70],[4,31,37,39,40,41,62]],[37,517,[62,65,70],[4,31,33,39,40,41,64,69]],[39,517,[62,64,65,69],[4,31,33,37,40,41,70]],[41,517,[62,64,69,70],[4,31,33,37,39,40,65]],[40,518,[79,81,82],[4,31,33,37,39,41,86,87]],[8,265,[61,63,65,73,75],[30,44,46,49,50,51]],[30,265,[73,75],[8,44,46,49,50,51,61,63,65]],[44,265,[63,65,75],[8,30,46,49,50,51,61,73]],[46,265,[61,65,73,75],[8,30,44,49,50,51,63]],[50,265,[61,63,65,73],[8,30,44,46,49,51,75]],[51,265,[61,63,73,75],[8,30,44,46,49,50,65]],[49,266,[78,80,82],[8,30,44,46,50,51,90,92]],[13,193,[68,70,72,75,76],[38,48,54,56,58,59]],[38,193,[72,75,76],[13,48,54,56,58,59,68,70]],[48,193,[68,70,76],[13,38,54,56,58,59,72,75]],[54,193,[68,70,75],[13,38,48,56,58,59,72,76]],[56,193,[70,72,75],[13,38,48,54,58,59,68,76]],[58,193,[68,70,72,76],[13,38,48,54,56,59,75]],[59,193,[68,72,75,76],[13,38,48,54,56,58,70]],[38,194,[89,92,93],[13,48,54,56,58,59,85,87]],[48,194,[85,87,93],[13,38,54,56,58,59,89,92]],[68,228,[85],[]],[85,228,[68],[]],[69,676,[86],[]],[86,676,[69],[]],[70,708,[87],[]],[87,708,[70],[]],[72,216,[89],[]],[89,216,[72],[]],[73,344,[90],[]],[90,344,[73],[]],[75,456,[92],[]],[92,456,[75],[]],[76,240,[93],[]],[93,240,[76],[]]],\"edges\":[[23,[4,31,33,37,39,40,41,62,64,65,69,70,79,81,82,86,87]],[28,[8,30,44,46,49,50,51,61,63,65,73,75,78,80,82,90,92]],[39,[13,38,48,54,56,58,59,68,70,72,75,76,85,87,89,92,93]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,23,25,26,28,29],[-5,28,29],[-6,25,26,28,29],[-7,23,26,29],[-9,23,25,26,28],[-11,23,25,28,29],[-10,35,37,38],[-2,22,24,26,31,32],[-4,31,32],[-12,24,26,32],[-13,22,26,31,32],[-16,22,24,26,31],[-17,22,24,31,32],[-15,34,36,38],[-3,27,29,30,32,33],[-8,30,32,33],[-14,27,29,33],[-18,27,29,32],[-19,29,30,32],[-20,27,29,30,33],[-21,27,30,32,33],[-8,42,44,45],[-14,39,41,45],[-27,39],[-39,27],[-28,40],[-40,28],[-29,41],[-41,29],[-30,42],[-42,30],[-31,43],[-43,31],[-32,44],[-44,32],[-33,45],[-45,33],[-46,27,28,29],[-27,46],[-28,46],[-29,46],[-47,30,31,32],[-30,47],[-31,47],[-32,47],[-33,48],[-39,48],[-40,49],[-41,49],[-42,50],[-43,50],[-44,50],[-45,51],[-22,52],[-23,52],[-24,52],[-25,52],[-26,52],[-34,53],[-35,53],[-36,53],[-37,53],[-38,53],[-54,46,47],[-47,54],[-46,54],[-46,-47,55],[-49,56],[-48,56],[-57,54,56],[-56,57],[-54,57],[-54,-56,58],[-55,58],[-51,59],[-50,59],[-53,60],[-52,60],[-60,61],[-59,61],[-59,-60,62],[-57,-62,63],[-58,-61,63],[-63],[1,5,6,7,9,10,11,23,25,26,28,29,35,37,38,40,41],[2,4,12,13,15,16,17,22,24,26,31,32,34,36,38,43,44],[3,8,14,18,19,20,21,27,29,30,32,33,39,41,42,44,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":517,\"a\":4,\"owners\":[62,64,65,69,70]},{\"tag\":\"mate\",\"ridge\":517,\"a\":31,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":517,\"a\":33,\"owners\":[64,65,69,70]},{\"tag\":\"mate\",\"ridge\":517,\"a\":37,\"owners\":[62,65,70]},{\"tag\":\"mate\",\"ridge\":517,\"a\":39,\"owners\":[62,64,65,69]},{\"tag\":\"mate\",\"ridge\":517,\"a\":41,\"owners\":[62,64,69,70]},{\"tag\":\"mate\",\"ridge\":518,\"a\":40,\"owners\":[79,81,82]},{\"tag\":\"mate\",\"ridge\":265,\"a\":8,\"owners\":[61,63,65,73,75]},{\"tag\":\"mate\",\"ridge\":265,\"a\":30,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":265,\"a\":44,\"owners\":[63,65,75]},{\"tag\":\"mate\",\"ridge\":265,\"a\":46,\"owners\":[61,65,73,75]},{\"tag\":\"mate\",\"ridge\":265,\"a\":50,\"owners\":[61,63,65,73]},{\"tag\":\"mate\",\"ridge\":265,\"a\":51,\"owners\":[61,63,73,75]},{\"tag\":\"mate\",\"ridge\":266,\"a\":49,\"owners\":[78,80,82]},{\"tag\":\"mate\",\"ridge\":193,\"a\":13,\"owners\":[68,70,72,75,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":38,\"owners\":[72,75,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":48,\"owners\":[68,70,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":54,\"owners\":[68,70,75]},{\"tag\":\"mate\",\"ridge\":193,\"a\":56,\"owners\":[70,72,75]},{\"tag\":\"mate\",\"ridge\":193,\"a\":58,\"owners\":[68,70,72,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":59,\"owners\":[68,72,75,76]},{\"tag\":\"mate\",\"ridge\":194,\"a\":38,\"owners\":[89,92,93]},{\"tag\":\"mate\",\"ridge\":194,\"a\":48,\"owners\":[85,87,93]},{\"tag\":\"mate\",\"ridge\":228,\"a\":68,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":228,\"a\":85,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":676,\"a\":69,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":676,\"a\":86,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":708,\"a\":70,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":708,\"a\":87,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":216,\"a\":72,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":216,\"a\":89,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":344,\"a\":73,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":344,\"a\":90,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":456,\"a\":75,\"owners\":[92]},{\"tag\":\"mate\",\"ridge\":456,\"a\":92,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":240,\"a\":76,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":240,\"a\":93,\"owners\":[76]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[68,69,70],\"full_literals\":[-46,27,28,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-27,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-28,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-29,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[72,73,75],\"full_literals\":[-47,30,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-30,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-31,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-32,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-33,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-39,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-40,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-41,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":89,\"full_literals\":[-42,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":90,\"full_literals\":[-43,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":92,\"full_literals\":[-44,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-45,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-22,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":62,\"full_literals\":[-23,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-24,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":64,\"full_literals\":[-25,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-26,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-34,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-35,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-36,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":81,\"full_literals\":[-37,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-38,53]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[4,31,33,37,39,40,41,62,64,65,69,70,79,81,82,86,87]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[8,30,44,46,49,50,51,61,63,65,73,75,78,80,82,90,92]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,38,48,54,56,58,59,68,70,72,75,76,85,87,89,92,93]}]}"
  "88 57 0 71 72 68 69 65 66 49 46 47 43 45 39 41 37 23 16 31 19 35 15 18 20 21 87 0\n89 -62 0 88 84 82 0\n90 56 47 0 88 68 69 70 48 49 47 64 26 28 24 38 0\n91 59 58 0 75 76 53 50 51 52 36 22 30 32 34 42 90 73 66 39 41 15 17 18 20 21 25 29 19 87 0\n92 47 60 0 77 59 61 63 14 78 58 56 54 44 45 9 33 8 11 13 12 35 10 86 0\n93 58 0 89 74 91 81 77 78 60 62 63 55 57 58 7 92 67 40 41 2 27 1 5 3 6 29 4 85 0\n94 -61 0 93 84 83 0\n95 -60 0 94 79 0\n96 -59 0 94 80 0\n97 47 0 95 92 0\n98 -50 0 96 76 0\n99 -42 0 98 50 0\n100 -43 0 98 51 0\n101 -44 0 98 52 0\n102 -30 0 99 30 0\n103 -31 0 100 32 0\n104 -32 0 101 34 0\n105 0 102 103 97 104 42 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b29c2f172b2a9a8e966a5936a394e3386e8789e0f9d15c4f1b24e9a66392e5c5594e5a55954d4b5a354d334ad1b61d2743db0d63c4e9354cd38cd331ce8b92d4b32e2b86c9b0ee8751cc749c6785c9783d0f23c4f07c6a458360ba91a24c91a515254352342d50c6384d130ce0b12c2b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6da6da6d36d24db6d249349349a4934924924d34d2492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 74), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 67), (facetIndex 90)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 60), (facetIndex 66), (facetIndex 68), (facetIndex 86)]))
 (.leaf ([(facetIndex 81), (facetIndex 82), (facetIndex 93)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 56), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 87), (facetIndex 91)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 53), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 83), (facetIndex 89)]))
 (.leaf ([(facetIndex 85), (facetIndex 92)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "385176528073305500000004421200000200040060000000000000040602z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped3_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8]
def grouped3_0016 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010" "{\"ridges\":[[6,522],[11,322],[18,193],[18,200],[19,648],[29,522],[34,198],[35,322],[39,530],[40,522],[41,193],[41,200],[42,322],[43,522],[44,522],[48,210],[49,322],[52,322],[53,706],[59,193],[60,332],[61,648],[66,228],[68,452],[71,656],[72,193],[72,200],[73,193],[73,200],[73,648],[74,240],[76,464],[81,198],[86,356],[89,706],[93,228]],\"owners\":[[6,522,[79,83,87,88,89],[29,39,40,43,44]],[29,522,[87,88,89],[6,39,40,43,44,79,83]],[40,522,[79,83,88,89],[6,29,39,43,44,87]],[43,522,[79,83,87,88],[6,29,39,40,44,89]],[44,522,[79,87],[6,29,39,40,43,83,88,89]],[39,530,[85],[9,31,47,50,51,79,87,88]],[11,322,[82,86,90],[35,42,49,52]],[35,322,[90],[11,42,49,52,82,86]],[42,322,[86,90],[11,35,49,52,82]],[49,322,[82,86],[11,35,42,52,90]],[52,322,[82],[11,35,42,49,86,90]],[18,193,[34,48,53,66,68,74,76],[41,59,72,73]],[41,193,[66,68,74,76],[18,34,48,53,59,72,73]],[59,193,[48,53,74,76],[18,34,41,66,68,72,73]],[72,193,[34,48,53,68,76],[18,41,59,66,73,74]],[73,193,[34,48,66,68,74,76],[18,41,53,59,72]],[18,200,[81,89,93],[41,59,72,73]],[41,200,[93],[18,59,72,73,81,89]],[72,200,[81,89],[18,41,59,73,93]],[73,200,[81,93],[18,41,59,72,89]],[19,648,[83,88,89,92],[44,61,71,73]],[61,648,[88,89],[19,44,71,73,83,92]],[73,648,[83,88,92],[19,44,61,71,89]],[71,656,[85],[20,50,65,88,92]],[34,198,[81],[]],[81,198,[34],[]],[48,210,[],[]],[53,706,[89],[]],[89,706,[53],[]],[60,332,[82],[]],[66,228,[93],[]],[93,228,[66],[]],[86,356,[67],[]],[68,452,[],[]],[74,240,[],[]],[76,464,[],[]]],\"edges\":[[29,[6,19,29,39,40,43,44,56,61,70,71,73,79,83,87,88,89,92]],[39,[18,34,41,48,53,59,66,68,72,73,74,76,81,89,93]],[40,[11,35,42,49,52,60,67,68,75,76,82,86,90]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,32,35,38,39,40],[-5,38,39,40],[-9,32,35,39,40],[-12,32,35,38,39],[-13,32,38],[-8,36],[-2,34,37,41],[-7,41],[-11,37,41],[-15,34,37],[-16,34],[-3,6,14,17,22,24,29,31],[-10,22,24,29,31],[-19,14,17,29,31],[-27,6,14,17,24,31],[-28,6,14,22,24,29,31],[-3,33,40,43],[-10,43],[-27,33,40],[-28,33,43],[-4,35,39,40,42],[-21,39,40],[-28,35,39,42],[-26,36],[-6,33],[-33,6],[-14],[-17,40],[-40,17],[-20,34],[-22,43],[-43,22],[-37,23],[-24],[-29],[-31],[-30,44],[-23,45],[-41,45],[-46,6,20,22,24,37],[-6,46],[-20,46],[-22,46],[-37,46],[-33,47],[-34,47],[-43,47],[-18,48],[-25,48],[-32,49],[-38,49],[-17,50],[-39,50],[-35,51],[-40,51],[-36,52],[-42,52],[-45,53],[-44,53],[-54,46,47],[-47,54],[-46,54],[-46,-47,55],[-54,56],[-55,57],[-53,56],[-53,-54,57],[-49,58],[-48,58],[-52,59],[-51,59],[-59,60],[-50,60],[-50,-59,61],[-60,62],[-61,63],[-58,62],[-56,-63,64],[-57,-62,64],[-64],[1,4,5,8,9,12,13,18,21,25,26,28,32,35,38,39,40,42],[3,6,10,14,17,19,22,24,27,28,29,31,33,40,43],[2,7,11,15,16,20,23,24,30,31,34,37,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[79,83,87,88,89]},{\"tag\":\"mate\",\"ridge\":522,\"a\":29,\"owners\":[87,88,89]},{\"tag\":\"mate\",\"ridge\":522,\"a\":40,\"owners\":[79,83,88,89]},{\"tag\":\"mate\",\"ridge\":522,\"a\":43,\"owners\":[79,83,87,88]},{\"tag\":\"mate\",\"ridge\":522,\"a\":44,\"owners\":[79,87]},{\"tag\":\"mate\",\"ridge\":530,\"a\":39,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":11,\"owners\":[82,86,90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":35,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":42,\"owners\":[86,90]},{\"tag\":\"mate\",\"ridge\":322,\"a\":49,\"owners\":[82,86]},{\"tag\":\"mate\",\"ridge\":322,\"a\":52,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":193,\"a\":18,\"owners\":[34,48,53,66,68,74,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":41,\"owners\":[66,68,74,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":59,\"owners\":[48,53,74,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":72,\"owners\":[34,48,53,68,76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":73,\"owners\":[34,48,66,68,74,76]},{\"tag\":\"mate\",\"ridge\":200,\"a\":18,\"owners\":[81,89,93]},{\"tag\":\"mate\",\"ridge\":200,\"a\":41,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":200,\"a\":72,\"owners\":[81,89]},{\"tag\":\"mate\",\"ridge\":200,\"a\":73,\"owners\":[81,93]},{\"tag\":\"mate\",\"ridge\":648,\"a\":19,\"owners\":[83,88,89,92]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[88,89]},{\"tag\":\"mate\",\"ridge\":648,\"a\":73,\"owners\":[83,88,92]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":198,\"a\":34,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":198,\"a\":81,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":210,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":53,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":706,\"a\":89,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":332,\"a\":60,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":228,\"a\":66,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":228,\"a\":93,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":356,\"a\":86,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":452,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":76,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":75,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-23,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":90,\"full_literals\":[-41,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[34,60,66,68,86],\"full_literals\":[-46,6,20,22,24,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-6,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":60,\"full_literals\":[-20,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-22,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":86,\"full_literals\":[-37,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":81,\"full_literals\":[-33,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-34,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":93,\"full_literals\":[-43,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":56,\"full_literals\":[-18,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-25,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-32,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-38,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-17,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-39,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-35,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":89,\"full_literals\":[-40,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-36,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":92,\"full_literals\":[-42,52]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-47,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-54,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-59,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-56,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,19,29,39,40,43,44,56,61,70,71,73,79,83,87,88,89,92]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[18,34,41,48,53,59,66,68,72,73,74,76,81,89,93]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,35,42,49,52,60,67,68,75,76,82,86,90]}]}"
  "84 -46 6 20 22 37 0 34 40 0\n85 3 6 10 17 19 22 27 28 33 40 43 0 27 34 35 36 82 0\n86 2 7 11 15 16 20 23 30 34 37 41 0 34 36 83 0\n87 56 0 64 66 61 62 58 59 46 42 44 38 39 37 7 10 11 8 9 86 0\n88 -63 0 87 80 78 0\n89 -61 0 88 76 0\n90 54 17 0 27 35 36 29 14 61 62 45 47 41 43 17 19 18 20 85 0\n91 47 37 -54 0 45 46 47 60 25 30 31 84 0\n92 17 57 0 36 35 34 27 65 14 29 90 67 58 38 33 91 63 41 43 26 15 13 32 16 12 85 0\n93 -17 0 89 28 52 55 74 71 0\n94 -40 0 93 29 0\n95 57 0 93 92 0\n96 -62 0 95 80 79 0\n97 -60 0 96 75 0\n98 -58 0 96 77 0\n99 -59 0 97 72 0\n100 -50 0 97 73 0\n101 -49 0 98 68 0\n102 -48 0 98 69 0\n103 -52 0 99 70 0\n104 -51 0 99 71 0\n105 -39 0 100 53 0\n106 -32 0 101 50 0\n107 -38 0 101 51 0\n108 -18 0 102 48 0\n109 -25 0 102 49 0\n110 -36 0 103 56 0\n111 -42 0 103 57 0\n112 -35 0 104 54 0\n113 -21 0 105 94 22 0\n114 -5 0 105 107 94 2 0\n115 -13 0 106 107 5 0\n116 -8 0 110 6 0\n117 -26 0 110 24 0\n118 -4 0 112 105 94 111 21 0\n119 -28 0 112 105 111 23 0\n120 -12 0 112 106 107 105 4 0\n121 -1 0 112 106 107 105 94 1 0\n122 -9 0 112 106 105 94 3 0\n123 0 112 113 114 116 122 120 115 121 108 118 117 109 106 119 107 105 94 111 81 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c5c96a4e8e6a59561da8e5386e8791e5c569c66394e6c539695556351d68d5362d1b51d70d6338e9354d331ce8b52d2b1ae1ba1d4729e1745c9715e0f43c8f13e1c0f11a0e8c6198360b81e865190e68531465854358342d0754330c6344c3342c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26d26d36926d2492692692493493492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 52)]))
 (.branch 2
 (.leaf ([(facetIndex 76), (facetIndex 79)]))
 (.leaf ([(facetIndex 59), (facetIndex 63)]))))
 (.branch 4
 (.leaf ([(facetIndex 70), (facetIndex 71)]))
 (.branch 5
 (.leaf ([(facetIndex 75), (facetIndex 78)]))
 (.leaf ([(facetIndex 82), (facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "b403018006c00004004z2c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012" "{\"ridges\":[[12,321],[20,641],[20,644],[42,321],[43,641],[47,321],[51,321],[54,321],[55,321],[59,332],[60,641],[60,644],[63,340],[64,641],[64,644],[66,641],[66,644],[70,360],[71,368],[75,332],[78,340],[82,360],[83,368]],\"owners\":[[12,321,[59,63,70,71],[42,47,51,54,55]],[42,321,[70,71],[12,47,51,54,55,59,63]],[47,321,[63,71],[12,42,51,54,55,59,70]],[51,321,[59,70],[12,42,47,54,55,63,71]],[54,321,[59,63],[12,42,47,51,55,70,71]],[55,321,[59,63,70,71],[12,42,47,51,54]],[20,641,[48,52],[43,60,64,66]],[43,641,[],[20,48,52,60,64,66]],[60,641,[52],[20,43,48,64,66]],[64,641,[48],[20,43,52,60,66]],[66,641,[48,52],[20,43,60,64]],[20,644,[76,79],[43,60,64,66]],[60,644,[79],[20,43,64,66,76]],[64,644,[76],[20,43,60,66,79]],[66,644,[76,79],[20,43,60,64]],[59,332,[75],[]],[75,332,[59],[]],[63,340,[78],[]],[78,340,[63],[]],[70,360,[82],[]],[82,360,[70],[]],[71,368,[83],[]],[83,368,[71],[]]],\"edges\":[[40,[12,42,47,51,54,55,59,63,70,71,75,78,82,83]],[43,[20,43,48,52,60,64,66,76,79]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,11,13,16,17],[-3,16,17],[-5,13,17],[-7,11,16],[-9,11,13],[-10,11,13,16,17],[-2,6,8],[-4],[-12,8],[-14,6],[-15,6,8],[-2,19,21],[-12,21],[-14,19],[-15,19,21],[-11,18],[-18,11],[-13,20],[-20,13],[-16,22],[-22,16],[-17,23],[-23,17],[-6,24],[-8,24],[-19,25],[-21,25],[-26,11,13],[-11,26],[-13,26],[-27,16,17],[-16,27],[-17,27],[-18,28],[-20,28],[-22,29],[-23,29],[-26,30],[-25,30],[-25,-26,31],[-30,32],[-31,33],[-24,32],[-24,-30,33],[-29,34],[-28,34],[-34,35],[-27,-34,36],[-32,-36,37],[-33,-35,37],[-37],[1,3,5,7,9,10,11,13,16,17,18,20,22,23],[2,4,6,8,12,14,15,19,21]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":12,\"owners\":[59,63,70,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":42,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":47,\"owners\":[63,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":51,\"owners\":[59,70]},{\"tag\":\"mate\",\"ridge\":321,\"a\":54,\"owners\":[59,63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":55,\"owners\":[59,63,70,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":20,\"owners\":[48,52]},{\"tag\":\"mate\",\"ridge\":641,\"a\":43,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":60,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[48,52]},{\"tag\":\"mate\",\"ridge\":644,\"a\":20,\"owners\":[76,79]},{\"tag\":\"mate\",\"ridge\":644,\"a\":60,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":644,\"a\":64,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":644,\"a\":66,\"owners\":[76,79]},{\"tag\":\"mate\",\"ridge\":332,\"a\":59,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":332,\"a\":75,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":340,\"a\":63,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":340,\"a\":78,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":360,\"a\":70,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":360,\"a\":82,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":368,\"a\":71,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":368,\"a\":83,\"owners\":[71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-6,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-8,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":76,\"full_literals\":[-19,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-21,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[59,63],\"full_literals\":[-26,11,13]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-11,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-13,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[70,71],\"full_literals\":[-27,16,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-16,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-17,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-18,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-22,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-23,29]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-30,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-32,-36,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-33,-35,37],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,42,47,51,54,55,59,63,70,71,75,78,82,83]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,43,48,52,60,64,66,76,79]}]}"
  "54 2 6 8 12 14 15 19 21 0 8 53 0\n55 32 0 41 43 39 24 25 26 27 10 9 7 11 54 0\n56 -36 0 55 51 49 0\n57 26 27 0 33 23 32 21 2 29 30 1 4 5 6 17 3 19 52 0\n58 -26 33 0 42 38 40 44 26 27 24 25 14 13 12 15 54 0\n59 -27 0 56 48 45 36 37 20 22 31 0\n60 26 0 59 57 0\n61 33 0 60 58 0\n62 -35 0 61 51 50 0\n63 -34 0 62 47 0\n64 -28 0 63 46 0\n65 -18 0 64 34 0\n66 -20 0 64 35 0\n67 -11 0 65 16 0\n68 -13 0 66 18 0\n69 0 67 68 60 28 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record012
