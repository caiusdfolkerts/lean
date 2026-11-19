module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00088Data
public import GraphInputsRow24Part00088Frames
public import GraphInputsRow24Part00088Leaves
public import GraphInputsRow24Part00088Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
#print axioms local_excluded
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
#print axioms local_excluded
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
#print axioms local_excluded
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
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record008
