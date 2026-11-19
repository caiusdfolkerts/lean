module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00120Data
public import GraphInputsRow24Part00120Frames
public import GraphInputsRow24Part00120Leaves
public import GraphInputsRow24Part00120Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00120.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 9007199254740992]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 585467951558164480, (certNat% 10)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 864691132750102528, (certNat% 13), (certNat% 14), 4398583382016]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), 576460754585124864, (certNat% 20), (certNat% 21)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 19), (certNat% 23), 578712554264592384, (certNat% 24), (certNat% 5)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 586593851465007104, (certNat% 27), 422212465065984, 288230376151711744]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 576460754450907136, 1374389534720, (certNat% 29), (certNat% 30)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 2305844658514690048, 588845651278692352, (certNat% 12), 703687441776640]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 26), 2305844658514690048, (certNat% 34), 985162418487296, (certNat% 35)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), 2305844108758876160, (certNat% 38), 9992361673228288, (certNat% 39)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 2305844658514690048, (certNat% 34), (certNat% 41), (certNat% 35), (certNat% 5), 9992361673228288]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00120.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00120.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005
def vertexColumn : Fields := ⟨10, (certNat% 42)⟩
def kindColumn : Fields := ⟨3, (certNat% 43)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1152993523692208128, (certNat% 44), (certNat% 45), (certNat% 46), (certNat% 47), 6871947673600, 79993765888]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00120.record005
