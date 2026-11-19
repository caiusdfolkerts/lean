module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00010Data
public import GraphInputsRow30Part00010Frames
public import GraphInputsRow30Part00010Leaves
public import GraphInputsRow30Part00010Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00010.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017
def vertexColumn : Fields := ⟨10, hexnat% "3c4d52d4e31cccb2acc729c570dc8f3c2d4ad2e29cacaaaac6a9a568da8eb86d1ac671b26a9b16a5a56558d68d876c3a8e6394e33a2e4b8ae8791e2785e0f9c9564d9e15c5c96a5c5695554d58d4756354d3352d2b51d2745de0dc3c8ea3c4e9354cd38cc7362d4b32d2b2ad1b26c5bc1e8761d4731e2749ca719e1745c9715c3743c8f13c2f07e340f2320e839514c5154354348d0b41d50cc314c3342c8b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d36db6db6d36db6db6d36db6db6db4db69b6d249249249a6db4924924926da4db6db492691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨93, by decide⟩, ⟨105, by decide⟩, ⟨117, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000800e7c039f180f600000", hexnat% "200200000000000000000000000000", 75540846874722304, hexnat% "4318000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200200200080037800de180f600000", hexnat% "80002000000000000", 75471577642172416, hexnat% "4308400000000000000", hexnat% "40001000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20020020008002f800be180f600000", hexnat% "80002000000000000", 75506762014261248, hexnat% "4310400000000000000", hexnat% "40001000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2002002000800278009e180f600000", hexnat% "80002000000000000", 75717868246794240, hexnat% "4340400000000000000", hexnat% "18000600000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "437fd0080180b600000", hexnat% "200000200080080000000004000000", hexnat% "200000000000003000000000000", 139637976727552, 3377699720527872]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "437fc0804180b600000", hexnat% "200000200080080000000004000000", hexnat% "200000000000003000000000000", 275977418571776, 73183493944770560]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2002002000842c010f07000f600000", 272678883688448, hexnat% "100000001800000000", hexnat% "3fc00000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200200084200003000007600000", hexnat% "2000000000000c0000000000000000", 280375465082880, hexnat% "3fc00000000000000", 75435396971888640, hexnat% "100000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00010.record017
