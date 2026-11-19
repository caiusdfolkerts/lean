module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00001Data
public import GraphInputsRow26Part00001Frames
public import GraphInputsRow26Part00001Leaves
public import GraphInputsRow26Part00001Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016
def vertexColumn : Fields := ⟨10, hexnat% "3c2acb4acaa6a66ac671aa6998b66394e1b89e17bc1ac749ca669666c5716a5994b56354d1b49d17783d0ec370f23a8e63a4d938ccb3c2d8b92d4b8ad2b1ad1b26c5b0ee8761e4751cc789ca719c9715c3743c8f13c2f07c3ce0b425283a258361382e07b81d05490e4950d44d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "269b6db69a49269b6db69a4924db6db6db69b6db4db6db69a6d2449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfaabfeffffffffff80000", hexnat% "10001000000000000000", hexnat% "10001000000000000000000", hexnat% "44000000000000000000", hexnat% "4000400000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1fffffffffcfffafff80000", 844429225099264, 17179869184]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffeffffefffff7fff80000", hexnat% "10000000000000000000", 72057628397666304]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffeffffefffff7ffd80000", hexnat% "10000000000000200000", hexnat% "10000000100000000000000", 34359738368]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfeeffe67ffbf7ffd80000", 1729382256912367616, hexnat% "10001000180000000000000", 4432406249472, hexnat% "4010000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c2 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff6fffffffffffff80000", hexnat% "8000000000000000000", hexnat% "10001000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bff4fffffffffffff80000", hexnat% "10001000000000000000000", hexnat% "a000000000000000000", hexnat% "4000000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bfa5ffb1fffffffff80000", hexnat% "40004000000000000000", hexnat% "14000000000000000000000", 1008806316530991104, hexnat% "1a000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bffebfba7ffbfffaf80000", 4899916394662985728, hexnat% "10001000180000000000000", hexnat% "4000400000040000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bfa7bfa1fffbfffad00000", hexnat% "18000000000000200000", hexnat% "40004000000005080000", hexnat% "4000400000040000000000", 1008806316530991104, 1152921504606846976]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c23 c10
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c24 c0
  c25
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00001.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00001.record016
