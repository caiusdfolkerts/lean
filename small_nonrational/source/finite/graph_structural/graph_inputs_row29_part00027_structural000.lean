module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00027Data
public import GraphInputsRow29Part00027Frames
public import GraphInputsRow29Part00027Leaves
public import GraphInputsRow29Part00027Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00027.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003
def vertexColumn : Fields := ⟨10, hexnat% "3c2a695aa9966a394e8b92e2785e0fbc1a6559a9565a354d8b52d2745d0f783d0ec370ea358e9354e8b52e1b46c9b16c3ba1d4789d2729c670de0f43c8f13f283532234b0a8a92a318961582e07b21347098a529314951542d07703a0d4330e2348c9314e0b42c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d24936db6d2492492492492492492492449249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2202375febf8000000000", hexnat% "c0000000000000000", hexnat% "c0000000000000000000", hexnat% "100100001400000000000", 9943947977234055168]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6007aaefff8000000000", hexnat% "300000000000000000", hexnat% "300000000000000000000", hexnat% "80080110000000000000", 6052837899185946624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e033fba54f8000000000", hexnat% "c0000000000000000", 756463999909888, 313000174102249472]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3203ffba54f8000000000", hexnat% "c0000000000000000000", 756463999909888, 313000174102249472]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12013fba5468000000000", hexnat% "40040008080000000000", 757563511537664, 310748374288564224, hexnat% "80080000000000000000", hexnat% "200200000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e00ff7172f8000000000", hexnat% "300000000000000000", 576689450722000896, 65302194596872192]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e03ff7172f8000000000", hexnat% "300000000000000000000", 576689450722000896, 65302194596872192]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a00bf7132d8000000000", hexnat% "200200004800000000000", 576550912256901120, 65302194596872192, hexnat% "40040000000000000000", hexnat% "100100000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10011ffff7f8000000000", hexnat% "e0000000000000000", hexnat% "e0000000000000000000", hexnat% "200200000800000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffff78000000000", hexnat% "320000000000000000", hexnat% "320000000000000000000", hexnat% "c0000080000000000", hexnat% "c0000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff078000000000", hexnat% "e0000080000000000", hexnat% "100100000400000000000", hexnat% "e0000000000000000000", hexnat% "200200000800000000000", 52776558133248]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4005feffff8000000000", hexnat% "80080100000000000000", hexnat% "320000000000000000", hexnat% "320000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [18351042031872114688, hexnat% "40040000000000000000", hexnat% "320004000000000000", hexnat% "320000000000000000000", hexnat% "10140000000000000", hexnat% "80080010000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4004c0a8248000000000", hexnat% "200200002800000000000", 3026718016755728384, hexnat% "11540000000000000", hexnat% "80080010090000000000", hexnat% "100100004420000000000", hexnat% "20020000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c23 c6
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c24 c1
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00027.record003
