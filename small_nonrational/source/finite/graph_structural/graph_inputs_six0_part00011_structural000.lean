module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsSix0Part00011Data
public import GraphInputsSix0Part00011Frames
public import GraphInputsSix0Part00011Leaves
public import GraphInputsSix0Part00011Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00011.record046
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046
def vertexColumn : Fields := ⟨10, hexnat% "363b4e6795de374db96cd735ad573cce736c6f17fc8d32cccb29cf0b8acaa9a4e8bad1ac6c9966a58d6c3a8e8b92e8789e0fbc1e2749b25c94e4b9d16c5594d5c368d9354d3352d27783d0ec370d6334d332cf0ba2d8b4acab46c9b0ef07a1e4751cc749c6725c5783d0f23c2f07c3cd0ac2918364a4990e4350b41d50cc348c930cc4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1249249249248db6d36db49b6db6db4db6d26db6db6934924936d36936924926da449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7cff9ffddffffffff", hexnat% "80000002200000000", 3459327463773962240, 1125899906842624]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7cff9fff9ffffffff", hexnat% "80000000600000000", 3459327463773962240, 1125899906842624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffdf3fffffffb5ffbcffffff", 10995166609408, hexnat% "20c0000000400040000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffdf3fffffff6bffb3ffffff", 21990433882112, hexnat% "20c0000000800040000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7cff9fff9ffe7ffff", 2306968917711519744, hexnat% "80000000400080000", 1153484454560268288]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffff3fffffff27ff80ffffff", 8796411789312, 17592924241920, hexnat% "c0000000c00040000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7cff9ffddffe7ffff", 1153484463150727168, hexnat% "80000002000100000", 2306968909120536576]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7dff9fff9fde7ffff", 2306968917711519744, hexnat% "80000000400080000", 562949986975744]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7eff9ffddf7e7ffff", 1153484463150727168, hexnat% "80000002000100000", 1125900041060352]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffff3ffffff93fff8fffffff", hexnat% "40000002000010000000", hexnat% "80000004000020000000", 211107306274816]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffdf3ff7fffdbffbbff7ffff", hexnat% "80000000400080000", hexnat% "20c0000000400040000000", 562949953421312]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7effdffd9ffffffff", hexnat% "80000002600000000", 1153484454560268288]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffdf3ff7fffb7fdfbfefffff", hexnat% "80000002000100000", hexnat% "20c0000000800040000000", 1125899906842624]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffff7dffbffd9ffffffff", hexnat% "80000002600000000", 2306968909120536576]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffdf3fffeffd3fffffffffff", 1153484454560268288, hexnat% "20c0000000c00000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffffdf3fffdffb3fffffffffff", 2306968909120536576, hexnat% "20c0000000c00000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .size 4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c24 c7
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c26 c5
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c27 c4
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c28 c3
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c29 c2
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c30 c1
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c31 c0
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00011.record046
