module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00044Data
public import GraphInputsRow26Part00044Frames
public import GraphInputsRow26Part00044Leaves
public import GraphInputsRow26Part00044Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record057
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057
def vertexColumn : Fields := ⟨10, hexnat% "1d8ce2d4cd32cc723c4f2aaa695a36a3a4e966a595635a364da2e4ba1e4783eb45d172729aa719a6599564d9b172559715a5655554d5c362d4b61d476a358e9354cd3a2d4b32e2b4acab86d1b26c5ba1d4731e2749c6785d1725c5783d0f0bc1fa61543489a15a898a52951625494c322c2b11c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db4d36da4db6db6da4d36da4db4da4db6da4d249b4da4926da6d3249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5e7ff5ffffe5f77ef0000", 11529215595824283648, hexnat% "18000000000000100000", hexnat% "a00000000000080000000", 1237084798976]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5f7ffffffff5bffff0000", 704374636544, hexnat% "208000000000000000000", hexnat% "800000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "15fe7bffffffffffffff0000", hexnat% "20084000000000000000000", hexnat% "80100000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5efffffffff7b7fff0000", hexnat% "10000000000000000000", 569083166720, hexnat% "a00000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5e7ffdffffe5b7fef0000", 706522120192, hexnat% "18000000000000100000", hexnat% "800002000000000000000", hexnat% "200000000010000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffde7ffdff7fedf67ef0000", hexnat% "200000000012080000000", 403701760, 2308094809027379200, hexnat% "18000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffeffe7e7f7fe7ecff0000", hexnat% "18000001800000000", hexnat% "10000000000012000000", 108086391073669120, 140737488355328]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5f7ff5ffffe4bffff0000", hexnat% "208000000010000000000", 704374636544, hexnat% "800002000000000000000", 9223372105574252544]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff7fffe7e7f7f6bfeff0000", hexnat% "800000000009000000000", 108086391073669120, hexnat% "18000000400000000", 140737488355328]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffde7ffffffffdbffff0000", 154618822656, hexnat% "18000000000000000000", hexnat% "200000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "15ff7dffffffffffffff0000", hexnat% "20002000000000000000000", hexnat% "80080000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c3 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c3 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff7fffffff7ff5bffff0000", 2251799813685248, hexnat% "800000000008000000000", 154618822656]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5efff7ff7ff5bffff0000", hexnat% "10000008000000000000", 9223372603790458880, hexnat% "a00000000000000000000", 137438953472]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5fffe5e7fff4bffff0000", 108086391056891904, hexnat% "200000000002000000000", hexnat% "800002000008000000000", hexnat% "18000001400000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff7fffe77ffdff4ef0000", 137573171200, 2251799814733824, 108086391107223552, hexnat% "8000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffff7ffde77fffff4ef0000", 2308094809028427776, 108086391107223552, hexnat% "8000000000008000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5fffeffffff53ffff0000", hexnat% "a00000000000000000000", hexnat% "10000000c00000000", 687194767360]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ff5f7fefe7fff53f4ff0000", hexnat% "8000000000008000000", hexnat% "10000000c00000000", hexnat% "a00000000000000000000", 108086391107223552, 687194767360]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c29 c24
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c32 c13
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c33 c12
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c34 c11
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c35 c10
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c36 c9
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c37 c0
  c38
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00044.record057_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00044.record057
