module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00080Data
public import GraphInputsRow29Part00080Frames
public import GraphInputsRow29Part00080Leaves
public import GraphInputsRow29Part00080Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000
def vertexColumn : Fields := ⟨10, hexnat% "e331c6715c3713c2f07ce299a568da4e8ba1eb8665956359362d876c3a8e63a4e538ce8b92e2b86e4789e1783ee2719664d92e785c5595354b5c368d6364d3362d2b46d8751d2745d0f78364cd32cc73c2e8b62e4b32e2b2ad1b26c5b0ef07a1d8791cc789ca745c9715c3783d0f23c4f0bc1f6607865074c298a1ab06618661c469264590e465254550d46382c8b12c2b81c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36da49b6d24db6934db6da6db6d24da49b6db69b4936da49249349249249a493493249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨88, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨117, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "21810281000004e07e8fd2e0000000", hexnat% "210000080100000000000", hexnat% "c000000000c00000000", hexnat% "180000000600000000000", hexnat% "4284000000000100000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "428400019c04c15ee01cc0000000", hexnat% "8100000000000000080000000000", hexnat% "2000000a0140000000000", 4132295409664, hexnat% "210002810000002000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "428400019c04a15ee01ca0000000", hexnat% "8100000000000000080000000000", hexnat% "2000000a0140000000000", 4132832280576, hexnat% "210002810000004000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8100000000000040680080000000", hexnat% "380008000800000000000", 53480245575024640, hexnat% "1c000000001000000000", hexnat% "4284000000000100000c00000000", 26113401159680, hexnat% "210002810000046000000260000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004
def vertexColumn : Fields := ⟨10, hexnat% "2e8d62d8b9334ad2ccab26c3b29cd8b52ccb4a9a8eac6a5a568dac9a6639b168d9362da4e33a2e2b86e8789ed85e1d45d1cc5b1d26693a7199655936725994e5c56354d4b5934cd8b4ad1b61d38d5334d332cd4b32cab1ad1b26c5b31d2729c6745c970dc8f13c2fd821c2716207961384c9264a52548d0754348c6344c4b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6936db6db6db6db6db4926db6d36d369b69a69a49a693492692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000c00205582327c00000", hexnat% "200000300000000000000000", 2323857407723175936, 5514872225792, 35701915648, 274877906944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1022014c6b51c00000", hexnat% "200000200000000000000000", 19140298953195520, hexnat% "400000c00000100000000000", 1116859269120, 67108864]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000c00201182f2d800000", hexnat% "200000300000000000000000", 5772436045824, 19210667160502272, 2305843009217888256, 1375731712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100045494a77c00000", hexnat% "200000200000000000000000", 2449958334728503296, hexnat% "400000c00000100000000000", 4419655565312]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000c00004582e3f400000", 5498631880704, hexnat% "200000300000000000000000", 279181262848, 2324138882699886592, 144115188075855872]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000f02040086a75000000", hexnat% "400000000000100000000000", 1477743627730944, 144119590417334272, 46137344, 1116825714688]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000300000080a15000000", hexnat% "400000c00000100000000000", 5498766098432, 296361132032, 19492142137212928, 2449958334728503296, 574619648]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009
def vertexColumn : Fields := ⟨10, hexnat% "370ba3589e2e4d5274b325c78b323ab1a8e8ba39b168d8b633a1e27b6178751cc6715c7499a4e9c6659566392e479d166539715955558d4b51d64d8749d175c368d6338cb352ccb2ac6b46c9b0ed4731ca719d1725c3713f60cc24c3321c4c88e0796138531324c52344d0752328d130cc8b06c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db49a6db6db4924d34da6db6db4db6da49349269349349a491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401009a800000f4082000000", hexnat% "10080000000000000", hexnat% "c000000001200000000000", 60599304192, 138512695296, hexnat% "6000000c00000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00e000001e6448a000000", 1142796845056, hexnat% "810080000000000000", hexnat% "400001280000000000000000", hexnat% "1000000000000000000000", 8934605717504]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5006010000ef6ede000000", hexnat% "800080000000000000", hexnat% "8008000001000000000000", hexnat% "400001280000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40100000f6ede000000", hexnat% "800080000000000000", hexnat% "a000000400000000000", hexnat% "401000280000000000000000", hexnat% "c000000001200000000000", hexnat% "1000000800000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88900804e64c2000000", hexnat% "c000000001200000000000", hexnat% "6000000800000000000", hexnat% "401000200000000000000000", 1142931062784, hexnat% "1000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40d004280001e46002000000", hexnat% "1800000000000000000", hexnat% "a000000000000000000", hexnat% "10080020080000000", 1160110931968, 8797166764032]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e880001ef6ede000000", hexnat% "10080000000000000", hexnat% "c000000000000000000000", hexnat% "400001200000000000000000", hexnat% "1000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00e000001ed648a000000", 43285217280, 36030997115961344, hexnat% "401000280000000000000000", hexnat% "810000000000000000", hexnat% "1000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c00f200081ef64ce000000", 43218108416, hexnat% "810000000000000000", hexnat% "401000080000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40c00e080081ef64ce000000", hexnat% "1000200000000000000000", 43218108416, hexnat% "810000000000000000", hexnat% "1000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000000080ef6ede000000", hexnat% "810000000000000000", hexnat% "6000000000000000000", hexnat% "8008000001000000000000", hexnat% "401000280000000000000000", hexnat% "1000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40d004280001e46042000000", hexnat% "1800000000000000000", hexnat% "a000000000000000000", hexnat% "10080020080000000", 9904261693440, 51942260736]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c008000001646042000000", hexnat% "1004000000000000000000", hexnat% "400001280000000000000000", hexnat% "10080020080000000", hexnat% "2000000800000000000", 1160110931968, hexnat% "800000080000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010
def vertexColumn : Fields := ⟨10, hexnat% "bc2e8b61e43d0ec37362d4a723cb4a9a8ea968da598e6558d62d876538ce2b86e2785ed86e178751b46b19c4f1d26c9aa6693a699964d9c95a5c56352d70d8b4ad87743c8e6358ce3c4e5354cd38ccb31cf0b92d4b32e2b2ac6b86c9b16ca745c970dd0f23c2fd82583609c5885a4981ec861926525294952341d48c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36d26db6d24db6db6d24db6db6db69249b4da4d34db6db6db6db492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220300300070080000f4800000", 188743680, 328762772798046208, hexnat% "1008000000002800000000000", hexnat% "8000800000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101002800780a8000e4800000", hexnat% "22020010000000000000000000", 457179136, 328762772798046208, hexnat% "8000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2303001000700a0000e0000000", hexnat% "8000000000800000000000", hexnat% "8000800000000000000", hexnat% "20000000000014800000", 188743680, 328762772798046208]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22030030007008000074800000", 188743680, 328762772798046208, hexnat% "1008000000002800000000000", 2147483648, hexnat% "8000800000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30020000c0a000000000000", hexnat% "1008000000000800000000000", 532676608, 40532396646334464, hexnat% "22000010000000000000000000", 8070450536006025216, hexnat% "8000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011
def vertexColumn : Fields := ⟨10, hexnat% "bc1e8d6364d5274d316cc725c572723c96a3aa6659a568d8b61d94e4b8ae1b89e17b61b85e1d46d1ac6713c749725a95a4e9c6659564d9c56352d70d4b4ad8751d2766358ce394cd38ccb31cd4b32d2b2ac6b16e2749ca785c970dd0f23c2fd80d8c90e2348ca2685a07b2126705895258550d074a324c8b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6da6db6db4d36db6db6926db6db6db6da49a4d24da69a6d34d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a00000005b9528df000000", 36028801850802176, hexnat% "1000001000000000000000000", hexnat% "4000100000200000000", hexnat% "2000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000000cb95297f000000", 4503601774854144, hexnat% "1000001000000000000000000", hexnat% "4000100000200000000", hexnat% "2000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000000db1529ff000000", hexnat% "2000000000000000000000", hexnat% "1000001000000000000000000", hexnat% "4000100800200000000", hexnat% "2000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a0000000c815287f000000", hexnat% "1000001000000000000000000", 6442450944, 5348024557502464, hexnat% "6000000000200000000", 72198331526283264]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c0
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002007000109852bff000000", hexnat% "8000000000100000000000", 59109745109237760]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000007000100852253000000", hexnat% "2000000000100800000000", hexnat% "8000000040000008000000", 6755401655648256, 36028801850802176, 844424930131968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002006000099010985000000", 18577349133991936, 140738864087040, hexnat% "8000000000142000000000", hexnat% "1000100000200000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000db8101bd000000", hexnat% "1000002000000000000000000", 35467034624, hexnat% "a000000000142000000000", hexnat% "1000100000200000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80040000db0101ff000000", hexnat% "1000002000000000000000000", 72198340116217856, hexnat% "2000000000142800000000", hexnat% "1000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000006000008010028000000", 54043199823413248, hexnat% "a000000000142000000000", 4503601841963008, hexnat% "1000100000200000000", 985162418487296, 35752247296]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c6
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00080.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00080.record011
