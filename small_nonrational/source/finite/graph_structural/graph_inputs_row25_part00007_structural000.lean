module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00007Data
public import GraphInputsRow25Part00007Frames
public import GraphInputsRow25Part00007Leaves
public import GraphInputsRow25Part00007Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064
def vertexColumn : Fields := ⟨10, hexnat% "3b0e6364cd1b49b31c6725ce8b92ccab26caaa9a8eaa6a5ac99a699b1665a568d9362da4e8b8ae1ba1e2785ed87316c6693a7196665969565655352d58d2b46d4749d1772368e6338f1364e538cd332ce4b32e2b2ac6b86c5b61d2729d1725c570dc8f0be6292a1a268661381e6859126525195151341d28c6324c8b12c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6d349b4db6da6d249b4db4d249b6924d24d36d24d249a492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40024034680015fe000000", hexnat% "8001800000000800000000", hexnat% "20000000001010000000000", 9804371573157658624, hexnat% "810000000000000000000", 143623706378240, hexnat% "80002000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c001c0281803bcbe000000", 9232379236109516800, 1170935907411296256, hexnat% "800000001800000000000", hexnat% "80002200000000000", 288230377225453568, hexnat% "20012000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20802000043a2b4b6000000", 1441151885187743744, hexnat% "88800000000000000", hexnat% "4010400000010000000000", 15762599769538560, hexnat% "8001800000000800000000", 2305843009213693952]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88b813a231be000000", 20266198323167232, 297237576480194560, 1700807049216, hexnat% "20812000000000000000000", hexnat% "c001400000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81422a221fe000000", 9804336388785569792, 20266198323167232, hexnat% "802000000000000000", hexnat% "10000000019400000000", hexnat% "20802000001000000000000", hexnat% "c001400000000800000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2481200344101319e000000", 143486267424768, hexnat% "400008000400000000", hexnat% "8001800000000800000000", hexnat% "80002200000000000", 9813343588577181696, 1073741824]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2081240344101319e000000", 143486267424768, hexnat% "4000000008000400000000", hexnat% "8001800000000800000000", hexnat% "80002200000000000", 9813343588577181696, 1073741824]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2080200000180309c000000", 1170935907444850688, hexnat% "c001c00000000c00000000", hexnat% "80002220000000000", 9813343588577181696, hexnat% "10000000018000000000", 2251800887427072, 2594073385365405696]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record064_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record070
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070
def vertexColumn : Fields := ⟨10, hexnat% "3a89e1b49d26c9723c1f3a2d4b326cb8acaaaa6aa5a8e9a665a568d9362da4e33a2e2ba1e1783ed47316c671ca5a99a6598e479695954d4b51d4cd1b45d0f743c8da3c4d9394d538cd332cf0b62e4b32e2b4acab86c5b0ed8731d2729d1725c370bc1fcc0acc4a52928562384e685312a4a5154352344d0b58344c5322c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db49b6da6da6da4d34da4da6db4d24924da49269b49369a693492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨88, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c1118880119f4c1664000000", hexnat% "1002000000000000000", 288232850187091968, 720575940379279360, hexnat% "108000000080000000", hexnat% "20000000000010000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81118800018f041204000000", 432345564361785344, 11287174053888, hexnat% "1802000400000000000", 576460754182471680, hexnat% "109000000080000000", hexnat% "400020000010000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88001f800a16fc000000", hexnat% "10100000000040000000000", hexnat% "400020000010404000000000", hexnat% "908000000000000000", hexnat% "801000000003000000000000", 3377699720527872, hexnat% "1002000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400028003f914042fc000000", hexnat% "908000000000000000", 1134713179734016, hexnat% "100000a040000000000", hexnat% "180000000020000000000", hexnat% "811000000000000000000000", 68719476736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "980a80f401674000000", hexnat% "811000000000000000000000", hexnat% "180000000060000000000", hexnat% "100010084080000000", 540431955418677248, 1152921504606846976, hexnat% "400020000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "188000f800e565c000000", hexnat% "400020000010400080000000", hexnat% "811000000002000000000000", hexnat% "909000000000000000", 1407375420424192, hexnat% "1000008000000000000", 2305843009213693952]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "890ba940a46f8000000", 360287970256748544, hexnat% "100000a040000000000", hexnat% "180000000000000000000", hexnat% "400020000000400000000000", hexnat% "801000000001000000000000", hexnat% "10000000000001000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c111a900159a4652dc000000", 1407375420424192, 720575940379279360, hexnat% "100000080000000000", 11529215063248338944, hexnat% "800000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c100a9003f984242fc000000", 1134713179734016, hexnat% "908000000000000000", 567416719409152, hexnat% "1000000001000000000000", hexnat% "100000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c100291018184a42d8000000", 567416719409152, 540431955351568384, hexnat% "80a000000000000000", hexnat% "180000000000000000000", hexnat% "1000000001000000000000", 1125917623582720]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c11108001b82061254000000", hexnat% "a0000400000008000000", 3729543441416192, hexnat% "1802000000000000000", hexnat% "100010084080000000", 9223372054034644992, 536870912]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41002990301d4a42d8000000", hexnat% "801000000002000000000000", 9223372054034644992, 576460752907403264, hexnat% "180000000040000000000", 540431955284459520, 68719476736]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "411108001000421250000000", hexnat% "80000000000b000000000000", hexnat% "1000000040000000000", 828662331503280128, hexnat% "80a000000000000000", hexnat% "100010084080000000", hexnat% "a0000400000008000000", 1125917623582720]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c23 c2
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00007.record070_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00007.record070
