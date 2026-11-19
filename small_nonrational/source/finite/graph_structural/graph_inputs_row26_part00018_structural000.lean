module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00018Data
public import GraphInputsRow26Part00018Frames
public import GraphInputsRow26Part00018Leaves
public import GraphInputsRow26Part00018Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031
def vertexColumn : Fields := ⟨10, hexnat% "7cd49b2e2b4a72a5a8e87a71996558b61d8ce1ba1e1783ed45b1e2749726598e47971595554b51d4cd1b61d1743de0f4370da3c4d9394d538cd332cc73c2e8b62e4b52ccb8acab1ae1b16c3b61d4731ca719e1745c9715c3783c8f13c2f07cacc49522a8a6158362384e0bb11544a9294550d48d1342d"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36db6db4924d24db6db6d249349b6d369b6db6db69b6db69b6d2692649249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨30, by decide⟩, ⟨38, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7b000ec00000000700000", hexnat% "10000000041000000", hexnat% "200008000024000000000000", hexnat% "800020000000002000000", 274877906944]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6b001ec00000041100000", hexnat% "100000000000000600000", hexnat% "8020004000000000000", hexnat% "200800000000000000000000", 9007474166202368]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eb001a424004043700000", hexnat% "100004000000000000000", hexnat% "200008000000000000000000", hexnat% "20800000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bb0006c24004043700000", hexnat% "400010000000000000000", hexnat% "200008000000000000000000", hexnat% "28000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3a003ec24004043700000", hexnat% "200008000000000000000000", hexnat% "410000000000000000000", hexnat% "800000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7b000ec24004043700000", hexnat% "10000000000000000", hexnat% "8020000000000000000", hexnat% "200800000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3b000c424004043700000", hexnat% "400010000000000000000", hexnat% "200008000000000000000000", hexnat% "800020000000000000000", 2882303761517117440]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200088000424004000000000", hexnat% "100004000000000700000", hexnat% "400010000000041000000", hexnat% "800020000000002000000", 12105675798371893248, hexnat% "230000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record044
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044
def vertexColumn : Fields := ⟨10, hexnat% "ec1e8cd0ecc70dc78b326c9ca6a96a3a99a36b26c5a364d92e1b91e17ba1e4731ac5b16a4e9c659936665394d58d4b5334ad1b61d2745dc8da338f1364cd38cd332cd8b32d2b2ac6b46c9b16e2785c570dc2f6611a1984e078e132499894658544d0746312c1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6da6db6d24db6da6924d34d249b4db6db4da492492249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffefefeb7777f73f00000", hexnat% "101000000000c000000", 72198333673766912, 18023194602504192, 2252349569499136]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffcfee5ff7feed00000", hexnat% "10000000000000000", hexnat% "20100000010000000", 5066549599666176, 2252349569499136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffefdfeeddf7f6ec00000", 5066549599666176, hexnat% "1000000008080000000", hexnat% "20100200010100000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffdffdf7ffffff00000", hexnat% "20000000000000000", 9147936743096320]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffd7f9f7ffff5f00000", hexnat% "28000000000000000", 9147936776650752, 18014398643699712]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffc7fbdeffff7400000", 18014398643699712, hexnat% "28000000000100000", 580542149951488, hexnat% "10000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffefc7e875fff60e00000", hexnat% "100004000000c000000", hexnat% "18000000002000000", hexnat% "20100200010100000", 6755399457832960, 9147938890579968]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00018.record044_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00018.record044
