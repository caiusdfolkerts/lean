module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00159Data
public import GraphInputsRow24Part00159Frames
public import GraphInputsRow24Part00159Leaves
public import GraphInputsRow24Part00159Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001
def vertexColumn : Fields := ⟨10, hexnat% "a725c3723c4f0bc1f29a968da8e8ba1ea96958d68d8b61db0ea398e9394e33a2e4b8ae1ba1e2785e0fa59365392e479954d54d4b51d58d9354d3352d2b46d8751d2745d0f65334cb31cd8b92d4b32cab1ae1b26c5b0ed8791d4731ca719e1725c570de0f43c8f13c2f07e589524a4aa4649929264590e525254550d52342c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db4db6d36db6d36d36db6924924936da6db4936da4924d2492493493492649249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨93, by decide⟩, ⟨99, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7de00e0238820000000", hexnat% "200000200000002040000000", hexnat% "40000220000100000000f000000", hexnat% "8000000000000800000000000", 378231999954944, 371514671104]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "38c1021fb842f000000", hexnat% "4400040000000000000", hexnat% "400002200000080000000000000", 525059751936, hexnat% "8200000000000000080000000", hexnat% "320000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8200006f00081fbfeef000000", hexnat% "1081020000000000000", hexnat% "60040000000000000", hexnat% "400002200000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100001fb7eef000000", hexnat% "e0020000000000000", hexnat% "4000022000010c0000000000000", hexnat% "200000200000000000000000", hexnat% "1c00000008000000000", hexnat% "8000004000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fe00e0188ae0000000", hexnat% "4000000802000000000", hexnat% "40000220000100000000f000000", hexnat% "8200000000000030000000000", 360777252864, 387028092977152]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3420001fbfe4f000000", hexnat% "81020000020000000", hexnat% "4800040000000000000", hexnat% "400002200000080000000000000", hexnat% "8200000000000000080000000", hexnat% "340000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7de00e03bfeef000000", 492581209243648, hexnat% "400002200001000000000000000", hexnat% "200000200000000000000000", hexnat% "8000000000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ca102018feef000000", hexnat% "340040000000000000", 390326627860480, hexnat% "8000004000000800000000000", hexnat% "400002200000080000000000000", hexnat% "200000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4082020062200009baae0000000", hexnat% "1c00020000000000000", 387028344635392, hexnat% "1c0000000000000000", 360777252864, hexnat% "2000010c0000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000003fe00e0188ee0000000", hexnat% "4000000802000000000", hexnat% "200000000000030000000000", 343849041920, hexnat% "400002200001000000000000000", 387028092977152]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000002060001fbdeef000000", hexnat% "1081020000000000000", hexnat% "4c00040000000000000", hexnat% "400002200000080000000000000", hexnat% "200000200000002000000000", hexnat% "100000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4082020062600019baae0000000", hexnat% "180020000000000000", 361028911104, hexnat% "1c00000000000000000", 105553116266496, hexnat% "2000010c0000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82000030e1021180a01000000", hexnat% "4200000802000000000", hexnat% "100000200000000000", hexnat% "c00000038000000000", 364535349248, 70368979058688, hexnat% "4000022000000c0000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002
def vertexColumn : Fields := ⟨10, hexnat% "dc4f0bc1f25a368ba1ea96958d68d8b61d98e538ce4b8ae1b89e1783e964d94e4b91e695356354d4b51d58d534cd4b4ad1b51d2745d0f69394cd38ccb31cd8b92d4b32cab1ae1b26c5b0ef07a1d8751cc789ca719e1725c570dd0f23c4f0bc1f9512a9192694529264590e64549615254550d64348d0b22c4b0ae0741c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6d36db6d36db4924924936d36d24d36da4924d24924924924924c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨85, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2008a2380887fff8000000", hexnat% "200000000200380000000000", 6473924464345088, hexnat% "7400000000000000000", hexnat% "70000000000000000000", hexnat% "80000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204202380a07fff8000000", hexnat% "200000000200380000000000", 6051711999279104, hexnat% "88200000000000000000", hexnat% "5c00000000000000000", hexnat% "30000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000c7e03a02384f80000000", hexnat% "2000020000000078000000", hexnat% "38000000000000000000", 3378249476341760, 7902739824640, 4925812092436480]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "203242381fb85878000000", hexnat% "c8000000000000000000", hexnat% "200000000200000780000000", hexnat% "1800000002000000000", 8246337208320, hexnat% "4200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2012c2380107fff8000000", hexnat% "200000000200380000000000", hexnat% "5200000000000000000", hexnat% "28000000800000000000", 8444249301319680, hexnat% "c0000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20008fe03a01b85f80000000", hexnat% "70000000000000000000", hexnat% "2000020000000078000000", 3378249476341760, 7834020347904, 5066549580791808]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202a22381fb85878000000", hexnat% "d0000000000000000000", hexnat% "200000000200000780000000", hexnat% "1800000002000000000", 8246337208320, hexnat% "4400000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220001fbffff8000000", hexnat% "2000023800000000000000", hexnat% "200000000200000000000000", hexnat% "5c00000000000000000", hexnat% "d8000000000000000000", hexnat% "20000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200007e03a01badf80000000", hexnat% "2000020000000078000000", 5634997092352, hexnat% "78000000000000000000", hexnat% "80000008000000000000", 6192449487634432]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17e0380187fff8000000", hexnat% "2000020000000000000000", hexnat% "200000000200380000000000", 8444249301319680, hexnat% "68000000000000000000", hexnat% "80000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fe20381fb8f810000000", hexnat% "1c00000000080000000", hexnat% "2000020000000068000000", hexnat% "200000000200000700000000", 7696581394432]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204622381fb9f878000000", 6629282021376, hexnat% "20800000000000000000", hexnat% "98000000000000000000", hexnat% "200000000200000000000000", hexnat% "1400000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204622381187fff8000000", hexnat% "200000000200380000000000", 3940649673949184, hexnat% "1c00000000000000000", hexnat% "38000000000000000000", hexnat% "80000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffe03811bcf880000000", 3940649942384640, hexnat% "2000020000000068000000", hexnat% "200000000200000700000000", 3298534883328]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fe038118cff80000000", hexnat% "80000208100000000000", hexnat% "200000000000200000000000", 3300548149248, hexnat% "2000020000000000000000", 1688849860263936]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77a2081fbcf878000000", hexnat% "88001000000000000000", hexnat% "2000002000000000000000", 3330747138048, hexnat% "200000000200000000000000", hexnat% "400000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5720001f97fff8000000", hexnat% "c00800000000000000", hexnat% "2000023000000000000000", hexnat% "200000000200280000000000", hexnat% "28000000000000000000", hexnat% "80000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000d720021dbeff80000000", 1101524893696, hexnat% "c00800000000000000", 562949953421312, hexnat% "28000000000000000000", hexnat% "2000023000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000d720021d96f900000000", hexnat% "20820800000008000000", 1127428915200, 562951832469504, hexnat% "403000000000000000", hexnat% "8000000280000000000", hexnat% "2000000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c25 c10
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c26 c9
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c27 c8
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c28 c7
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c29 c6
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c31 c4
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003
def vertexColumn : Fields := ⟨10, hexnat% "dc2f07c368ba1ea96958d68d9362d87663a4e538ce4b8ae1b89e1783e364b91e695356354d4b51d58d9354d334ad1b49d1743da4cd38cd332cc7362e4b52ccb2ac6b26c5b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f9512c9492a945299152585495154354348d1342d90d2384c9314c3342c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4db6db6d36db6da4924924924924924924924db4db4da6926924c9249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨85, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802000000000089778000000", hexnat% "200040000000000000", hexnat% "2000400000000000000", 53902458040090624, 4251398048237748224, hexnat% "5fc000000000000000", hexnat% "1d800000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007
def vertexColumn : Fields := ⟨10, hexnat% "2729ab1aa699a8e93a2e996558d64d8b61d98e9392e2b86e9c669c6699666394e4b965555355352d4756364d4b4ad1b663c4e9364d5334e334ccb3c2e8b62e4b8ad2b2ac6b86d1b26c3b61e4751cc749ca745c9715c3783c4f948721990e2382e944711950d2342d90c6384d1324c530ce0b42c8b0ad0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6db6d26924db6db6db693492492492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "210006f07ff14cf0000000", hexnat% "4000080000180000000000000", hexnat% "1600000000000000000000", 768799145984, 1008821709693779968]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4002180043ff0f1bfd0000000", 290546484510720, hexnat% "2c000000000000000", hexnat% "1600000000000000000000", 3947246743715840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4002080041ffad4bfd0000000", 290546484510720, hexnat% "2e000000000000000", hexnat% "1700000000000000000000", 1164382813814784]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000080001ffeffaae0000000", hexnat% "2e000000010000000", hexnat% "1700000000000000000000", 90194313216, 281749854617600, hexnat% "2000040000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4002080041ff6b6bfd0000000", 290546484510720, hexnat% "2e000000000000000", hexnat% "1700000000000000000000", 2323268069490688]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000410001403c0000000", hexnat% "4000080000040800000000000", hexnat% "2e000000010000000", hexnat% "1700000000000000000000", 1082868629504, 4336473859948544, 1130406805004877824]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008
def vertexColumn : Fields := ⟨10, hexnat% "9d2726693a2e87a99b16a599695a364d8b61d98e9392e2b86e9c599564d94e4b91e665c569565655554d58d5352d4756364d534cd4b4ad98f13a4d9394e334ccb31cd8b92d2b2ac6b46c9b16c3bc1e8761e4789d2729c6785d1725c570de0f13c6c4388e0ba511c469914654348d1342d84d1324c3342c8b0ae0741c8709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db69a4936db49b69b6da49249a49249269249a492492493491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40c01fc2211ff0e000000", hexnat% "200400000000000000000", hexnat% "5800000000000000000000", 400222232510464, 133982092672368640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60c4141fe11110a000000", hexnat% "5800000000000004000000", 13546827679130451968, 400222232510464, 1025960312832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c010002000100000000", 18158513697658503168, hexnat% "5c00000000000000000000", hexnat% "400020001080000000", 405719790649344, 1023947046912, 133995283053805568]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011
def vertexColumn : Fields := ⟨10, hexnat% "2746713c2f07c6693a2ea66c5a9665a364d8b66394e3392e2b86e4789e0fa71666594e4b91e665c5695656558d5352d4756354d3352d2b46d4749d1743d98f13a4d938cd332cd8b92d4b32d2b2ae1b46c9b0ef07a1d8751cc789d2729e1745c970dd0f23c4f0bc1f1aa4619869464990e64519615454950d64318d0b22c4b0ae0741c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69b6db6db69b6d34924924926db6926936db692493492492492492493249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400401000760301fffe000000", 1387583674253312, hexnat% "ff00000000000000000", hexnat% "2e0000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42c0007607effffe000000", hexnat% "21100000000000000000", hexnat% "4000010800000000000000000", hexnat% "e600000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2c0002207ee31fc000000", hexnat% "20104400000002000000", hexnat% "4004000000000000000000000", 1984274890752, hexnat% "11800000000000000000", hexnat% "e601000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400401000760289fffe000000", 1519525069586432, hexnat% "ff00000000000000000", hexnat% "2e0000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000090d0020049fffe000000", 2146246697418752, hexnat% "4000007400000000000000", hexnat% "21000000000000000000", hexnat% "240000000060000000000", hexnat% "e200000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400021ff03604087de4000000", hexnat% "e0000000020000000000", 1090715534753792, 1658293583872, hexnat% "4000004000000000000000", 4398046511104]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2fff01207efbdec000000", hexnat% "4004000000000000000000000", 283769831424, 7205759403792793600]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2c3001207ee35ec000000", hexnat% "20104400000002000000", hexnat% "4000010800000000800000000", 1933003718656, hexnat% "c602000000000000000", hexnat% "4000000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000128002000c3c00000000", 2216615508705280, hexnat% "2e0000400020000000000", hexnat% "400000700000001a000000", hexnat% "1000000018100000000", 287225937920, hexnat% "c700000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012
def vertexColumn : Fields := ⟨10, hexnat% "2746713c2f2726693a2ea66c5a9665a568d9362d87663a4e538ce4b8ae1b91e2783e9c5994e4b999715a5595956354d4b51d58d9354d3352d2b51d2743d98f13a4d9394e334ccb31cd8b92d4b32d2b2ad1b26c3bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07c6c1a8699146585515254354348d1342d90c6384d1324c3342c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db6db6db4db6db4924924924924924924924924926da6db6924d3492649249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨40, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000000000107af000000", 2461217196357976064, hexnat% "88a00000000000000000", 6737807255011328, hexnat% "5fc000000000000000", 2143713422628356096, hexnat% "77000000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00159.record012
