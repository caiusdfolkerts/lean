module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00004Data
public import GraphInputsRow23Part00004Frames
public import GraphInputsRow23Part00004Leaves
public import GraphInputsRow23Part00004Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00004.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001
def vertexColumn : Fields := ⟨10, hexnat% "aa9562bb51aa719a6659566392e479c55352d4752b45d0f783d0ea3c4d53c2e4b52ccb8ac6b86c5b0ef07a1d8731d2719d1715c3723c4f0bd54a28aa518a6c4551a24a9864590e5452951515435c0e8350ca382c8b12c2b41c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a983d3fe00e0000000", hexnat% "100000c000700000000", 2164663517184, hexnat% "164000000000000000", 2017612633061982208, hexnat% "400020000000000000", 2305843009213693952]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "407c00b1ffe0000000", hexnat% "2800010000000000000", hexnat% "100000c0e0000000000", 27866022694354944, 9403516021949595648, hexnat% "200000400000000000", hexnat% "1d0000000000000000", hexnat% "20100000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fdd803e1900000000", hexnat% "2200010400080000000", hexnat% "100000c000600000000", hexnat% "800200000060000000", hexnat% "402000000000000000", 9992361673228288, 18016322654830592, 137438953472]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2e75794640ae0000000", hexnat% "88800000000000000", hexnat% "102008000000000000", hexnat% "10000000a0500000000", 1002754604531712, 2130303778816, 27021597764222976]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2804110e1ffe0000000", 27866022694354944, 2053641430080946176, hexnat% "100000c0e0000000000", hexnat% "208200000000000000", 17592186044416, hexnat% "522000000000000000", hexnat% "d0000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "27fc1b16e2880000000", hexnat% "100000c000700000000", 2017612633061982208, hexnat% "800200000060000000", 721279627821056, 18016322654830592, 2305843009213693952, 68719476736]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a5cb917279e0000000", 18578997730344960, 1441151906528362496, hexnat% "180000080000000000", hexnat% "100000c040000000000", 9147936743096320, hexnat% "422000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2bfc3902e28e0000000", 2017612637356949504, hexnat% "100000c000600000000", 1073123348709376, hexnat% "402000000000000000", 18016322654830592, 9007267974217728]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28541102028a0000000", hexnat% "88800000000000000", hexnat% "522000000000000000", hexnat% "100000c0e0700000000", 18016322654830592, 1477180677777522688, hexnat% "200200000000000000", 9007269047959552, 1073123348709376]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00004.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00004.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019
def vertexColumn : Fields := ⟨10, hexnat% "15a2e87ae1b46a99562d876538ae1783e564b91e785d16a5554b51d54d2b45d0f783d0ea354cb31cf0ba2d8b32d2b1ad1b26d8791cc789d2719e1745c9743c8f13c2f07d4a2a85a0eb06a1946298560d9492a4590e705a1545294550d703a0d4328c530cd0b22c4b0ac1b81d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8004010104000000000000", hexnat% "2001004001850000000000", hexnat% "40020080024a0000000000", hexnat% "20810401008004000000000", hexnat% "41020802010008000000000", hexnat% "10408200820202000000000", 486388759756013568, hexnat% "3c01e0000000000000000", 17592186044416]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00004.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00004.record019
