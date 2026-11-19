module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00015Data
public import GraphInputsRow23Part00015Frames
public import GraphInputsRow23Part00015Leaves
public import GraphInputsRow23Part00015Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00015.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031
def vertexColumn : Fields := ⟨10, hexnat% "2b25a95aa9a96358b65392e2b86e2783eac569566a5a54d52d54d4b4ad1b49d0f72368d6394d5334e332ce2b2ac6b86d1b26c3ba1d4731e2749c6785c3743c8f172a2a494a4a85a298961584e0b81ea869152529164a5254551342d0768350e2348ca384c9314d0b12c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492492249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43fe4bfc7cc770000000000", hexnat% "18400000000000000000", hexnat% "1000800880000000000", hexnat% "c002000002000000000000", hexnat% "30000000010000000000000", 3459045988797251584, 9007199254740992]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43fe39606040f0000000000", hexnat% "10008001050000000000000", 2893562760585543680, hexnat% "10680000000000000000", hexnat% "20000004000100000000000", hexnat% "18180600000000000", hexnat% "c004000002000000000000", 422212465065984]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10048001050000000000000", hexnat% "20010008008c0000000000", hexnat% "c00600001220000000000", 2750573472416530432, hexnat% "20110084000100000000000", hexnat% "41020820000000000000000", hexnat% "18180400000000000", hexnat% "c006000002000000000000", hexnat% "280140000010000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c3 c2
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00015.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00015.record059
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059
def vertexColumn : Fields := ⟨10, hexnat% "172a696655936a394e3392e2b86e5c699595554d68d534cd4b4ad1b563c4d9394cd38ccb31ce4b52ccb8ad2b2ac6b86c9b16c3ba1d8731ca719d1725c570de0f43e9254932a29464988e1382ea45514c689515252344d0b68350d2384d1324c530ce0b22c4b0ad0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9c13933fc8b5800000000", hexnat% "40080000000a000000000", hexnat% "20040400040000000000", hexnat% "2004000003400000000000", hexnat% "200400000200000000000", hexnat% "1002000000100000000000", 14411518807585587200, hexnat% "4018020000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "560ad0ffc473800000000", hexnat% "80100000000c000000000", hexnat% "80101000080000000000", hexnat% "2004000003800000000000", hexnat% "200400000200000000000", hexnat% "1002000000100000000000", 16140901064495857664, hexnat% "4018020000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2004000093200000000000", hexnat% "200400048001000000000", hexnat% "3e0000000800000000", hexnat% "c01810000016000000000", hexnat% "1f0000000000000000000", 82401799432044544, hexnat% "500a000200020000000000", 31336081391616, 18158513697557839872]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00015.record059_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00015.record059
